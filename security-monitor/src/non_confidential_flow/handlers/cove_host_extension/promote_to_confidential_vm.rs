// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::sbi::NaclSharedMemory;
use crate::core::architecture::{GeneralPurposeRegister, Hgatp, PageSize};
use crate::core::control_data::{
    ConfidentialHart, ConfidentialVm, ConfidentialVmId, ConfidentialVmMemoryLayout, ControlDataStorage, HypervisorHart, StaticMeasurements,
};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::core::memory_protector::ConfidentialVmMemoryProtector;
use crate::core::page_allocator::{Allocated, Page, PageAllocator};
use crate::error::Error;
use crate::non_confidential_flow::handlers::supervisor_binary_interface::SbiResponse;
use crate::non_confidential_flow::{ApplyToHypervisorHart, NonConfidentialFlow};
use alloc::vec::Vec;
use flattened_device_tree::FlattenedDeviceTree;
use riscv_cove_tap::{AttestationPayload, AttestationPayloadParser, Secret};

/// Creates a confidential VM in a single-step. This handler implements the Promote to TVM call defined by the COVH ABI in the CoVE
/// specification. With this call, the hypervisor presents a state of a virtual machine, requesting the security monitor to promote it to a
/// confidential VM. The security monitor copies the VM state (data, page tables, boot hart state) into the confidential memory and measures
/// it.
///
/// # Safety
///
/// * The virtual machine initial state must consist of only one hart (boot hart) running. All other hart must be still in reset state.
/// * The address of the flattened device tree must be aligned to 8 bytes.
/// * The address of the authentication blob must be either `0` or aligned to 8 bytes.
pub struct PromoteToConfidentialVm {
    fdt_address: ConfidentialVmPhysicalAddress,
    attestation_payload_address: Option<ConfidentialVmPhysicalAddress>,
    program_counter: usize,
    hgatp: Hgatp,
}

impl PromoteToConfidentialVm {
    const FDT_ALIGNMENT_IN_BYTES: usize = 8;
    const TAP_ALIGNMENT_IN_BYTES: usize = 4;
    const BOOT_HART_ID: usize = 0;

    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        let fdt_address = ConfidentialVmPhysicalAddress::new(hypervisor_hart.gprs().read(GeneralPurposeRegister::a0));
        let attestation_payload_address = match hypervisor_hart.gprs().read(GeneralPurposeRegister::a1) {
            0 => None,
            address => Some(ConfidentialVmPhysicalAddress::new(address)),
        };
        let program_counter = hypervisor_hart.gprs().read(GeneralPurposeRegister::a2);
        let hgatp = Hgatp::from(hypervisor_hart.csrs().hgatp.read());
        Self { fdt_address, attestation_payload_address, program_counter, hgatp }
    }

    pub fn handle(self, non_confidential_flow: NonConfidentialFlow) -> ! {
        let transformation = match self.create_confidential_vm(non_confidential_flow.shared_memory()) {
            Ok(confidential_vm_id) => {
                debug!("Created new confidential VM[id={:?}]", confidential_vm_id);
                SbiResponse::success_with_code(confidential_vm_id.usize())
            }
            Err(error) => {
                debug!("Promotion to confidential VM failed: {:?}", error);
                SbiResponse::error(error)
            }
        };
        non_confidential_flow.apply_and_exit_to_hypervisor(ApplyToHypervisorHart::SbiResponse(transformation))
    }

    fn create_confidential_vm(&self, shared_memory: &NaclSharedMemory) -> Result<ConfidentialVmId, Error> {
        debug!("Promoting a VM to a confidential VM");
        // Copying the entire VM's state to the confidential memory, recreating the MMU configuration
        let mut memory_protector = ConfidentialVmMemoryProtector::from_vm_state(&self.hgatp)?;

        // The pointer to the flattened device tree (FDT) as well as the entire FDT must be treated as an untrusted input, which measurement
        // is reflected during attestation. We can parse FDT only after moving VM's data (and the FDT) to the confidential memory.
        let (vm_memory_layout, number_of_confidential_harts) = self.process_device_tree(&memory_protector)?;

        // TODO: generate htimedelta
        let htimedelta = 0;

        debug!("number_of_confidential_harts = {}", number_of_confidential_harts);
        // We create a fixed number of harts (all but the boot hart are in the reset state).
        let confidential_harts: Vec<_> = (0..number_of_confidential_harts)
            .map(|confidential_hart_id| match confidential_hart_id {
                Self::BOOT_HART_ID => {
                    ConfidentialHart::from_vm_hart(confidential_hart_id, self.program_counter, self.fdt_address, htimedelta, shared_memory)
                }
                _ => ConfidentialHart::from_vm_hart_reset(confidential_hart_id, htimedelta, shared_memory),
            })
            .collect();

        let attestation_payload =
            self.read_attestation_payload(&memory_protector).inspect_err(|e| debug!("TAP reading failed: {:?}", e)).unwrap_or(None);
        let measurements = self.measure(&mut memory_protector, &vm_memory_layout, &confidential_harts)?;

        let secrets = self
            .authenticate_and_authorize_vm(attestation_payload, &measurements)
            .inspect_err(|e| debug!("Local attestation failed: {:?}", e))
            .unwrap_or(alloc::vec![]);

        ControlDataStorage::try_write(|control_data| {
            // We have a write lock on the entire control data! Spend here as little time as possible because we are
            // blocking all other harts from accessing the control data. This influences all confidential VMs in the system!
            let id = control_data.unique_id()?;
            control_data.insert_confidential_vm(ConfidentialVm::new(id, confidential_harts, measurements, secrets, memory_protector))
        })
    }

    fn measure(
        &self, memory_protector: &mut ConfidentialVmMemoryProtector, vm_memory_layout: &ConfidentialVmMemoryLayout,
        confidential_harts: &Vec<ConfidentialHart>,
    ) -> Result<StaticMeasurements, Error> {
        let mut measurements = StaticMeasurements::default();
        memory_protector.finalize(&mut measurements, vm_memory_layout)?;
        confidential_harts[Self::BOOT_HART_ID].measure(measurements.pcr_boot_hart_mut());
        debug!("VM measurements: {:?}", measurements);
        Ok(measurements)
    }

    fn process_device_tree(&self, memory_protector: &ConfidentialVmMemoryProtector) -> Result<(ConfidentialVmMemoryLayout, usize), Error> {
        debug!("Reading flatten device tree (FDT) at memory address {:?}", self.fdt_address);
        let address_in_confidential_memory = memory_protector.translate_address(&self.fdt_address)?;
        // Make sure that the address is 8-bytes aligned. Once we ensure this, we can safely read 8 bytes because they must be within
        // the page boundary. These 8 bytes should contain the `magic` (first 4 bytes) and `size` (next 4 bytes).
        ensure!(address_in_confidential_memory.is_aligned_to(Self::FDT_ALIGNMENT_IN_BYTES), Error::FdtNotAlignedTo64Bits())?;
        // Below use of unsafe is ok because (1) the security monitor owns the memory region containing the data of the not-yet-created
        // confidential VM's and (2) there is only one physical hart executing this code.
        let fdt_total_size = unsafe { FlattenedDeviceTree::total_size(address_in_confidential_memory.to_ptr())? };
        ensure!(fdt_total_size >= FlattenedDeviceTree::FDT_HEADER_SIZE, Error::FdtInvalidSize())?;

        // To work with FDT, we must have it as a continous chunk of memory. We accept only FDTs that fit within 2 MiB
        ensure!(fdt_total_size.div_ceil(PageSize::Size2MiB.in_bytes()) == 1, Error::FdtInvalidSize())?;
        let large_page = Self::relocate(memory_protector, &self.fdt_address, fdt_total_size, false)?;

        // Security note: We parse untrusted FDT using an external library. A vulnerability in this library might blow up our security
        // guarantees! Below unsafe is ok because the FDT address aligned to (at least) the size of the FDT header and all FDT is in a
        // continuous chunk of memory. See the safety requirements of `FlattenedDeviceTree::from_raw_pointer`.
        let device_tree = unsafe { FlattenedDeviceTree::from_raw_pointer(large_page.address().to_ptr()) }?;

        let number_of_confidential_harts = device_tree.harts().count();
        let kernel = device_tree.memory().and_then(|r| r.into_range())?;
        let initrd = device_tree.initrd().ok();

        let vm_memory_layout =
            ConfidentialVmMemoryLayout::new(kernel, (self.fdt_address.usize(), self.fdt_address.usize() + fdt_total_size), initrd);
        debug!("Virtual machine's memory layout: {:?}", vm_memory_layout);

        // Clean up, deallocate pages
        PageAllocator::release_pages(alloc::vec![large_page.deallocate()]);

        ensure!(number_of_confidential_harts > 0, Error::InvalidNumberOfHartsInFdt())?;
        ensure!(number_of_confidential_harts < ConfidentialVm::MAX_NUMBER_OF_HARTS_PER_VM, Error::InvalidNumberOfHartsInFdt())?;

        Ok((vm_memory_layout, number_of_confidential_harts))
    }

    fn read_attestation_payload(&self, memory_protector: &ConfidentialVmMemoryProtector) -> Result<Option<AttestationPayload>, Error> {
        match self.attestation_payload_address {
            Some(attestation_payload_address) => {
                debug!("Reading TEE attestation payload (TAP) at memory address {:?}", attestation_payload_address);
                let address_in_confidential_memory = memory_protector.translate_address(&attestation_payload_address)?;
                // Make sure that the address is 8-bytes aligned. Once we ensure this, we can safely read 8 bytes because they must be
                // within the page boundary. These 8 bytes should contain the `magic` (first 4 bytes) and `size` (next 2
                // bytes).
                ensure!(address_in_confidential_memory.is_aligned_to(Self::TAP_ALIGNMENT_IN_BYTES), Error::AuthBlobNotAlignedTo32Bits())?;
                // Below use of unsafe is ok because (1) the security monitor owns the memory region containing the data of the
                // not-yet-created confidential VM's and (2) there is only one physical hart executing this code.
                let header: u64 =
                    unsafe { address_in_confidential_memory.read_volatile().try_into().map_err(|_| Error::AuthBlobNotAlignedTo32Bits())? };
                let total_size = riscv_cove_tap::ACE_HEADER_SIZE + ((header >> 32) & 0xFFFF) as usize;
                // To work with the authentication blob, we must have it as a continous chunk of memory. We accept only authentication blobs
                // that fit within 2MiB
                ensure!(total_size.div_ceil(PageSize::Size2MiB.in_bytes()) == 1, Error::AuthBlobInvalidSize())?;
                let large_page = Self::relocate(memory_protector, &attestation_payload_address, total_size, true)?;
                // TODO: replace the hardcoded decapsulation key with a key or interface to device-specific decapsulation key
                let test_decapsulation_key = "673751CBB596541131C66398662CB4B0EB80796A88B28144A5BBC854F80D4B35BE0AB241E4795F8FBBA814F50FA80498CBE8BF68A0A583A4C5981B41DF0667DB614A628C3060697438E62C8D36026EE29C96B673BF1A194EE49481351F4D1748DD01CD023142F01057142B741CBA8302E432F88C63D0B4B5767AC3A5A59AFA3A321E65B1D1511807A06E16A04B2F1070E465586D4A9B68E2B42D57A356FA7BB3D04E51B193FF4C757CFA0F15924EA6E49AFB83B2919C985869ADA544338F44AE96A874C425AF87BC73F3CB0FD2627B1539B1F19A77E36B7FC817851D39BD8A069A6C2202C17469D421A588E65DAF450030B6674EC1C734AA25414B119E61B26EFC90DF81059D2B9599414F93692BF45A4B1C5CC09EDB37B1B1433026AEA6B0200722B819C7BC061C53A4304992FCA2AEE2324A324AB91C3E5D562096B8A141756940F15A2800C274EA4F65817E639C5D2A278C6A294F9DB331F84CCB0A10309F530A06EB962573C86005C15BFC7531A143026396721297E25CB655A294964B2FE531905F2802376B8ACE35AE3E2814BAB7062BC1A840657DBFCB5F41BB55475697849A31E2222E995518CA7640AD4B9CEE9820984138BE0510FFD6AC225393A5F0CB030528CD2A0610E78A5CF1B073039A6D143068C53DBD15A1D4446DA7B310EE795D1FB31B2F97008F83BDF348A593A3BDCBB571907B36D0978162C253E6F50106C463149834ABFB0707D8AB4A4BABC323598A085B309764B7C32C9DB0C9F2D52EF2F00BACE7846868C33B82AFA430A4C2F67B698A60526A161CD62115DCA767C203E3E2CC787031A73B5B7DBA1EEE5AB04B77BB569B952D9A15D198779804197D23C18E5B055F5C8087D742F64418D6505E70418ABFC6B1BF7BB3DE286599F4676CF87946D65144998AFAE1C689449E3F349FD0809AFB856DDE4A94A2C0258D56432F40C3DA812D3FD3B72259A61D2882E0F50B355121E564C6BD33366F32BF4A5996B9998961354925A2BACDF48056118453AC3792A7879B71579ADB65F5D83B1ED6C8C49836DE379DAA027E62B96F683C1688935CB3FCCD64329267273E60C6CD59BA1B7FC911E2662527ECCB7A474E5EF00CA9F789A3838E889242E7FB2B08F3790613C4EED3C912EC4EB029B971096B384727697B4DDC3B698C9A6DA6971FA4C574ECD18EB1C84C0C5790153AA6B9DB61D8BAC0A680A37ED623582A7E8C0885EBB35AF341477764368E0647B14553672316D0B90317C5B53AA747E61B4750DB9E63CC3712900005CA24226B523E0A179582C85968C107857BB41521B7342B13DCAC462A53BE38446F2142519667B48B1C68FCAFA4D3C7E3E5AFF163C41F2C1B4DBAC5456C30776078E7C3A713819F6B9ACA55D77D60637183A723035730F94285C42AC3587637F66AC30F2C4039E60420967576E27B96C8C004D9585F33939AC44F0D195B35D472FC219076F12D0984AC844728D5D2266BB5CD8B325DDA497B4F397BFE722C9D7684201A921F502271985CB3F31C04884C090B063631253DC454537031F2C82C10A1722DE6C556464DC9D64389DA37E469480C921065C79A30C83C867C952B30548A6B5BDFEB6EA6247480F163B427B17CF94889220FE934564DAB90F5B6A11648870B654495A6691AE21FEA86BDC8C49093FA07E926AF3ABA0E7CEC21F613B49986C6C8A139EDA70B7ED8211A3215E8C43EF8C151AE61740EF83B48276033614B58E9CEB992233CD21DFF70C7A6F7171707A2ADD37ACBF136A4EB4A79517FD0C8AFF0B5126435C3100331F208A546C9A4044A8F0503C8ADE9506A018B4CA7C6E8D70120017D38B13B52786A85A540D81B8E71C376B796A7215ABF065086D3C80EE94B8F09E2A3BA13B82583B825388E87BA010AF507173563789A1DCD088907C52BD7FC1C6930605F060F37978211C10FB5717E3FA291D20B5D43FB74CD4711394B0027E41C52B523797470532CBE123C92950720E5E255256577D4E156EBD4C698D813405C61430B978694ACDE78031E74BA1D8517DAE2346F008411231FCCE7BFF75BC361E691E776049004097B36490D876288701B2D3A1743AB8753D47AC6200E2DA7458D3A059681233872794E6720186B20108B1D1033971CE19ED67A2A28E499A360A4AD86AE4194034F202F8FA3626FE75F307A4CEA4148219B958EA0B7886659235A4D1980B192610847D86EF32739F94C3B446C4D81D89B8B422A9D079C88B11ACAF321B014294E18B296E52F3F744CF9634A4FB01DB0D99EF20A633A552E76A0585C6109F018768B763AF3678B4780089C1342B96907A29A1C11521C744C2797D0BF2B9CCDCA614672B45076773F458A31EF869BE1EB2EFEB50D0E37495DC5CA55E07528934F6293C4168027D0E53D07FACC6630CB08197E53FB193A171135DC8AD9979402A71B6926BCDCDC47B93401910A5FCC1A813B682B09BA7A72D2486D6C799516465C14729B26949B0B7CBC7C640F267FED80B162C51FD8E09227C101D505A8FAE8A2D7054E28A78BA8750DECF9057C83979F7ABB084945648006C5B28804F34E73B238111A65A1F500B1CC606A848F2859070BEBA7573179F36149CF5801BF89A1C38CC278415528D03BDB943F96280C8CC52042D9B91FAA9D6EA7BCBB7AB1897A3266966F78393426C76D8A49578B98B159EBB46EE0A883A270D8057CD0231C86906A91DBBADE6B2469581E2BCA2FEA8389F7C74BCD70961EA5B934FBCF9A6590BF86B8DB548854D9A3FB30110433BD7A1B659CA8568085639237B3BDC37B7FA716D482A25B54106B3A8F54D3AA99B5123DA96066904592F3A54EE23A7981AB608A2F4413CC658946C6D7780EA765644B3CC06C70034AB4EB351912E7715B56755D09021571BF340AB92598A24E811893195B96A1629F8041F58658431561FC0AB15292B913EC473F04479BC145CD4C563A286235646CD305A9BE1014E2C7B130C33EB77CC4A0D9786BD6BC2A954BF3005778F8917CE13789BBB962807858B67731572B6D3C9B4B5206FAC9A7C8961698D88324A915186899B29923F08442A3D386BD416BCC9A100164C930EC35EAFB6AB35851B6C8CE6377366A175F3D75298C518D44898933F53DEE617145093379C4659F68583B2B28122666BEC57838991FF16C368DD22C36E780C91A3582E25E19794C6BF2AB42458A8DD7705DE2C2AA20C054E84B3EF35032798626C248263253A71A11943571340A978CD0A602E47DEE540A8814BA06F31414797CDF6049582361BBABA387A83D89913FE4C0C112B95621A4BDA8123A14D1A842FB57B83A4FBAF33A8E552238A596AAE7A150D75DA648BC44644977BA1F87A4C68A8C4BD245B7D00721F7D64E822B085B901312EC37A8169802160CCE1160F010BE8CBCACE8E7B005D7839234A707868309D03784B4273B1C8A160133ED298184704625F29CFA086D13263EE5899123C596BA788E5C54A8E9BA829B8A9D904BC4BC0BBEA76BC53FF811214598472C9C202B73EFF035DC09703AF7BF1BABAAC73193CB46117A7C9492A43FC95789A924C5912787B2E2090EBBCFD3796221F06DEBF9CF70E056B8B9161D6347F47335F3E1776DA4BB87C15CC826146FF0249A413B45AA93A805196EA453114B524E310AEDAA46E3B99642368782566D049A726D6CCA910993AED621D0149EA588A9ABD909DBB69AA22829D9B83ADA2209A6C2659F2169D668B9314842C6E22A74958B4C25BBDCD293D99CB609D866749A485DFB56024883CF5465DBA0363206587F45597F89002FB8607232138E03B2A894525F265370054B48863614472B95D0A2303442E378B0DD1C75ACBAB971A9A8D1281C79613ACEC6933C377B3C578C2A61A1EC181B101297A37CC5197B2942F6A0E4704C0EC63540481B9F159DC255B59BB55DF496AE54217B7689BD51DBA0383A3D72D852FFCA76DF05B66EECCBD47BC53040817628C71E361D6AF889084916B408A466C96E7086C4A60A10FCF7537BB94AFBCC7D437590919C28650C4F2368259226A9BFDA3A3A0BA1B5087D9D76442FD786C6F81C68C0360D7194D7072C4533AEA86C2D1F8C0A27696066F6CFD11003F797270B32389713CFFA093D991B63844C385E72277F166F5A3934D6BB89A4788DE28321DEFC7457AB484BD30986DC1DAB3008CD7B22F69702FABB9A1045407DA4791C3590FF599D81D688CFA7CC12A68C50F51A1009411B44850F9015DC84A93B17C7A207552C661EA9838E31B95EAD546248E56BE7A5130505268771199880A141771A9E47ACFED590CB3AA7CB7C5F74911D8912C29D6233F4D53BC64139E2F55BE75507DD77868E384AEC581F3F411DB1A742972D3EBFD3315C84A5AD63A0E75C8BCA3E3041E05D9067AFF3B1244F763E7983D48BA34134BAB88D635D8CF8FF5D686058FA68B6C2FEEAA5FA4DE65757086C0125E937BCC0D02FAA8988AE7169DF07F6A771E6E7FE3AB65E965C63C3E40ED909";
                let decapsulation_key = (0..test_decapsulation_key.len())
                    .step_by(2)
                    .map(|i| test_decapsulation_key.get(i..i + 2).and_then(|sub| u8::from_str_radix(sub, 16).ok()).unwrap())
                    .collect();
                let mut parser = unsafe { AttestationPayloadParser::from_raw_pointer(large_page.address().to_ptr(), total_size)? };
                let attestation_payload = parser.parse_and_verify(&decapsulation_key)?;
                // Clean up, deallocate pages
                PageAllocator::release_pages(alloc::vec![large_page.deallocate()]);
                Ok(Some(attestation_payload))
            }
            None => Ok(None),
        }
    }

    /// Performs local attestation. It decides if the VM can be promote into a confidential VM and decrypts the attestation secret intended
    /// for this confidential VM.
    fn authenticate_and_authorize_vm(
        &self, attestation_payload: Option<AttestationPayload>, measurements: &StaticMeasurements,
    ) -> Result<Vec<Secret>, Error> {
        use crate::core::control_data::MeasurementDigest;
        match attestation_payload {
            Some(attestation_payload) => {
                ensure!(attestation_payload.digests.len() > 0, Error::LocalAttestationFailed())?;
                for digest in attestation_payload.digests.iter() {
                    debug!("Reference PCR{:?}={:?}=0x{}", digest.pcr_id, digest.algorithm, digest.value_in_hex());
                    ensure!(digest.algorithm == riscv_cove_tap::DigestAlgorithm::Sha512, Error::LocalAttestationNotSupportedDigest())?;
                    let pcr_value = MeasurementDigest::clone_from_slice(&digest.value);
                    ensure!(measurements.compare(digest.pcr_id() as usize, pcr_value)?, Error::LocalAttestationFailed())?;
                }
                debug!("Attestation succeeded, fetched {} secrets", attestation_payload.secrets.len());
                Ok(attestation_payload.secrets)
            }
            None => Ok(alloc::vec![]),
        }
    }

    /// Copies a buffer into a single large page.
    ///
    /// Why do we need this function? The input buffer is continuous across guest physical pages with G-stage address
    /// translation enabled but might not be continuous across the real physical pages. The output buffer is continous accross real
    /// physical pages. Returns error if (1) the buffer to copy is larger than 2 MiB page, or (2) the base address is not aligned to
    /// 8-bytes.
    ///
    /// Safety:
    ///   * The caller of this function is responsible for deallocating the page returned from this function.
    fn relocate(
        memory_protector: &ConfidentialVmMemoryProtector, base_address: &ConfidentialVmPhysicalAddress, number_of_bytes_to_copy: usize,
        clear: bool,
    ) -> Result<Page<Allocated>, Error> {
        ensure!((base_address.usize() as *const u8).is_aligned_to(core::mem::size_of::<usize>()), Error::AddressNotAligned())?;
        let mut large_page = PageAllocator::acquire_page(PageSize::Size2MiB)?.zeroize();
        // Let's copy a blob from confidential VM's pages into the newly allocated huge page. We will copy in chunks of 8-bytes (usize).
        let mut copied_bytes = 0;
        while copied_bytes < number_of_bytes_to_copy {
            let confidential_vm_physical_address = base_address.add(copied_bytes);
            let confidential_memory_address = memory_protector.translate_address(&confidential_vm_physical_address)?;
            let value: usize = unsafe { confidential_memory_address.read_volatile() };
            if clear {
                unsafe { confidential_memory_address.write_volatile(0) };
            }
            large_page.write(copied_bytes, value)?;
            copied_bytes += core::mem::size_of::<usize>();
        }
        Ok(large_page)
    }
}

// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::attestation::RetrieveSecretRequest;
use crate::confidential_flow::handlers::interrupts::{AllowExternalInterrupt, ExposeEnabledInterrupts, HandleInterrupt};
use crate::confidential_flow::handlers::mmio::{
    AddMmioRegion, MmioLoadRequest, MmioLoadResponse, MmioStoreRequest, MmioStoreResponse, RemoveMmioRegion,
};
use crate::confidential_flow::handlers::sbi::{InvalidCall, SbiResponse};
use crate::confidential_flow::handlers::sbi_base_extension::{
    SbiExtensionProbe, SbiGetImplId, SbiGetImplVersion, SbiGetMarchId, SbiGetMimpid, SbiGetMvendorid, SbiGetSpecVersion,
};
use crate::confidential_flow::handlers::shared_page::{SharePageComplete, SharePageRequest, UnsharePageRequest};
use crate::confidential_flow::handlers::shutdown::ShutdownRequest;
use crate::confidential_flow::handlers::symmetrical_multiprocessing::{
    Ipi, NoOperation, RemoteFenceI, RemoteSfenceVma, RemoteSfenceVmaAsid, SbiHsmHartStart, SbiHsmHartStatus, SbiHsmHartStop,
    SbiHsmHartSuspend,
};
use crate::confidential_flow::handlers::virtual_instructions::VirtualInstruction;
use crate::confidential_flow::{ApplyToConfidentialHart, DeclassifyToConfidentialVm};
use crate::core::architecture::riscv::sbi::BaseExtension::*;
use crate::core::architecture::riscv::sbi::CovgExtension::*;
use crate::core::architecture::riscv::sbi::HsmExtension::*;
use crate::core::architecture::riscv::sbi::IpiExtension::*;
use crate::core::architecture::riscv::sbi::RfenceExtension::*;
use crate::core::architecture::riscv::sbi::SbiExtension::*;
use crate::core::architecture::riscv::sbi::SrstExtension::*;
use crate::core::architecture::specification::CSR_MSTATUS_MPV;
use crate::core::architecture::TrapCause::*;
use crate::core::architecture::{is_bit_enabled, HartLifecycleState, TrapCause, CSR};
use crate::core::control_data::{
    ConfidentialHart, ConfidentialHartRemoteCommand, ConfidentialVm, ConfidentialVmId, ControlDataStorage, HardwareHart, HypervisorHart,
    ResumableOperation,
};
use crate::core::interrupt_controller::InterruptController;
use crate::error::Error;
use crate::non_confidential_flow::{DeclassifyToHypervisor, NonConfidentialFlow};

extern "C" {
    fn exit_to_confidential_hart_asm() -> !;
}

/// Ensures control flow integrity within the `confidential flow` part of the finite state machine (FSM) of the security
/// monitor.
///
/// The ConfidentialFlow has an ownership of HypervisorHart and ConfidentialHart assigned to this physical hart. It
/// encapsulates both HypervisorHart and ConfidentialHart, so the only way to access their confidential state is through
/// ConfidentialFlow's public functions.
///
/// # Guarantees
///
/// * A confidential hart (not a dummy one!) is assigned to the hardware hart.
/// * The confidential VM that logically owns the confidential hart exists in the control data.
pub struct ConfidentialFlow<'a> {
    hardware_hart: &'a mut HardwareHart,
}

impl<'a> ConfidentialFlow<'a> {
    const DUMMY_HART_ERROR_MSG: &'static str = "Bug: Found dummy hart instead of a confidential hart";

    /// Routes the control flow to a handler that will process the confidential hart interrupt or exception. This is an entry point to
    /// the security monitor from the assembly context switch.
    ///
    /// Creates the mutable reference to HardwareHart by casting a raw pointer obtained from the context switch (assembly), see safety
    /// requirements of the asembly context switch. This is a private function, not accessible to the Rust code from the outside of the
    /// ConfidentialFlow but accessible to the assembly code performing the context switch.
    #[no_mangle]
    unsafe extern "C" fn route_trap_from_confidential_hart(hardware_hart_pointer: *mut HardwareHart) -> ! {
        let flow = Self { hardware_hart: unsafe { &mut *hardware_hart_pointer } };
        assert!(!flow.hardware_hart.confidential_hart().is_dummy());

        if !is_bit_enabled(CSR.mstatus.read(), CSR_MSTATUS_MPV) {
            debug!(
                "TSM exception {} when executing confidential hart {}",
                flow.confidential_hart().confidential_hart_state().csrs().mcause.read(),
                flow.confidential_hart().confidential_hart_id(),
            );
            ShutdownRequest::from_confidential_hart(flow.confidential_hart()).handle(flow)
        }

        match TrapCause::from_hart_architectural_state(flow.confidential_hart().confidential_hart_state()) {
            Interrupt => HandleInterrupt::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetSpecVersion)) => SbiGetSpecVersion::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetImplId)) => SbiGetImplId::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetImplVersion)) => SbiGetImplVersion::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(ProbeExtension)) => SbiExtensionProbe::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetMvendorId)) => SbiGetMvendorid::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetMarchid)) => SbiGetMarchId::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetMimpid)) => SbiGetMimpid::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Ipi(SendIpi)) => Ipi::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Rfence(RemoteFenceI)) => RemoteFenceI::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Rfence(RemoteSfenceVma)) => RemoteSfenceVma::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Rfence(RemoteSfenceVmaAsid)) => RemoteSfenceVmaAsid::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Rfence(RemoteHfenceGvmaVmid)) => NoOperation::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Rfence(RemoteHfenceGvma)) => NoOperation::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Rfence(RemoteHfenceVvmaAsid)) => NoOperation::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Rfence(RemoteHfenceVvma)) => NoOperation::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Hsm(HartStart)) => SbiHsmHartStart::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Hsm(HartStop)) => SbiHsmHartStop::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Hsm(HartSuspend)) => SbiHsmHartSuspend::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Hsm(HartGetStatus)) => SbiHsmHartStatus::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Srst(SystemReset)) => ShutdownRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Covg(AddMmioRegion)) => AddMmioRegion::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Covg(RemoveMmioRegion)) => RemoveMmioRegion::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Covg(AllowExternalInterrupt)) => AllowExternalInterrupt::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Covg(ShareMemory)) => SharePageRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Covg(UnshareMemory)) => UnsharePageRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Covg(RetrieveSecret)) => RetrieveSecretRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(_) => InvalidCall::from_confidential_hart(flow.confidential_hart()).handle(flow),
            GuestLoadPageFault => MmioLoadRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VirtualInstruction => VirtualInstruction::from_confidential_hart(flow.confidential_hart()).handle(flow),
            GuestStorePageFault => MmioStoreRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            trap_reason => {
                debug!("Not supported trap cause {:?}", trap_reason);
                ShutdownRequest::from_confidential_hart(flow.confidential_hart()).handle(flow)
            }
        }
    }

    /// Creates an instance of the confidential flow for the requested confidential hart. Returns error if it cannot steal the confidental
    /// hart, i.e., the confidential hart does not exist or it has been already assigned another physical hart.
    pub fn enter_from_non_confidential_flow(
        hardware_hart: &'a mut HardwareHart, confidential_vm_id: ConfidentialVmId, confidential_hart_id: usize,
    ) -> Result<(usize, Self), (&'a mut HardwareHart, Error)> {
        assert!(hardware_hart.confidential_hart().is_dummy());
        // Now, we are going to change the context between security domains.
        // 1) Store the hypervisor hart state that executed on this physical hart to the main memory.
        hardware_hart.hypervisor_hart_mut().save_in_main_memory();
        match ControlDataStorage::try_confidential_vm(confidential_vm_id, |confidential_vm| {
            confidential_vm.steal_confidential_hart(confidential_hart_id, hardware_hart)?;
            Ok(confidential_vm.allowed_external_interrupts())
        }) {
            Ok(allowed_external_interrupts) => {
                // 2) Load confidential hart state from main memory to the physical hart executing this code.
                hardware_hart.confidential_hart_mut().restore_from_main_memory();
                Ok((allowed_external_interrupts, Self { hardware_hart }))
            }
            Err(error) => Err((hardware_hart, error)),
        }
    }

    /// Moves in the finite state machine (FSM) from the confidential flow into non-confidential flow.
    pub fn into_non_confidential_flow(self) -> NonConfidentialFlow<'a> {
        // When moving back to the non-confidential flow, we always declassify enabled interrupts and timer configuration. This allows the
        // hypervisor to schedule the confidential VM timer and interrupts. Read the CoVE spec to learn more.
        let declassifier =
            DeclassifyToHypervisor::EnabledInterrupts(ExposeEnabledInterrupts::from_confidential_hart(self.confidential_hart()));

        // Now, we are going to change the context between security domains.
        // 1) Store the confidential hart state that executed on this physical hart to the main memory.
        self.hardware_hart.confidential_hart_mut().save_in_main_memory();
        let _ = ControlDataStorage::try_confidential_vm(self.confidential_vm_id(), |confidential_vm| {
            Ok(confidential_vm.return_confidential_hart(self.hardware_hart))
        })
        // Below unwrap is safe because we are in the confidential flow that guarantees that the confidential VM with
        // the given id exists in the control data.
        .unwrap();
        // Enable memory access control for the hypervisor
        unsafe { self.hardware_hart.hypervisor_hart().enable_hypervisor_memory_protector() };
        // 2) Load hypervisor hart state from main memory to the physical hart executing this code.
        self.hardware_hart.hypervisor_hart_mut().restore_from_main_memory();
        NonConfidentialFlow::create(self.hardware_hart).declassify_to_hypervisor_hart(declassifier)
    }

    /// Resumes execution of the confidential hart after the confidential hart was not running on any physical hart.
    /// This is an entry point to the confidential flow from the non-confidential flow.
    pub fn resume_confidential_hart_execution(mut self) -> ! {
        // During the time when this confidential hart was not running, other confidential harts could have sent it
        // `remote commands`. We must process them before resuming confidential hart's execution.
        self.process_confidential_hart_remote_commands();

        // It might have happened, that this confidential hart has been shutdown when processing an IPI. I.e., there was
        // an IPI from other confidential hart that requested this confidential hart to shutdown. If this had happened, we
        // cannot resume this confidential hart anymore. We must exit to the hypervisor and inform it about it.
        if self.confidential_hart().lifecycle_state() == &HartLifecycleState::PoweredOff {
            crate::confidential_flow::handlers::shutdown::shutdown_confidential_hart(self);
        }

        // One of the reasons why this confidential hart was not running is that it could have sent a request (e.g., a hypercall or MMIO
        // load) to the hypervisor. We must handle the response or resume confidential hart's execution.
        use crate::core::control_data::ResumableOperation::*;
        match self.confidential_hart_mut().take_resumable_operation() {
            Some(SbiRequest()) => SbiResponse::success().handle(self),
            Some(ResumeHart(v)) => v.handle(self),
            Some(MmioLoad(v)) => MmioLoadResponse::from_hypervisor_hart(self.hypervisor_hart(), v).handle(self),
            Some(MmioStore(v)) => MmioStoreResponse::from_hypervisor_hart(self.hypervisor_hart(), v).handle(self),
            Some(SharePage(v)) => SharePageComplete::from_hypervisor_hart(self.hypervisor_hart(), v).handle(self),
            None => self.exit_to_confidential_hart(),
        }
    }

    pub fn declassify_to_confidential_hart(mut self, declassifier: DeclassifyToConfidentialVm) -> Self {
        match declassifier {
            DeclassifyToConfidentialVm::SbiResponse(v) => v.declassify_to_confidential_hart(self.confidential_hart_mut()),
            DeclassifyToConfidentialVm::MmioLoadResponse(v) => v.declassify_to_confidential_hart(self.confidential_hart_mut()),
            DeclassifyToConfidentialVm::MmioStoreResponse(v) => v.declassify_to_confidential_hart(self.confidential_hart_mut()),
            DeclassifyToConfidentialVm::Resume(v) => v.declassify_to_confidential_hart(self.confidential_hart_mut()),
        }
        self
    }

    pub fn declassify_and_exit_to_confidential_hart(self, declassifier: DeclassifyToConfidentialVm) -> ! {
        self.declassify_to_confidential_hart(declassifier).exit_to_confidential_hart()
    }

    /// Applies transformation to the confidential hart and passes control to the context switch (assembly) that will
    /// execute the confidential hart on the hardware hart.
    pub fn apply_and_exit_to_confidential_hart(mut self, transformation: ApplyToConfidentialHart) -> ! {
        match transformation {
            ApplyToConfidentialHart::MmioAccessFault(v) => v.apply_to_confidential_hart(self.confidential_hart_mut()),
            ApplyToConfidentialHart::SbiResponse(v) => v.apply_to_confidential_hart(self.confidential_hart_mut()),
            ApplyToConfidentialHart::VirtualInstruction(v) => v.apply_to_confidential_hart(self.confidential_hart_mut()),
        }
        self.exit_to_confidential_hart()
    }

    fn exit_to_confidential_hart(mut self) -> ! {
        // We must restore the control and status registers (CSRs) that might have changed during execution of the security monitor.
        // We call it here because it is just before exiting to the assembly context switch, so we are sure that these CSRs have their
        // final values.
        let interrupts = self.confidential_hart().csrs().hvip.read_from_main_memory() | self.confidential_hart().csrs().pending_vssip_irqs;
        let address = self.confidential_hart_mut().address();
        self.confidential_hart().csrs().hvip.write(interrupts);
        self.confidential_hart().csrs().sscratch.write(address);
        unsafe { exit_to_confidential_hart_asm() }
    }
}

// ConfidentialFlow implementation that supports inter hart requests, including IPIs
impl<'a> ConfidentialFlow<'a> {
    /// Broadcasts the inter hart request to confidential harts of the currently executing confidential VM. Returns error if sending an IPI
    /// to other confidential hart failed or if there is too many pending IPI queued.
    pub fn broadcast_remote_command(
        &mut self, confidential_vm: &ConfidentialVm, confidential_hart_remote_command: ConfidentialHartRemoteCommand,
    ) -> Result<(), Error> {
        let sender_confidential_hart_id = self.hardware_hart.confidential_hart().confidential_hart_id();
        // check if the remote command is also dedicated for the currently executing confidential hart
        if confidential_hart_remote_command.is_hart_selected(sender_confidential_hart_id) {
            self.hardware_hart.confidential_hart_mut().execute(&confidential_hart_remote_command);
        }
        // For the time-being, we rely on the OpenSBI's implementation of broadcasting IPIs to hardware harts.
        let hart_mask = confidential_vm.broadcast_remote_command(sender_confidential_hart_id, confidential_hart_remote_command)?;
        if hart_mask != 0 {
            // Confidential harts that should receive an ConfidentialHartRemoteCommand are currently running on a hardware
            // harts. We interrupt such hardware harts with IPIs. Consequently, hardware harts running target confidential
            // harts will trap into the security monitor, which will execute ConfidentialHartRemoteCommands on the target harts.
            self.hardware_hart.opensbi_context(|| {
                InterruptController::try_read(|controller| controller.send_ipis(hart_mask, 0))?;
                Ok(())
            })?;
        }

        Ok(())
    }

    /// Processes pending requests from other confidential harts by applying the corresponding state transformation to
    /// this confidential hart.
    ///
    /// This function must only be called when the hypervisor requested resume of confidential hart's execution or when
    /// a hardware hart executing a confidential hart is interrupted with the inter-processor-interrupt (IPI).
    pub fn process_confidential_hart_remote_commands(&mut self) -> bool {
        let mut requests_processed = false;
        ControlDataStorage::try_confidential_vm(self.confidential_vm_id(), |confidential_vm| {
            confidential_vm.try_confidential_hart_remote_commands(
                self.confidential_hart_id(),
                |ref mut confidential_hart_remote_commands| {
                    confidential_hart_remote_commands.drain(..).for_each(|confidential_hart_remote_command| {
                        // The confidential flow has an ownership of the confidential hart because the confidential hart
                        // is assigned to the hardware hart.
                        self.confidential_hart_mut().execute(&confidential_hart_remote_command);
                        requests_processed = true;
                    });
                    Ok(())
                },
            )
        })
        // below unwrap never panics because 1) the confidential_vm_id and confidential_hart_id are valid since we are in the
        // confidential flow of the finite state machine (FSM) that guarantees it and 2) the processing of inter hart
        // requests always succeeds.
        .unwrap();
        requests_processed
    }
}

// ConfidentialFlow implementation that supports optional hart lifecycle transitions.
impl<'a> ConfidentialFlow<'a> {
    /// Delegates the state transition to the confidential hart. The confidential hart is intentionally encapsulated to prevent access to it
    /// other than via the ControlFlow.
    pub fn suspend_confidential_hart(&mut self) -> Result<(), Error> {
        self.confidential_hart_mut().transition_from_started_to_suspended()
    }

    /// Delegates the state transition to the confidential hart. The confidential hart is intentionally encapsulated to prevent access to it
    /// other than via the ControlFlow.
    pub fn stop_confidential_hart(&mut self) -> Result<(), Error> {
        self.confidential_hart_mut().transition_from_started_to_stopped()
    }

    /// Delegates the state transition to the confidential hart. The confidential hart is intentionally encapsulated to prevent access to it
    /// other than via the ControlFlow.
    pub fn resume_confidential_hart(&mut self, start_address: usize, opaque: usize) -> Result<(), Error> {
        self.confidential_hart_mut().transition_from_suspended_to_started(start_address, opaque)
    }

    /// Delegates the state transition to the confidential hart. The confidential hart is intentionally encapsulated to prevent access to it
    /// other than via the ControlFlow.
    pub fn shutdown_confidential_hart(&mut self) {
        self.confidential_hart_mut().transition_to_shutdown();
    }
}

impl<'a> ConfidentialFlow<'a> {
    pub fn set_resumable_operation(mut self, request: ResumableOperation) -> Self {
        self.confidential_hart_mut().set_resumable_operation(request);
        self
    }

    pub fn confidential_vm_id(&self) -> ConfidentialVmId {
        self.confidential_hart().confidential_vm_id().expect(Self::DUMMY_HART_ERROR_MSG)
    }

    fn confidential_hart_id(&self) -> usize {
        self.confidential_hart().confidential_hart_id()
    }

    fn confidential_hart_mut(&mut self) -> &mut ConfidentialHart {
        self.hardware_hart.confidential_hart_mut()
    }

    fn confidential_hart(&self) -> &ConfidentialHart {
        self.hardware_hart.confidential_hart()
    }

    fn hypervisor_hart(&self) -> &HypervisorHart {
        &self.hardware_hart.hypervisor_hart()
    }
}

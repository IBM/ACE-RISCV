# Verification of the Security Monitor

This directory contains work-in-progress on verifying the security monitor.
Currently, the verification is in early stages.

We use the tool [RefinedRust](https://plv.mpi-sws.org/refinedrust/) in the [Coq proof assistant](https://coq.inria.fr/) for verification.

## Architecture
Our approach to proving code in the security monitor is to add verification annotations to the Rust source code.
These include invariants as well as pre- and postconditions.

Afterwards, RefinedRust translates the Rust source code and annotations into a representation in the Coq proof assistant.
This is initiated by running `make verify` in the root directory of the repository.

The generated Coq code is placed in the [`verification/rust_proofs/ace`](/verification/rust_proofs/ace) folder.
There are two subfolders, [`generated`](/verification/rust_proofs/ace/generated) and [`proofs`](/verification/rust_proofs/ace/proofs).
The [`generated`](/verification/rust_proofs/ace/generated) subfolder contains the automatically generated model of the Rust code, the translated specifications, and proof templates.
It is re-generated on every run of `make verify` and thus should not be modified manually.
The [`proofs`](/verification/rust_proofs/ace/proofs) subfolder contains the proofs for the individual functions.
These files can be modified because they are not touched by RefinedRust after their initial creation.
If the default RefinedRust proof automation does not succeed in completing the proof, (correct) manual proof steps will need to be added to complete the proof of the function.

In addition to the files managed by RefinedRust, the [`verification/theories`](/verification/theories) folder contains definitions and lemmas that are useful for specifying the Rust code.
These files are manually created and written, and imported into RefinedRust through annotations on the Rust code.

### Example: Architecture of the Page Token verification

|                     | Location |
|---------------------|----------|
| Rust source file    | [`security_monitor/src/core/page_allocator/page.rs`](/security-monitor/src/core/page_allocator/page.rs)         |
| Extra Coq theories  | [`verification/theories/memory_tracker/page/page_extra.v`](/verification/theories/memory_tracker/page/page_extra.v)        |
| Generated files     |          |
| \|- generated code  | [`verification/rust_proofs/ace/generated/rust_proofs_ace.v`](/verification/rust_proofs/ace/generated/rust_proofs_ace.v)         |
| \|- generated specs | [`verification/rust_proofs/ace/generated/generated_specs_ace.v`](/verification/rust_proofs/ace/generated/generated_specs_ace.v)        |
| \|- proofs          | [`verification/rust_proofs/ace/proofs`](/verification/rust_proofs/ace/proofs)        |

As a more concrete example, let us consider the `Page` structure and the `Page::init` function.

For the `Page` structure, RefinedRust generates the following code:
1. in generated code: the definition `Page_sls` describing the layout of the `Page` struct
2. in generated specs: the definition `Page_ty` and `Page_inv_t` describing the `Page` struct type and the type containing the invariant specified through the annotations on the struct
The definition of the invariant on `Page` uses some extra (manually written) Coq theories, for instance the definition of the `page_size` Coq type.

For the `Page::read` function, RefinedRust generates the following code:
1. in generated code: the definition `core_page_allocator_page_Page_core_page_allocator_page_T_read_def` containing the source code of the function translated into RefinedRust's operational model Radium
2. in generated specs: the definition `type_of_core_page_allocator_page_Page_core_page_allocator_page_T_read` contains the annotated specification of the function translated into RefinedRust's refinement type system
3. the file `generated_template_core_page_allocator_page_Page_core_page_allocator_page_T_read.v` in [`verification/rust_proofs/ace/generated/`](/verification/rust_proofs/ace/generated) contains the lemma statement that RefinedRust will prove for the function and a proof script for function-specific parts of the proof.
4. the file [`proof_core_page_allocator_page_Page_core_page_allocator_page_T_read.v`](/verification/rust_proofs/ace/proofs/proof_core_page_allocator_page_Page_core_page_allocator_page_T_read.v) in [`verification/rust_proofs/ace/proofs/`](/verification/rust_proofs/ace/proofs) contains the proof of the lemma for the function.
  The default proof that RefinedRust generates will use the proof script from step 3 and then call into RefinedRust's generic automation.

## Getting Started
The [setup](setup.md) document details how to set the verification setup up on your system.

Here are some pointers to get you started with verifying more code in our setup:
- the [RefinedRust paper](https://dl.acm.org/doi/10.1145/3656422) explains the basics of the verification system and methodology with a few simple examples
- the [RefinedRust tutorial](https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev/-/blob/main/docs/tutorial.md?ref_type=heads) explains how to use RefinedRust on your own using a simple example
- the [RefinedRust documentation](https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev/-/blob/main/docs/SPEC_FORMAT.md?ref_type=heads) provides a technical documentation of the available annotations
- the page token implementation is documented extensively, so you may learn by example.

## Status

The following table documents the verification status of the security monitor's individual modules.
Some less interesting support modules are not included.

The Rust source path is relative to [`security_monitor/src`](/security_monitor/src/).

| Module                     | Rust source | Status                     | Remarks |
|----------------------------|-------------|----------------------------|---------|
| Memory isolation config       |           | Specififed, partly verified                           |         |
| \|- Page token                 | [`core/page_allocator/page.rs`](/security-monitor/src/core/page_allocator/page.rs)            | Specified, partly verified |         |
| \|- Page allocator             | [`core/page_allocator/allocator.rs`](/security-monitor/src/core/page_allocator/allocator.rs)            | Specified, not verified    |         |
| \|- Page table encoding        | [`core/architecture/riscv/mmu`](/security-monitor/src/core/architecture/riscv/mmu)            | Specified, not verified    |         |
| Initialization             | [`core/initialization`](/security-monitor/src/core/initialization)            | Specified, partly verified |         |
| VM Interactions            |             | Unspecified                |         |
| \|- Interface              | [`core/control_data`](/security-monitor/src/core/control_data)            |                            |         |
| \|- Confidential flow      | [`confidential_flow`](/security-monitor/src/confidential_flow)            |                            |         |
| \|- Non-confidential flow | [`non_confidential_flow`](/security-monitor/src/non_confidential_flow)            |                            |         |

### RefinedRust proof annotations

Rust functions are only translated and verified by RefinedRust if RefinedRust annotations (`#[rr::...]`) are attached to them.
If a function is annotated, the function is verified against that specification, except if one of the following opt-out annotations is present:
- `#[rr::only_spec]`: only the specification is generated, but the code is not translated and not verified
- `#[rr::trust_me]`: the specification and code are generated, but the code is not verified against the specification

These opt-out annotations help to progressively cover code with specification and delay the work on the verification itself. Eventually, a fully verified security monitor would not have any of the opt-out annotations and RefinedRust will verify that.

## Guarantees

### Verification goal

Currently, we aim to verify memory safety (i.e., the absence of null dereferences, data races, use-after-free, etc.) and functional correctness (i.e., the code does what it is functionally intended to) of the security monitor implementation.

In the future, we plan to verify (relaxed) non-interference, in order to show that confidential VMs are correctly isolated from each other and the hypervisor.
This will build on and directly integrate with our current verification of memory safety and functional correctness.


### Non-goals

A fully verified virtualization stack required a number of components, this project is focused on only one of those necessary components.
There are several efforts which are complementary to the aims of this project:

**Software**
* Hypervisor verification: While our security monitor architecture can ensure confidentiality of VMs without trusting the hypervisor, VMs may still need to communicate with the hypervisor (e.g. for IO). One may want to prove that the hypervisor is still trustworthy or that it responds correctly to hypercalls.
  Our architecture assumes that the hypervisor retains control over threads scheduling, so it is in control over the availability of confidential VMs. One might try to prove the correctness of the hypervisor in order to get availability guarantees.
* VM verification: In order to actually run a secure workload end-to-end, one would have to verify the code of confidential VMs protected by the security monitor.
* Low-level firmware/bootloader verification: Our security monitor currently builds on OpenSBI, which we trust.
  In future work, we would like to deprivilege firmware (see discussions in the RISC-V community on M-mode partitioning or M-mode lightweight isolation) or reimplement and prove the minimal set of required functionalities of the M-mode firmware (e.g., OpenSBI).

**Hardware**
* verification of ISA security: Our security monitor relies on hardware components, such as RISC-V physical memory protection (PMP) or the memory management unit (MMU). We have to trust that these mechanisms provided by the RISC-V ISA are actually secure and do not allow unintentional information flow when correctly configured.
* microarchitectural verification: We need to rely on the hardware correctly implementing the ISA, and that the hardware has no side-channels that allow information flow beyond what is specified in the ISA.
* designing secure hardware

**Verification technology**
* Compiler verification: We verify the Rust code against a model of the Rust semantics, but what actually runs on the hardware is the compiled assembly code. To transfer our verification results to the compiled code, we need a verified compiler for Rust.
* Assembly verification: Currently, we do not verify the small parts of the code written in assembly.
* Multi-language verification: Combining verification results for multiple languages such as Rust and Assembly is a challenging problem.

### Rust model
RefinedRust verifies the Rust code against a model of the Rust semantics, specialized to 64-bit pointers (i.e., `sizeof(usize) = 64`) and Little Endian semantics.

As there is no authoritative Rust semantics yet, RefinedRust's model necessarily has inaccuracies with respect to how the Rust compiler behaves.
The most important limitations of RefinedRust's model include following aspects of the Rust semantics:
- weak memory semantics (i.e., RefinedRust assumes sequential consistency)

### Assembly semantics
In the current stage of the project, we do not yet verify the inline Assembly semantics and specifics of the RISC-V core (e.g. when switching execution between a VM and the security monitor).
Accurate verification of multi-language programs and verification of system software against authoritative ISA semantics are an open research problem under active research.

### Trusted Computing Base
RefinedRust's is a foundational verification tool (i.e., the proofs are done in a proof assistant with a small proof kernel; concretely, the Coq proof assistant), and as such its trusted computing base is fairly small.
The risk of unintentional soundness bugs is much lower compared to tools relying on, e.g., SMT solvers.

Nevertheless, there are some code parts which have to be trusted:
- the formalization of Rust's operational semantics in RefinedRust
- the statement of RefinedRust's top-level soundness statement
- the translation from Rust's MIR intermediate representation to RefinedRust's Coq code

If you want to validate the behavior of the generated machine code with the verification, you have to add the translation from MIR to machine code in the Rust compiler.
On the other hand, if you want to validate that your surface-level Rust code has the correct behavior, you have to add the translation from surface-level Rust to MIR.

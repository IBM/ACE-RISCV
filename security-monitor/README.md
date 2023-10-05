# Security monitor
Our formal proof efforts focus on the security monitor implementation. The security monitor is implemented in Rust. There are minor parts that require assembly, e.g., context switches. Read more about our approach in the [paper](https://arxiv.org/abs/2308.10249).

**This is an active research project, without warranties of any kind.**

## Dependencies
To speed up the MVP implementation, we use OpenSBI as a firmware. OpenSBI runs in the M-mode. The ultimate goal is to deprivilege it or re-implement in Rust and formally prove. There is ongoing work at RISC-V community on partitioning M-mode firmware.

Our principle is to rely on as minimal Rust runtime dependencies as possible. Currently, we use the `riscv crate` because it provides a simplified interface to interact with RISC-V architecture. We consider deriving a minimal required subset of RISC-V registers and CSRs from the spec and then remove the `riscv crate` dependency.

## Proofs
We will interatively add our proofs to the repository.
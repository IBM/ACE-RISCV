# Security monitor
Our formal proof efforts focus on the security monitor implementation. The security monitor is implemented in Rust. There are minor parts that require assembly, e.g., context switches. Read more about our approach in the [paper](https://arxiv.org/abs/2308.10249).

## Implementation
<img src="../.github/fsm.png" align="center" width="60%"> 

Above Figure presents the finite state machine (FSM) implemented by the security monitor. [Non-confidential Flow](src/non_confidential_flow) (orange) implements part of the security monitor that responds to hypervisor requests. [Confidential Flow](src/confidential_flow) (blue) implements part of the security monitor that response to confidential VM requests. Heavy context switch, i.e., switch between security domains, occures during ["stealing"](https://github.com/IBM/ACE-RISCV/blob/main/security-monitor/src/core/control_data/confidential_vm.rs) and ["returning"](https://github.com/IBM/ACE-RISCV/blob/main/security-monitor/src/core/control_data/confidential_vm.rs) a confidential hart from/to a confidential VM.

## Dependencies
To speed up the implementation, we used OpenSBI as firmware. OpenSBI runs together with the security monitor in the M-mode. The ultimate goal is to deprivilege it or re-implement it in Rust and then formally verify. Our principle is to rely on as minimal Rust dependencies as possible.

## Proofs
We will interatively add our proofs to the repository. Check the [verification](../verification/) folder to learn more.

# Citation
**This is an active research project, without warranties of any kind.**

```
@inproceedings{ozga2023riscvtee,
    title={Towards a Formally Verified Security Monitor for VM-based Confidential Computing},
    author={Ozga, Wojciech and Hunt, Guerney D. H. and Le, Michael V. and Palmer, Elaine R. and Shinnar, Avraham},
    booktitle = {Proceedings of the 12th International Workshop on Hardware and Architectural Support for Security and Privacy},
    series = {HASP2023},
    year={2023}
}
```

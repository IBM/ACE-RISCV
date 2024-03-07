# Security monitor
Our formal proof efforts focus on the security monitor implementation. The security monitor is implemented in Rust. There are minor parts that require assembly, e.g., context switches. Read more about our approach in the [paper](https://arxiv.org/abs/2308.10249).

**This is an active research project, without warranties of any kind.**

## Dependencies
To speed up the MVP implementation, we use OpenSBI as a firmware. OpenSBI runs in the M-mode. The ultimate goal is to deprivilege it or re-implement it in Rust and then formally prove. There is ongoing work at RISC-V community on partitioning M-mode firmware.

Our principle is to rely on as minimal Rust dependencies as possible.

## Proofs
We will interatively add our proofs to the repository. Check the [verification](../verification/) folder to learn more.

# Citation
```
@inproceedings{ozga2023riscvtee,
    title={Towards a Formally Verified Security Monitor for VM-based Confidential Computing},
    author={Ozga, Wojciech and Hunt, Guerney D. H. and Le, Michael V. and Palmer, Elaine R. and Shinnar, Avraham},
    booktitle = {Proceedings of the 12th International Workshop on Hardware and Architectural Support for Security and Privacy},
    series = {HASP2023},
    year={2023}
}
```

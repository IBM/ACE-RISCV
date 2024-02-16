# Confidential VM (CVM)
This folder contains sample confidential VMs. A confidential VM is a workload that executes confidentially on the ACE infrastructure. The hypervisor, virtual machines, other confidential VMs, untrusted peripherial devices are considered untrusted.

## Baremetal CVM
A baremetal confidenital VM is a minimal proof of concept VM that leverages ACE to run confidentially. It is a bare metal application running in virtual supervisor mode that tests presence of certain hypercalls and virtIO.

## Linux VM
It is a proof of concept that linux-based VMs can execute in a trusted execution environment (TEE) provided by ACE.
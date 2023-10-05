# Confidential VM (CVM)
This folder contains sample confidential VMs. A confidential VM is a workload that executes confidentially on the ACE infrastructure. The hypervisor, virtual machines, other confidential VMs, untrusted peripherial devices are considered untrusted.

## Baremetal CVM
A baremetal CVM is a minimal proof of concept VM that leverages ACE to run confidentially. It is a bare metal application running in virtual supervisor mode that tests presence of certain hypercalls and virtIO.
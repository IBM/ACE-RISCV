# Security Monitor Source Code
The source code is structured accordingly to the finite state machine (Figure below). During the boot of the platform, boot firmware calls the [initialization procedure](core/initialization). After that, the security monitor only executes on explicit calls from hypervisor or confidential harts.

<img src="../.github/fsm.png" align="center" width="60%"> 

## Non-confidential flow
Hypervisor calls traps to the [assembly context switch](non_confidential_flow/lightweight_context_switch/enter_from_hypervisor_or_vm.S) in the non-confidential part of the finite state machine (FSM). [The finite state machine](non_confidential_flow/finite_state_machine.rs) implements the FSM that invokes [handlers](non_confidential_flow/handlers/).

## Confidential flow
Confidential hart calls trap to the [assembly context switch](confidential_flow/lightweight_context_switch/enter_from_confidential_hart.S) in the confidential part of the FSM. [The finite state machine](confidential_flow/finite_state_machine.rs) implements the router that invokes [handlers](confidential_flow/handlers/).

## Core
Security monitor functionality that manages confidential VMs and reconfigures hardware components is in [core](core/). 
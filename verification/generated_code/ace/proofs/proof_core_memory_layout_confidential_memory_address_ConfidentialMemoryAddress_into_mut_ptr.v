From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace.
From sm.ace.generated Require Import generated_template_core_memory_layout_confidential_memory_address_ConfidentialMemoryAddress_into_mut_ptr.

Set Default Proof Using "Type".

Section proof.
Context `{!typeGS Σ}.
Lemma core_memory_layout_confidential_memory_address_ConfidentialMemoryAddress_into_mut_ptr_proof (π : thread_id) :
  core_memory_layout_confidential_memory_address_ConfidentialMemoryAddress_into_mut_ptr_lemma π.
Proof.
  core_memory_layout_confidential_memory_address_ConfidentialMemoryAddress_into_mut_ptr_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Admitted. (* admitted due to admit_proofs config flag *)
End proof.
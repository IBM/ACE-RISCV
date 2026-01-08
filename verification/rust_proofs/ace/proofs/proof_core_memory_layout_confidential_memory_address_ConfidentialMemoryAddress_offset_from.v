From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_memory_layout_confidential_memory_address_ConfidentialMemoryAddress_offset_from.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_memory_layout_confidential_memory_address_ConfidentialMemoryAddress_offset_from_proof (π : thread_id) :
  core_memory_layout_confidential_memory_address_ConfidentialMemoryAddress_offset_from_lemma π.
Proof.
  core_memory_layout_confidential_memory_address_ConfidentialMemoryAddress_offset_from_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

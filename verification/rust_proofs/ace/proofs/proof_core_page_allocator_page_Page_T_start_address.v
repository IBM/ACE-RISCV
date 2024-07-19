From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace.
From sm.ace.generated Require Import generated_template_core_page_allocator_page_Page_T_start_address.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
Lemma core_page_allocator_page_Page_T_start_address_proof (π : thread_id) :
  core_page_allocator_page_Page_T_start_address_lemma π.
Proof.
  core_page_allocator_page_Page_T_start_address_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Admitted. (* admitted due to admit_proofs config flag *)
End proof.

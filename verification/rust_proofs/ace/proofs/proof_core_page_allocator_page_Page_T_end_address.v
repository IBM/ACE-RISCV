From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace.
From sm.ace.generated Require Import generated_template_core_page_allocator_page_Page_T_end_address.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
Lemma core_page_allocator_page_Page_T_end_address_proof (π : thread_id) :
  core_page_allocator_page_Page_T_end_address_lemma π.
Proof.
  core_page_allocator_page_Page_T_end_address_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { revert select (_ ≤ (conf_end _).2).
    specialize (conf_end_in_usize x0).
    rewrite /page_size_in_bytes_nat; solve_goal. }
  { revert select (_ ≤ (conf_end _).2).
    specialize (conf_end_in_usize x0).
    rewrite /page_size_in_bytes_nat; solve_goal. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

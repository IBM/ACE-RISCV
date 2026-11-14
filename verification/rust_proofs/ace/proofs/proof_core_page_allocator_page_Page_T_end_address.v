From radium Require Import lang notation.
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
  (* !start proof(page.accessors) *)
  { clear_layout.
    destruct (conf_end_in_usize MEMORY_CONFIG) as [? ?].
    lia. }
  (* !end proof *)
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

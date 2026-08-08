From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_closure0.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_closure0_proof (π : thread_id) :
  core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_closure0_lemma π.
Proof.
  core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_closure0_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  (* !start proof(page.divide) *)
  - (* add *)
    eapply aligned_to_offset.
    { apply Haligned. }
    rewrite page_size_align_is_size.
    apply Z.divide_factor_r.
  - exfalso.
    rename select (¬ _ < _ ≤ _) into Herr.
    apply Herr.
    split; last lia.
    move: Hinrange.
    specialize (page_size_in_bytes_nat_ge capture_smaller_page_size_).
    nia.
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

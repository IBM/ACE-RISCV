From caesium Require Import lang notation.
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
  apply_update (updateable_copy_lft "vlft7" "ulft5").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "plft21" "vlft7").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft9" "ulft5").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft11" "ulft5").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "plft24" "vlft11").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "plft22" "ulft5").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft29" "ulft5").
  rep <-! liRStep. liShow.
  apply_update (updateable_copy_lft "vlft30" "ulft5").
  rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
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

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

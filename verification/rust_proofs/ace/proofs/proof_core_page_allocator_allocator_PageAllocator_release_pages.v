From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageAllocator_release_pages.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageAllocator_release_pages_proof (π : thread_id) :
  core_page_allocator_allocator_PageAllocator_release_pages_lemma π.
Proof.
  core_page_allocator_allocator_PageAllocator_release_pages_prelude.

  (* !start proof(page_allocator.release_pages) *)
  rep <-! liRStep; liShow.
  (* TODO: lots of spurious lifetimes, due to latebound instantiation (see #27) *)
  apply_update (updateable_copy_lft "vlft3" "static").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft10" "vlft5").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft12" "vlft5").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft14" "vlft5").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft16" "vlft5").
  rep <-! liRStep; liShow.
  rep <- 2 liRStep; liShow.
  { rep liRStep.
    unfold once_initialized. rep liRStep. }
  rep liRStep.
  (* !end proof *)


  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

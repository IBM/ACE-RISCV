From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageAllocator_acquire_page.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageAllocator_acquire_page_proof (π : thread_id) :
  core_page_allocator_allocator_PageAllocator_acquire_page_lemma π.
Proof.
  core_page_allocator_allocator_PageAllocator_acquire_page_prelude.

  (* TODO: lots of spurious lifetimes, due to latebound instantiation (see #27) *)
  (* !start proof(page_allocator.acquire_page) *)
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft5" "static").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft16" "vlft6").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft18" "vlft6").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft20" "vlft6").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft22" "vlft6").
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

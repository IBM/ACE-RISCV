From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageAllocator_acquire_page_closure0.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageAllocator_acquire_page_closure0_proof (π : thread_id) :
  core_page_allocator_allocator_PageAllocator_acquire_page_closure0_lemma π.
Proof.
  core_page_allocator_allocator_PageAllocator_acquire_page_closure0_prelude.

  rep <-! liRStep; liShow.
  (* !start proof(page_allocator.acquire_page) *)
  apply_update (updateable_copy_lft "ulft3" "ulft_4").
  rep <-! liRStep; liShow.
  (* !end proof *)

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  (* !start proof(page_allocator.acquire_page) *)
  1-2: congruence.
  { rename select (if_Ok _ _) into Hok.
    match type of Hok with if_Ok ?x _ => rename x into maybe_tok end.
    destruct maybe_tok; simpl in *; solve_goal. }
  (* !end proof *)
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

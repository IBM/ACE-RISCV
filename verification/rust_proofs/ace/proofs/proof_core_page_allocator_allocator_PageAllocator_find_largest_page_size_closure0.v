From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageAllocator_find_largest_page_size_closure0.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageAllocator_find_largest_page_size_closure0_proof (π : thread_id) :
  core_page_allocator_allocator_PageAllocator_find_largest_page_size_closure0_lemma π.
Proof.
  core_page_allocator_allocator_PageAllocator_find_largest_page_size_closure0_prelude.

  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft6" "ulft1").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "ulft3" "ulft_4").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft15" "ulft1").
  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

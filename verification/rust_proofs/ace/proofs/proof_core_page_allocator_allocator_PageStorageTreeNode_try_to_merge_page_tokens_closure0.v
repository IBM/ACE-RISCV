From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageStorageTreeNode_try_to_merge_page_tokens_closure0.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageStorageTreeNode_try_to_merge_page_tokens_closure0_proof (π : thread_id) :
  core_page_allocator_allocator_PageStorageTreeNode_try_to_merge_page_tokens_closure0_lemma π.
Proof.
  core_page_allocator_allocator_PageStorageTreeNode_try_to_merge_page_tokens_closure0_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { split.
    - intros ?. revert INV_CASE. sidecond_hammer.
    - intros (? & ->). revert INV_CASE. unfold page_storage_node_invariant_case.
      destruct (allocation_state child) eqn:Heq; simpl; sidecond_hammer. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

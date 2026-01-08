From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_closure0.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_closure0_proof (π : thread_id) :
  core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_closure0_lemma π.
Proof.
  core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_closure0_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { unfold page_node_can_allocate.
    revert INV_CASE.
    destruct (node.(allocation_state)) eqn:Heq; simpl.
    all: normalize_and_simpl_impl false.
    all: clear; sidecond_hammer. 
  }

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

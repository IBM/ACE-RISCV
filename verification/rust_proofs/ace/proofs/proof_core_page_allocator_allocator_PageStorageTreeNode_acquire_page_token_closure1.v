From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_closure1.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_closure1_proof (π : thread_id) :
  core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_closure1_lemma π.
Proof.
  core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_closure1_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { f_equiv; first done.
    move: INV_CASE.
    unfold page_node_can_allocate.
    destruct (allocation_state child) eqn:Heq. 
    all: sidecond_hammer. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

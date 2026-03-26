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
  (* !start proof(page_allocator.acquire_page_token) *)
  { unfold page_node_can_allocate.
    opose proof* (page_storage_node_invariant_case_can_allocate) as Heq; first apply INV_CASE.
    rewrite -Heq. unfold page_node_can_allocate.
    unfold ord_le.
    split; solve_goal.
  }
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageStorageTreeNode_store_page_token_in_this_node.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Hint Unfold Z.divide : lithium_rewrite. 

Lemma core_page_allocator_allocator_PageStorageTreeNode_store_page_token_in_this_node_proof (π : thread_id) :
  core_page_allocator_allocator_PageStorageTreeNode_store_page_token_in_this_node_lemma π.
Proof.
  core_page_allocator_allocator_PageStorageTreeNode_store_page_token_in_this_node_prelude.

  rep liRStep; liShow.
  (* !start proof(page_allocator.store_page_token_in_this_node) *)
  { liInst Hevar_rf (mk_page_node self.(max_node_size) self.(base_address) PageTokenAvailable self.(children_initialized)).
    rep liRStep; liShow. }
  (* !end proof *)

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  (* !start proof(page_allocator.store_page_token_in_this_node) *)
  { move: INV_CASE.
    unfold name_hint. unfold page_storage_node_invariant_case.
    solve_goal. }
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

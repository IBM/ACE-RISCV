From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_from_this_node.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Hint Unfold Z.divide : lithium_rewrite.

Lemma core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_from_this_node_proof (π : thread_id) :
  core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_from_this_node_lemma π.
Proof.
  core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_from_this_node_prelude.

  rep <-! liRStep; liShow.
  (* !start proof(page_allocator.acquire_page_token_from_this_node) *)
  rep liRStep.
  liInst Hevar_rf (mk_page_node self.(max_node_size) self.(base_address) PageTokenUnavailable self.(children_initialized)).
  rep liRStep.
  (* !end proof *)

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

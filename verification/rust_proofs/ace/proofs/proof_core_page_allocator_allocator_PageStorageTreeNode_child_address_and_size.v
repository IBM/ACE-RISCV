From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageStorageTreeNode_child_address_and_size.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageStorageTreeNode_child_address_and_size_proof (π : thread_id) :
  core_page_allocator_allocator_PageStorageTreeNode_child_address_and_size_lemma π.
Proof.
  core_page_allocator_allocator_PageStorageTreeNode_child_address_and_size_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  (* !start proof(page_allocator.child_address_and_size) *)
  all: rename select (page_size_smaller _ = Some _) into Hsz.
  - opose proof (page_size_multiplier_size_in_bytes this_node_page_size _ _) as Heq.
    { rewrite Hsz//. }
    specialize (page_size_in_bytes_nat_in_usize this_node_page_size) as [].
    nia.
  - (* samei *)
    move: INV_IN_RANGE.
    opose proof (page_size_multiplier_size_in_bytes this_node_page_size _ _) as ->.
    { rewrite Hsz//. }
    nia.
  - unfold child_base_address.
    f_equiv. rewrite Z.mul_comm. f_equiv.
    congruence.
  - congruence.
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

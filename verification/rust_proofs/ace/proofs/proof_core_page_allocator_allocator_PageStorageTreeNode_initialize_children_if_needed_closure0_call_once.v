From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageStorageTreeNode_initialize_children_if_needed_closure0_call_once.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageStorageTreeNode_initialize_children_if_needed_closure0_call_once_proof (π : thread_id) :
  core_page_allocator_allocator_PageStorageTreeNode_initialize_children_if_needed_closure0_call_once_lemma π.
Proof.
  core_page_allocator_allocator_PageStorageTreeNode_initialize_children_if_needed_closure0_call_once_prelude.

  repeat liRStep; liShow.
  (* !start proof(page_allocator.initialize_children_if_needed) *)
  liInst Hevar_x0 node_size. liInst Hevar_x2 (n * page_size_align node_size).
  rep liRStep; liShow.
  (* !end proof *)

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

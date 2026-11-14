From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_drop_glue_core_page_allocator_allocator_PageAllocator.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma drop_glue_core_page_allocator_allocator_PageAllocator_proof (π : thread_id) :
  drop_glue_core_page_allocator_allocator_PageAllocator_lemma π.
Proof.
  drop_glue_core_page_allocator_allocator_PageAllocator_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  match goal with
  | H : max_node_size ?node = Size128TiB |- _ =>
      liInst Hevar_node node;
      liInst Hevar_base_addr (base_address node);
      liInst Hevar_node_size (max_node_size node)
  end.
  rep <-! liRStep; liShow.
  match goal with
  | H : max_node_size _ = Size128TiB |- _ => rewrite H
  end.
  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

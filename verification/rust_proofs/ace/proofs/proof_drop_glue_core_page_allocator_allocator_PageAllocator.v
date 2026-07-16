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
  liInst Hevar_node x1.
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

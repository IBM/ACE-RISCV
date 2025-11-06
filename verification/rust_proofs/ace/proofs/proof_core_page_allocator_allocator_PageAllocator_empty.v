From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageAllocator_empty.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageAllocator_empty_proof (π : thread_id) :
  core_page_allocator_allocator_PageAllocator_empty_lemma π.
Proof.
  core_page_allocator_allocator_PageAllocator_empty_prelude.

  repeat liRStep; liShow.
  liInst Hevar Size128TiB.
  liInst Hevar0 0.
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. 
  { exists 0. lia. }
  { apply page_size_in_bytes_nat_in_usize. }
  all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

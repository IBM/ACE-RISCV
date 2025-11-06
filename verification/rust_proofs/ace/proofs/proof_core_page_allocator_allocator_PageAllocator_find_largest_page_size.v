From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageAllocator_find_largest_page_size.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageAllocator_find_largest_page_size_proof (π : thread_id) :
  core_page_allocator_allocator_PageAllocator_find_largest_page_size_lemma π.
Proof.
  core_page_allocator_allocator_PageAllocator_find_largest_page_size_prelude.

  rep liRStep; liShow. 
  1: match goal with 
  | H : capture_address_ `aligned_to` page_size_in_bytes_nat ?x, 
    H' : page_size_smaller ?x = Some ?x' |- _ => 
      rename x into sz_aligned;
      rename x' into sz_aligned_smaller;
      rename H' into Hsmaller
  end.
  1: rewrite Hsmaller.
  all: rep liRStep; liShow.
  1: match goal with 
  | H : address `aligned_to` page_size_in_bytes_nat ?x, 
    H' : page_size_smaller ?x = Some ?x' |- _ => 
      rename x into sz_aligned;
      rename x' into sz_aligned_smaller;
      rename H' into Hsmaller
  end.
  1: rewrite Hsmaller.
  all: rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  all: try match goal with 
    | H : _ `aligned_to` page_size_in_bytes_nat ?x |- _ =>
        rename x into sz';
        specialize (page_size_in_bytes_nat_ge sz') as ?
    end.
  all: try lia.
  all: by eapply address_aligned_to_page_size_smaller.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

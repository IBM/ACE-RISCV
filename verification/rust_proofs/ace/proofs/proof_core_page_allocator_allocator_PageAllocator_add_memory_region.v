From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageAllocator_add_memory_region.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageAllocator_add_memory_region_proof (π : thread_id) :
  core_page_allocator_allocator_PageAllocator_add_memory_region_lemma π.
Proof.
  core_page_allocator_allocator_PageAllocator_add_memory_region_prelude.

  rep <-! liRStep; liShow.
  all: match goal with
  | H : ?x `aligned_to` page_size_in_bytes_nat _ |- _ => rename x into larr
  end.
  all: try match goal with
  | H : ?x = Size4KiB ∨ _.2 + _ ≤ _ |- _ =>
      rename x into sz_to_allocate;
      rename H into Hsz_bounds
  end.

  { (* calling Page::init *)
    apply_update (updateable_split_array larr (page_size_in_bytes_nat sz_to_allocate)).
    liRStepUntil typed_val_expr.
    apply_update (updateable_reshape_array larr (page_size_in_words_nat sz_to_allocate) bytes_per_addr).
    liRStepUntil typed_val_expr.
    iRename select (larr ◁ₗ[_, _] _ @ (◁ _))%I into "Harr".
    iApply fupd_typed_val_expr.
    iMod (ltype_own_array_subtype_strong _ _ _ _ (int usize) with "[] Harr") as "(% & Harr)"; [done | | | | | ].
    { shelve_sidecond. }
    { solve_layout_alg. }
    { shelve_sidecond. }
    { iModIntro. iIntros (??) "Harr". iPoseProof (ty_own_val_array_int_to_int with "Harr") as "$"; last done.
      shelve_sidecond. }
    iModIntro.

    repeat liRStep. }
  repeat liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: try lia.
  all: try congruence.
  - rewrite -page_size_align_is_size /page_size_align.
    exists (page_size_align_log Size4KiB). lia.
  - sidecond_hammer.
  - specialize (page_size_in_bytes_nat_ge x').
    specialize (page_size_in_bytes_nat_in_usize x') as [].
    split; lia.
  - specialize (page_size_in_bytes_nat_ge x').
    specialize (page_size_in_bytes_nat_in_usize x') as [].
    sidecond_hammer.
  - unfold page_size_in_bytes_nat. lia.
  - specialize (page_size_in_words_nat_ge sz_to_allocate). lia.
  - intros ? Hly1. apply syn_type_has_layout_array_inv in Hly1 as (? & Hly1 & -> & ?).
    apply syn_type_has_layout_int_inv in Hly1 as ->.
    eexists. split; first by apply syn_type_has_layout_int.
    rewrite ly_size_mk_array_layout. done.
  - (* if location is aligned to page size, it's aligned to usize *)
    eapply base.aligned_to_mul_inv.
    revert select (larr `aligned_to` page_size_in_bytes_nat sz_to_allocate).
    done.
  - sidecond_hammer.
  - rewrite page_size_align_is_size. done.
  - rewrite MAX_PAGE_ADDR_unfold /MAX_PAGE_ADDR_def.
    revert select (¬ memory_region_end.2 > _).
    rewrite Hroot_sz. lia.
  - rename select (max_node_size _ = Size128TiB) into Hroot_sz'.
    rewrite Hroot_sz'.
    apply page_size_le_max.
  - rewrite Hroot_sz Hroot_base.
    split; simpl.
    + lia.
    + revert select (larr.2 + _ ≤ MAX_PAGE_ADDR). rewrite MAX_PAGE_ADDR_unfold /MAX_PAGE_ADDR_def. lia.
  - apply aligned_to_offset; first done.
    solve_goal.

  all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

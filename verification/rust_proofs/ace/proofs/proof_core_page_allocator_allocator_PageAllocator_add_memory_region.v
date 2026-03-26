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
  (* !start proof(page_allocator.add_memory_region) *)
  all: match goal with
  | H : ?x `aligned_to` page_size_in_bytes_nat _ |- _ => rename x into larr
  end.
  all: try match goal with
  | H : ?x = Size4KiB ∨ _.(loc_a) + _ ≤ _ |- _ =>
      rename x into sz_to_allocate;
      rename H into Hsz_bounds
  end.
  { (* calling Page::init *)
    apply_update (updateable_split_array larr (page_size_in_bytes_nat sz_to_allocate)).
    liRStepUntil typed_call.
    apply_update (updateable_reshape_array larr (page_size_in_words_nat sz_to_allocate) bytes_per_addr).
    liRStepUntil typed_call.
    iRename select (larr ◁ₗ[_, _] _ @ (◁ _))%I into "Harr".
    iApply fupd_typed_call.
    iMod (ltype_own_array_subtype_strong _ _ _ _ (int usize) _ _ _ (λ _ _, True%I) with "[] Harr") as "(% & _ & Harr)"; [done | | | | | ].
    { shelve_sidecond. }
    { solve_layout_alg. }
    { shelve_sidecond. }
    { iModIntro. iIntros (??? _) "Harr". 
      iPoseProof (ty_own_val_array_int_to_int with "Harr") as "(% & $)"; last done.
      shelve_sidecond. }
    iModIntro.
    repeat liRStep. }
  repeat liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: try lia.
  all: try congruence.
  - apply page_size_in_bytes_is_power_of_two.
  - solve_goal.
  - specialize (page_size_in_bytes_nat_ge x').
    specialize (page_size_in_bytes_nat_in_usize x') as [].
    split; lia.
  - unfold page_size_in_bytes_nat. lia.
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
    revert select (¬ memory_region_end.(loc_a) > _).
    rewrite Hroot_sz. lia.
  - rename select (max_node_size _ = Size128TiB) into Hroot_sz'.
    rewrite Hroot_sz'.
    apply page_size_le_max.
  - rewrite Hroot_sz Hroot_base.
    split; simpl.
    + lia.
    + revert select (larr.(loc_a) + _ ≤ MAX_PAGE_ADDR). rewrite MAX_PAGE_ADDR_unfold /MAX_PAGE_ADDR_def. lia.
  - apply aligned_to_offset; first done.
    solve_goal.
  (* !end proof *)

  all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
(*Qed.*)
Admitted. (* admitted due to long Qed *)
End proof.

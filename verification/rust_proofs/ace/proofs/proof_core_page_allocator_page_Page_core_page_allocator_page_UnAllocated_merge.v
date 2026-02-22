From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_merge.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* !start proof(page.merge) *)
Lemma extract_page_token_invariants `{!onceG Σ memory_layout} `{!MachineConfig} {S_rt : RT} (S_attrs : core_page_allocator_page_PageState_spec_attrs S_rt) (S_ty : type S_rt) π xs xs' F :
  lftE ⊆ F →
  ([∗ list] x1; x2 ∈ xs'; xs, (core_page_allocator_page_Page_inv_t_inv_spec S_rt S_attrs <TY> S_ty <INST!>).(inv_P) π x1 x2) ={F}=∗
  ([∗ list] p ∈ xs, ⌜p.(page_loc).(loc_p) = ProvAlloc machine_memory_prov⌝ ∗ p.(page_loc) ◁ₗ[π, Owned] # (<#> p.(page_val)) @ ◁ array_t (page_size_in_words_nat p.(page_sz)) (int usize)).
Proof.
  iIntros (?) "Ha".
  iApply big_sepL_fupd.
  iApply (big_sepL2_elim_l xs').
  iApply (big_sepL2_impl with "Ha").
  iModIntro. iIntros (? inner pg Hlook1 Hlook2) "Hinv".
  simpl. iDestruct "Hinv" as "(%MEM & -> & Hpg & % & % & ? & % & % & % & _)".
  rewrite /guarded. iDestruct "Hpg" as "(((Hc1 & _) & _)& Hpg)".
  iApply (lc_fupd_add_later with "Hc1"). iNext.
  iR. by iFrame.
Qed.
(* !end proof *)

Lemma core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_merge_proof (π : thread_id) :
  core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_merge_lemma π.
Proof.
  core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_merge_prelude.

  rep <-! liRStep; liShow.
  (* !start proof(page.merge) *)
  opose proof (lookup_lt_is_Some_2 from_pages (length from_pages - 1) _) as [pg_last Hlook_pg_last].
  { lia. }
  destruct pg_last as [pg_loc_last pg_sz_last pg_val_last].
  opose proof (page_size_multiplier_ge new_size) as ?.
  opose proof (lookup_lt_is_Some_2 from_pages 0%nat _) as [pg_0 Hlook_pg0].
  { lia. }
  destruct pg_0 as [pg_loc_0 pg_sz_0 pg_val_0].
  rep <-! liRStep; liShow.
  2-5: rep liRStep; liShow.

  iRename select (arg_from_pages ◁ₗ[π, Owned] _ @ _)%I into "Hvec".
  iApply updateable_add_fupd.
  iAcquireCredit as "Hcred".
  iMod (vec_extract_invariant with "Hcred Hvec") as "(%xs' & Hinv & Hvec)"; first done.
  iMod (extract_page_token_invariants with "Hinv") as "Harrs"; first done.

  iMod (array_t_ofty_merge_big_sep (int usize) π _ (page_size_in_words_nat pg_sz_0) ((λ p, <#> p.(page_val)) <$> from_pages) (pg_loc_0) with "[Harrs]") as "Harr"; first done.
  { rewrite length_fmap. lia. }
  { rewrite length_fmap. rewrite /size_of_st/use_layout_alg'. simpl.
    erewrite syn_type_has_layout_int; last done.
    simpl. rewrite Hlen.
    rewrite bytes_per_int_usize.

    specialize (page_size_in_bytes_nat_in_isize new_size) as [_ Hsz].
    move: Hsz. rewrite /page_size_in_bytes_nat.
    opose proof * (page_size_multiplier_size_in_words new_size smaller_sz) as Hw.
    { rewrite Hsmaller//. }
    rewrite Hw.
    apply Hlook in Hlook_pg0 as [Hsz0 _]. simpl in Hsz0.
    rewrite Hsz0. lia. }
  { rewrite big_sepL_fmap. iApply (big_sepL_impl with "Harrs").
    iModIntro. iIntros (? pg' Hlook').
    apply Hlook in Hlook'.
    iIntros "(%Hprov & Hb)".
    destruct Hlook' as [-> Hloc_eq].
    revert select (loc_p (page_loc (from_pages !!! 0%nat)) = ProvAlloc machine_memory_prov).
    move: Hloc_eq. erewrite list_lookup_total_correct; last done.
    simpl. apply Hlook in Hlook_pg0 as [Hsz_0 Hloc_0].
    simpl in Hsz_0. rewrite Hsz_0. 
    intros Heq_a Heq_prov.
    enough (page_loc pg' = (pg_loc_0 offsetst{IntSynType usize}ₗ (k * page_size_in_words_nat smaller_sz))) as -> by done.
    move: Hprov Heq_a Heq_prov. destruct (page_loc pg'); simpl.
    intros -> ->.
    destruct pg_loc_0; simpl. intros ->. 
    rewrite /OffsetLocSt /offset_loc/use_layout_alg'/=.
    rewrite /shift_loc.
    erewrite syn_type_has_layout_int; last done.
    simpl. 
    rewrite /page_size_in_bytes_nat bytes_per_int_usize.
    f_equiv. lia. }
  repeat iClear select (page_loc (from_pages !!! Z.to_nat 0) ◁ₗ[ π, Shared _] _ @ _)%I.
  iModIntro.
  rep liRStep; liShow.
  rewrite (list_lookup_total_correct _ 0 _ Hlook_pg0). simpl.
  rep liRStep; liShow.
  liInst Hevar_x0 (mjoin (page_val <$> from_pages)).
  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - rewrite Hlen. specialize (page_size_multiplier_ge new_size). lia.
  - specialize (page_size_in_words_nat_ge (page_sz (from_pages !!! 0%nat))). lia.
  - specialize (page_size_in_words_nat_ge (page_sz (from_pages !!! 0%nat))). lia.
  - rewrite page_size_multiplier_quot_Z; first solve_goal.
    rewrite Hsmaller.
    erewrite list_lookup_total_correct; last done.
    apply Hlook in Hlook_pg0 as [-> _]. done.
  - opose proof (Hlook (length from_pages - 1)%nat _) as [Hlast_sz Hlast_off]; first done.
    simpl in *.
    split; first solve_goal.
    rename select (loc_a pg_loc_last + _ ≤ MaxInt USize) into Hbound.
    move: Hbound.
    rewrite Hlast_off.
    rewrite Hlen.
    rewrite (page_size_multiplier_size_in_bytes new_size smaller_sz); last by rewrite Hsmaller.
    simpl. rewrite Hlast_sz. clear. nia.
  - revert select (¬ length from_pages > 2).
    rewrite Hlen.
    revert Hsmaller. clear.
    destruct new_size; first done.
    all: intros _; unfold page_size_multiplier, page_size_multiplier_log; lia.
  - rename select (loc_a _ + page_size_in_bytes_Z new_size ≠ loc_a pg_loc_last + _) into Hcontra.
    apply Hcontra.
    opose proof (Hlook (length from_pages - 1)%nat _ _) as Hlook_last; first done.
    simpl in Hlook_last.  destruct Hlook_last as [-> ->].
    rewrite (page_size_multiplier_size_in_bytes new_size smaller_sz); last by rewrite Hsmaller.
    rewrite Hlen.
    clear. specialize (page_size_multiplier_ge new_size). nia.
  - revert select (_ `quot` _ ≠ length from_pages).
    rewrite page_size_multiplier_quot_Z; first solve_goal.
    rewrite Hsmaller.
    erewrite list_lookup_total_correct; last done.
    apply Hlook in Hlook_pg0 as [-> _]. done.
  - revert select (¬ _ `aligned_to` _).
    rewrite -page_size_align_is_size. done.
  - rewrite Hlen.
    rewrite (page_size_multiplier_size_in_words new_size smaller_sz); last rewrite Hsmaller//.
    apply Hlook in Hlook_pg0. simpl in Hlook_pg0. destruct Hlook_pg0 as [-> _]. lia.
  - rewrite list_fmap_mjoin.
    f_equiv. rewrite list_fmap_compose//.
  - move: Haligned.
    erewrite list_lookup_total_correct; last done.
    done.
  - (* we should open the invariant of the last page token *)
    opose proof (Hlook (length from_pages - 1)%nat _) as [Hlast_sz Hlast_off]; first done.
    simpl in *.
    revert select (loc_a (page_loc (from_pages !!! (length from_pages - Z.to_nat 1)%nat)) + _ ≤ MAX_PAGE_ADDR).
    erewrite list_lookup_total_correct; last done.
    simpl. rewrite Hlast_off. rewrite Hlen.
    erewrite list_lookup_total_correct; last done.
    simpl.
    rewrite (page_size_multiplier_size_in_bytes new_size smaller_sz); last by rewrite Hsmaller.
    simpl. rewrite Hlast_sz. clear. nia.
  - revert select (loc_a (conf_start MEMORY_CONFIG) ≤ loc_a (page_loc (from_pages !!! 0%nat))).
    erewrite list_lookup_total_correct; last done.
    done.
  - opose proof (Hlook (length from_pages - 1)%nat _) as [Hlast_sz Hlast_off]; first done.
    simpl in *.
    revert select (loc_a (page_loc (from_pages !!! (length from_pages - Z.to_nat 1)%nat)) + _ ≤ loc_a (conf_end MEMORY_CONFIG)).
    erewrite list_lookup_total_correct; last done.
    simpl. rewrite Hlast_off. rewrite Hlen.
    erewrite list_lookup_total_correct; last done.
    simpl.
    rewrite (page_size_multiplier_size_in_bytes new_size smaller_sz); last by rewrite Hsmaller.
    simpl. rewrite Hlast_sz. clear. nia.
  - revert select (loc_p (page_loc (from_pages !!! 0%nat)) = ProvAlloc machine_memory_prov).
    erewrite list_lookup_total_correct; last done.
    done.
  - erewrite list_lookup_total_correct; last done.
    done.
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Admitted. (* admitted due to long Qed *)
End proof.

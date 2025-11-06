From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_proof (π : thread_id) :
  core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_lemma π.
Proof.
  core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_prelude.

  rep <-! liRStep. liShow.
  apply_update (updateable_copy_lft "plft27" "plft31").
  rep <-! liRStep. liShow.
  apply_update (updateable_copy_lft "plft28" "plft32").
  rep <-! liRStep. liShow.
  apply_update (updateable_copy_lft "plft29" "plft33").
  rep <-! liRStep. liShow.
  apply_update (updateable_copy_lft "plft30" "plft34").
  rep <-! liRStep. liShow.

  rename self1 into pageval.
  rename self0 into sz.
  set (smaller_sz := default sz (page_size_smaller sz)).

  (* strip later *)
  apply_update (updateable_ltype_strip_later self).
  rep <-! liRStep; liShow.
  iRename select (self ◁ₗ[_, _] _ @ (◁ _))%I into "Harr".

  (* split up the array *)
  apply_update (updateable_add_fupd).
  iMod (array_t_ofty_split_reshape _ _ _ _ (page_size_multiplier sz) (page_size_in_words_nat smaller_sz) with "Harr") as "Harr"; [done | |].
  { rewrite (page_size_multiplier_size_in_words _ smaller_sz); last done. lia. }
  iModIntro.

  rename select memory_layout into memly.

  (* let's set the invariant *)
  set (INV := (λ (π : thread_id) (it : (Z * Z)) (clos : RT_xt (plistRT [page_sizeRT; memory_layoutRT; loc : RT; loc: RT])),
  (
    let '(itstart', itend') := it in
    let '*[smaller_sz'; memlayout; startloc; endloc] := clos in

    let itstart := Z.to_nat itstart' in
    let itend := Z.to_nat itend' in

    ⌜0 ≤ itstart'⌝ ∗ ⌜itend' = Z.of_nat (page_size_multiplier sz)⌝ ∗
    ⌜endloc = (self +ₗ page_size_in_bytes_Z sz)⌝ ∗ ⌜startloc = self⌝ ∗
    ⌜memlayout = memly⌝ ∗
    ⌜smaller_sz' = smaller_sz⌝ ∗
    once_status "MEMORY_LAYOUT" (Some memly) ∗
    [∗ list] i ∈ seq itstart (itend - itstart)%nat,
    ((startloc +ₗ (i * page_size_in_bytes_Z smaller_sz)) ◁ₗ[π, Owned false]
      # (<#> (take (page_size_in_words_nat smaller_sz)
        (drop (i * page_size_in_words_nat smaller_sz) pageval))) @ ◁ array_t (page_size_in_words_nat smaller_sz) (int usize))
  ) : iProp Σ)%I).

  rep liRStep; liShow.
  liInst Hevar INV.

  (* Prove initialization of the invariant *)
  unfold INV at 1.
  simpl.
  iApply prove_with_subtype_default.
  iSplitL "Harr".
  { iR.
    rewrite -page_size_multiplier_quot; last done.
    iSplitR. { rewrite page_size_multiplier_quot_Z; done. }
    iR. iR. iR. iR. iSplitR. { iExists _. iR. done. }
    iApply big_sepL2_elim_l. iPoseProof (big_sepL_extend_r with "Harr") as "Harr".
    2: iApply (big_sepL2_wand with "Harr").
    { rewrite List.length_seq length_reshape length_replicate. lia. }
    iApply big_sepL2_intro.
    { rewrite List.length_seq length_reshape length_replicate. lia. }
    iModIntro. iIntros (k ? ? Hlook1 Hlook2) "Ha".
    assert (k < page_size_multiplier sz).
    { eapply lookup_lt_Some in Hlook1. move: Hlook1. rewrite length_reshape length_replicate. lia. }
    rewrite lookup_seq_lt in Hlook2; last lia.
    injection Hlook2 as <-.
    unfold OffsetLocSt. simplify_layout_goal. unfold offset_loc.
    assert (ly_size usize * (k * page_size_in_words_nat smaller_sz) = k * page_size_in_bytes_Z smaller_sz) as ->.
    { rewrite /page_size_in_bytes_nat.
      simpl. rewrite bytes_per_int_usize. lia. }
    enough (x0 = (<#> take (page_size_in_words_nat smaller_sz) (drop (k * page_size_in_words_nat smaller_sz) pageval))) as -> by done.
    move: Hlook1. rewrite sublist_lookup_reshape.
    2: { specialize (page_size_in_words_nat_ge smaller_sz). lia. }
    2: {
      rename select (page_size_in_words_nat _ = length pageval) into Hpage_sz.
      rewrite length_fmap -Hpage_sz.
      erewrite (page_size_multiplier_size_in_words _ smaller_sz); last done.
      lia. }
    rewrite sublist_lookup_Some'.
    rewrite -fmap_drop -fmap_take.
    intros [? _]. done. }

  (* Prove preservation if the iterator emits an element *)
  liRStep; liShow. iApply prove_with_subtype_default.
  iSplitR.
  { liShow. iModIntro. simpl.
    iIntros ([istart itend] [itstart' itend'] (capture_smaller_sz & capture_memlayout & capture_start & capture_end & []) e) "Hnext (%Hstart & %Hend & -> & -> & -> & -> & Hinv)".
    rewrite boringly_persistent_elim. iDestruct "Hnext" as "%Hnext".
    simpl in Hnext. destruct Hnext as (<- & _ & <- & Hnext & [= Hcmp_eq]).
    case_bool_decide; last done.
    injection Hnext as [= ->].
    apply Z.cmp_less_iff in Hcmp_eq.
    remember ((Z.to_nat itend - Z.to_nat istart)%nat) as len eqn:Heq_len.
    destruct len. { exfalso. move: Hcmp_eq Heq_len Hstart Hend. lia. }
    iDestruct "Hinv" as "(#Hinv0 & Hinv1 & Hinv)".
    fold seq.
    iSplitL "Hinv0 Hinv1".
    { iExists _, istart, inhabitant, _, _, _, _. iR. iR.
      unfold name_hint. iFrame "#".
      iSplitR. { iPureIntro. simpl. lia. }
      iSplitR. { iPureIntro. lia. }
      opose proof (page_size_multiplier_size_in_bytes sz smaller_sz _) as Heq_sz; first done.
      iSplitR. { iPureIntro.
        subst itend.
        assert (page_size_in_bytes_Z sz ∈ usize) as Hel by done.
        rewrite Heq_sz in Hel.
        destruct Hel. split; nia. }
      iSplitR. { iPureIntro.
        rename select (self `aligned_to` _) into Hal.
        move: Hal. rewrite !page_size_align_is_size.
        rewrite Heq_sz.
        apply base.aligned_to_mul_inv. }
      iSplitR. {
        iPureIntro. simpl.
        subst itend.
        rewrite (page_size_multiplier_size_in_bytes sz smaller_sz); last done.
        move: Hcmp_eq. clear. nia. }
      iSplitR. { iPureIntro. simpl. lia. }
      rewrite Z2Nat.id; first done. lia. }
    iIntros (e' (capture_smaller_sz & capture_memlayout & capture_start & capture_end & [])).
    iIntros "(%v' & %i & % & % & % & % & % & %Heq1 & %Heq2 & -> & %Heq3)".
    injection Heq2 as <-.
    injection Heq1 as <- <- <- <-.
    injection Heq3 as -> -> -> ->.
    simpl. iSplitR. { iPureIntro. lia. }
    iR. iR. iR. iR. iR.
    replace ((S (Z.to_nat istart))) with (Z.to_nat (istart + 1%nat)) by lia.
    iR.
    assert ((Z.to_nat itend - Z.to_nat (istart + 1%nat))%nat = len)as ->; last done.
    { lia. }
  }
  (* Prove preservation if the iterator does not emit an element *)
  iApply prove_with_subtype_default.
  iSplitR.
  { liShow. iModIntro. simpl.
    iIntros ([istart itend] [itstart' itend'] (capture_smaller_sz & capture_memlayout & capture_start & capture_end & [])) "Hnext".
    rewrite boringly_persistent_elim. iDestruct "Hnext" as "%Hnext".
    simpl in Hnext. destruct Hnext as (<- & (Ha & <-) & _).
    injection Ha as <-.
    iIntros "Hinv". done.
  }
  rep <-! liRStep. liShow.

  rep liRStep. liShow.
  iApply prove_with_subtype_default.
  iRename select (MapInv _ _ _ _ _) into "Hinv".
  iSplitL "Hinv". { done. }

  rep <-! liRStep. liShow.

  (* discard the invariant on the original self token so that RefinedRust does not try to re-establish it *)
  iRename select (arg_self ◁ₗ[π, _] _ @ _)%I into "Hself".
  iPoseProof (opened_owned_discard with "Hself") as "Hself".

  rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - set (smaller_sz := (default self0 (page_size_smaller self0))).
    specialize (page_size_in_words_nat_ge smaller_sz).
    solve_goal.
  - set (smaller_sz := (default self0 (page_size_smaller self0))).
    specialize (page_size_in_words_nat_ge smaller_sz).
    solve_goal.
  - set (smaller_sz := (default self0 (page_size_smaller self0))).
    rewrite (page_size_multiplier_quot_Z _ smaller_sz); last done.
    specialize (page_size_multiplier_in_usize self0). solve_goal.
  - set (smaller_sz := (default self0 (page_size_smaller self0))).
    rewrite (page_size_multiplier_quot_Z _ smaller_sz); last done.
    specialize (page_size_multiplier_in_usize self0). solve_goal.
  - rename select (Forall2 _ _ _) into Hclos.
    opose proof (Forall2_length _ _ _ Hclos) as Hlen.
    rewrite length_seqZ in Hlen.
    rewrite page_size_multiplier_quot_Z in Hlen; last done.
    unfold subdivided_pages. simpl.
    split; first lia.
    rename x' into new_pages.
    intros i p' Hlook.
    opose proof (Forall2_lookup_r _ _ _ i _ Hclos Hlook) as (j & Hlook2 & Ha).
    apply lookup_seqZ in Hlook2 as (-> & Hlook2).
    move: Ha.
    normalize_and_simpl_goal.
    split; last done.
    rewrite /offset_loc. simpl.
    rewrite /page_size_in_bytes_nat.
    rewrite bytes_per_int_usize. f_equiv.
    rewrite /smaller_sz.
    lia.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

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

  Search once_status once_status_tok.
  Search once_status_tok.
  iRename select (once_init_tok _ memly) into "Htok1".
  iRename select (once_init_tok _ x) into "Htok2".
  iPoseProof (once_init_tok_agree with "Htok1 Htok2") as "<-".
  iRename select (once_status _ _) into "Hstatus".
  rename select (static_has_refinement _ _) into Hrfn1.
  iDestruct "Hstatus" as "(%x9 & %Hrfn & Htok3)".
  specialize (static_has_refinement_inj _ _ _ Hrfn1 Hrfn) as (Heq & Heq2).
  rewrite (UIP_refl _ _ Heq) in Heq2.
  simpl in Heq2. subst x9.

  (* Prove initialization of the invariant *)
  unfold INV at 1.
  simpl.
  iApply prove_with_subtype_default.
  iSplitL "Harr".
  { iR.
    rewrite -page_size_multiplier_quot; last done.
    iSplitR. { rewrite page_size_multiplier_quot_Z; done. }
    iR. iR. iR. iR. iSplitR. { iExists x4. iR. done. }
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
    { rewrite /page_size_in_bytes_Z /page_size_in_bytes_nat.
      simpl. rewrite bytes_per_int_usize. lia. }
    enough (x0 = (<#> take (page_size_in_words_nat smaller_sz) (drop (k * page_size_in_words_nat smaller_sz) pageval))) as -> by done.
    move: Hlook1. rewrite sublist_lookup_reshape.
    2: { specialize (page_size_in_words_nat_ge smaller_sz). lia. }
    2: { rewrite length_fmap -H122.
      erewrite (page_size_multiplier_size_in_words _ smaller_sz); last done.
      lia. }
    rewrite sublist_lookup_Some'.
    rewrite -fmap_drop -fmap_take.
    intros [? _]. done. }

  (* Prove preservation if the iterator emits an element *)
  liRStep; liShow. iApply prove_with_subtype_default.
  iSplitR.
  { liShow. iModIntro. simpl.
    iIntros ([istart itend] [itstart' itend'] (capture_smaller_sz & capture_memlayout & capture_start & capture_end & []) e Hnext) "(%Hstart & %Hend & -> & -> & -> & -> & Hinv)".
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
      iSplitR. { iPureIntro. unfold page_size_in_bytes_Z. simpl. lia. }
      iSplitR. { iPureIntro. lia. }
      opose proof (page_size_multiplier_size_in_bytes sz smaller_sz _) as Heq_sz; first done.
      iSplitR. { iPureIntro.
        subst itend.
        assert (page_size_in_bytes_Z sz ∈ usize) as Hel by done.
        rewrite /page_size_in_bytes_Z Heq_sz in Hel.
        rewrite /page_size_in_bytes_Z.
        destruct Hel. split; nia. }
      iSplitR. { iPureIntro.
        rename select (self `aligned_to` _) into Hal.
        move: Hal. rewrite !page_size_align_is_size.
        rewrite Heq_sz.
        apply base.aligned_to_mul_inv. }
      iSplitR. {
        iPureIntro. simpl.
        subst itend.
        rewrite /page_size_in_bytes_Z.
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
    iIntros ([istart itend] [itstart' itend'] (capture_smaller_sz & capture_memlayout & capture_start & capture_end & []) Hnext).
    simpl in Hnext. destruct Hnext as (<- & (Ha & <-) & _).
    injection Ha as <-.
    iIntros "Hinv". done.
  }
  rep <-! liRStep.
  liShow.

  (* discard the invariant on the original self token so that RefinedRust does not try to re-establish it *)
  iRename select (arg_self ◁ₗ[π, _] _ @ _)%I into "Hself".
  iPoseProof (opened_owned_discard with "Hself") as "Hself".

  clear Heq.

  (* derive inductive property about the result *)
  rename x' into new_pages.
  iRename select (IteratorNextFusedTrans _ _ _ _ _) into "Hiter".
  iAssert (⌜subdivided_pages (mk_page self sz pageval) new_pages⌝)%I with "[Hiter]" as "%Hnew_pages_correct".
  { simpl.
    unfold subdivided_pages. simpl.
    destruct (page_size_smaller sz) as [ sz_smaller | ] eqn:Hsmaller; subst smaller_sz.
    2: {
      rewrite Z.quot_same; first last.
      { specialize (page_size_in_bytes_nat_ge sz). unfold page_size_in_bytes_Z. lia. }
      assert (sz = Size4KiB) as ->. { by apply page_size_smaller_None. }
      destruct new_pages as [ | pg1 new_pages]; simpl.
      { iDestruct "Hiter" as "%Heq". injection Heq. simplify_eq. }
      iRevert "Hiter". rep liRStep; liShow.
      repeat case_bool_decide; simplify_eq.
      iRename select (IteratorNextFusedTrans _ _ _ _ _) into "Hiter".
      destruct new_pages as [ | pg2 new_pages]; simpl; first last.
      { iRevert "Hiter". rep liRStep. liShow.
        repeat case_bool_decide; simplify_eq. lia. }
      iRevert "Hiter".  rep liRStep. liShow.
      iPureIntro. split; first done.
      intros i p' Hlook. destruct i as [ | i]; last done.
      simpl in Hlook. injection Hlook as <-.
      simpl. done. }
    rewrite (page_size_multiplier_quot_Z _ sz_smaller); first last.
    { rewrite Hsmaller. done. }
    iRevert "Hiter". iClear "∗#".


    match goal with
    | |- context[IteratorNextFusedTrans ?attrs _ {| map_clos := ?clos |} _ ?fin] =>
        set (AT := attrs);
        set (final_state := fin);
        set (clos_state := clos)
    end.
    iAssert (∀ k : nat, IteratorNextFusedTrans AT π {| map_it := (Z.of_nat k, Z.of_nat $ page_size_multiplier sz); map_clos := clos_state |} new_pages final_state -∗
    ⌜length new_pages = (page_size_multiplier sz - k)%nat ∧ ∀ (i : nat) (p' : page), new_pages !! i = Some p' → page_loc p' = self offset{usize}ₗ (k + i) * page_size_in_words_nat sz_smaller ∧ page_sz p' = sz_smaller⌝)%I as "Hx"; first last.
    { iIntros "Hit".
      iPoseProof ("Hx" $! 0%nat with "Hit") as "Ha".
      rewrite Nat.sub_0_r.
      simpl. iDestruct "Ha" as "(% & %Hb)".
      iPureIntro. split; first done. intros ? ? Hlook. eapply Hb in Hlook.
      rewrite Z.add_0_l in Hlook. done. }

    iInduction new_pages as [ | pg1 new_pages] "IH"; simpl.
    - rep liRStep. liShow. iPureIntro.
      rewrite Nat.sub_diag.
      split; first done. done.
    - rep liRStep. liShow.
      iRename select (IteratorNextFusedTrans _ _ _ _ _) into "Hnext".
      case_bool_decide; simplify_eq.
      iPoseProof ("IH" $! (k + 1%nat)%nat) as "IH'".
      rewrite Nat2Z.inj_add. iPoseProof ("IH'" with "Hnext") as "(-> & %IH)".
      iPureIntro. split; first lia.
      intros [ | i] p'; simpl; intros Hlook.
      { injection Hlook as <-. simpl. rewrite Z.add_0_r.
        split; last done.
        rewrite /offset_loc. simpl.
        rewrite /page_size_in_bytes_Z /page_size_in_bytes_nat.
        rewrite bytes_per_int_usize. f_equiv. lia. }
      replace (k + S i) with (k + 1%nat + i) by lia.
      apply IH; done. }

  rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - set (smaller_sz := (default self0 (page_size_smaller self0))).
    specialize (page_size_in_words_nat_ge smaller_sz).
    solve_goal.
  - set (smaller_sz := (default self0 (page_size_smaller self0))).
    unfold page_size_in_bytes_Z.
    specialize (page_size_in_bytes_nat_ge smaller_sz).
    solve_goal.
  - set (smaller_sz := (default self0 (page_size_smaller self0))).
    rewrite (page_size_multiplier_quot_Z _ smaller_sz); last done.
    specialize (page_size_multiplier_in_usize self0). solve_goal.
  - set (smaller_sz := (default self0 (page_size_smaller self0))).
    rewrite (page_size_multiplier_quot_Z _ smaller_sz); last done.
    specialize (page_size_multiplier_in_usize self0). solve_goal.

  Unshelve. all: print_remaining_sidecond.
Admitted. (* admitted due to admit_proofs config flag *)
End proof.

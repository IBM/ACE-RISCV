From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_merge.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* Opening element invariants temporarily must retain a way to restore the
   original vector before its drop glue runs. *)
Lemma borrow_array_element_invariants {X Y : RT} (P : ex_inv_def X Y)
    (ty : type X) π (ys : list Y) (vs : list val) :
  ([∗ list] y; v ∈ ys; vs, array_own_el_val π (∃; P, ty) (#y) v) -∗
  ∃ xs, ([∗ list] x; y ∈ xs; ys, P.(inv_P) π x y) ∗
    (([∗ list] x; y ∈ xs; ys, P.(inv_P) π x y) -∗
     [∗ list] y; v ∈ ys; vs, array_own_el_val π (∃; P, ty) (#y) v).
Proof.
  iIntros "H". iInduction ys as [|y ys] "IH" forall (vs); destruct vs as [|v vs]; simpl.
  - iExists []. simpl. auto.
  - done.
  - done.
  - iDestruct "H" as "(Hv & Hvs)".
    iDestruct "Hv" as "(%y' & <- & Hv)".
    iEval (rewrite ex_plain_t_unfold_val) in "Hv".
    iDestruct "Hv" as "(%x & HP & Hv)".
    iDestruct ("IH" with "Hvs") as "(%xs & HPs & Hclose)".
    iExists (x :: xs). simpl. iFrame "HP HPs".
    iIntros "(HP & HPs)". iSplitL "HP Hv".
    { iExists y. iR. rewrite ex_plain_t_unfold_val. iExists x. iFrame. }
    iApply "Hclose". done.
Qed.

Lemma borrow_array_invariants {X Y : RT} (P : ex_inv_def X Y)
    (ty : type X) π (ys : list Y) l F :
  lftE ⊆ F →
  l ◁ₗ[π, Owned] #(<#> ys) @ ◁ array_t (length ys) (∃; P, ty) ={F}=∗
  ∃ xs, ([∗ list] x; y ∈ xs; ys, P.(inv_P) π x y) ∗
    (([∗ list] x; y ∈ xs; ys, P.(inv_P) π x y) ={F}=∗
     l ◁ₗ[π, Owned] #(<#> ys) @ ◁ array_t (length ys) (∃; P, ty)).
Proof.
  iIntros (?) "Hl".
  iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hl".
  iDestruct "Hl" as "(%ly & %Hst & %Hly & #Hsc & #Hlb & %rs & <- & Hl)".
  iMod (fupd_mask_mono with "Hl") as "(%v & Hl & Hv)"; first done.
  iEval (rewrite /ty_own_val /= array_t_own_val_unfold) in "Hv".
  iDestruct "Hv" as "(%ely & %Hm & %Hest & %Hsz & %Hlen & %Hvl & Hv)".
  iEval (rewrite big_sepL2_fmap_l) in "Hv".
  iDestruct (borrow_array_element_invariants with "Hv") as "(%xs & HP & Hclose)".
  iExists xs. iFrame "HP". iModIntro. iIntros "HP".
  iModIntro. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
  iExists ly. iFrame "#%". iExists _. iR.
  iModIntro. iExists v. iFrame "Hl".
  rewrite /ty_own_val /= array_t_own_val_unfold.
  iExists ely. iFrame "%". rewrite big_sepL2_fmap_l. iApply "Hclose". done.
Qed.

Lemma borrow_vec_invariants {X Y A : RT} (P : ex_inv_def X Y)
    (ty : type X) (aty : type A) attrs π (ys : list Y) l F :
  lftE ⊆ F →
  (£ 1 : iProp Σ) -∗
  l ◁ₗ[π, Owned] #(<#> ys) @ ◁ (Vec_inv_t Y A attrs -[] -[(∃; P, ty); aty]) ={F}=∗
  ∃ xs, ([∗ list] x; y ∈ xs; ys, P.(inv_P) π x y) ∗
    (([∗ list] x; y ∈ xs; ys, P.(inv_P) π x y) ={F}=∗
     l ◁ₗ[π, Owned] #(<#> ys) @ ◁ (Vec_inv_t Y A attrs -[] -[(∃; P, ty); aty])).
Proof.
  iIntros (?) "Hc Hl".
  iMod (vec_access_elems with "Hc Hl") as "(%le & He & Hvec)"; first done.
  iMod (borrow_array_invariants with "He") as "(%xs & HP & Harray)"; first done.
  iExists xs. iFrame "HP". iModIntro. iIntros "HP".
  iMod ("Harray" with "HP") as "He".
  iApply ("Hvec" with "[//] [//] He").
Qed.

Lemma borrow_page_token_invariant `{!onceG Σ memory_layout} `{!MachineConfig}
    {S_rt : RT} (S_attrs : core_page_allocator_page_PageState_spec_attrs S_rt)
    (S_ty : type S_rt) π inner pg :
  (core_page_allocator_page_Page_inv_t_inv_spec S_rt S_attrs -[] -[S_ty]).(inv_P) π inner pg -∗
  ▷ (⌜page_wf pg⌝ ∗ ⌜pg.(page_loc).(loc_p) = ProvAlloc machine_memory_prov⌝ ∗
     (pg.(page_loc) ◁ₗ[π, Owned] #(<#> pg.(page_val)) @ ◁ array_t (page_size_in_words_nat pg.(page_sz)) (int usize)) ∗
     ((pg.(page_loc) ◁ₗ[π, Owned] #(<#> pg.(page_val)) @ ◁ array_t (page_size_in_words_nat pg.(page_sz)) (int usize)) -∗
      (core_page_allocator_page_Page_inv_t_inv_spec S_rt S_attrs -[] -[S_ty]).(inv_P) π inner pg)).
Proof.
  simpl. iIntros "(%MEM & %Heq & Hpg & %Hwf & %Hbounds & #Honce & %Hstart & %Hend & %Hprov & _)".
  rewrite /guarded. iDestruct "Hpg" as "(Hcreds & Hpg)".
  iNext. iFrame "% Hpg". iIntros "Hpg".
  iExists MEM. iFrame "#%". rewrite /guarded. iFrame "Hcreds". by iNext.
Qed.

Lemma borrow_page_token_invariants `{!onceG Σ memory_layout} `{!MachineConfig}
    {S_rt : RT} (S_attrs : core_page_allocator_page_PageState_spec_attrs S_rt)
    (S_ty : type S_rt) π xs xs' F :
  (£ 1 : iProp Σ) -∗
  ([∗ list] x; pg ∈ xs'; xs, (core_page_allocator_page_Page_inv_t_inv_spec S_rt S_attrs -[] -[S_ty]).(inv_P) π x pg) ={F}=∗
  ⌜Forall page_wf xs⌝ ∗
  ([∗ list] pg ∈ xs, ⌜pg.(page_loc).(loc_p) = ProvAlloc machine_memory_prov⌝ ∗
    pg.(page_loc) ◁ₗ[π, Owned] #(<#> pg.(page_val)) @ ◁ array_t (page_size_in_words_nat pg.(page_sz)) (int usize)) ∗
  (([∗ list] pg ∈ xs, pg.(page_loc) ◁ₗ[π, Owned] #(<#> pg.(page_val)) @ ◁ array_t (page_size_in_words_nat pg.(page_sz)) (int usize)) -∗
   [∗ list] x; pg ∈ xs'; xs, (core_page_allocator_page_Page_inv_t_inv_spec S_rt S_attrs -[] -[S_ty]).(inv_P) π x pg).
Proof.
  iIntros "Hc HP".
  iAssert (▷ (⌜Forall page_wf xs⌝ ∗
    ([∗ list] pg ∈ xs, ⌜pg.(page_loc).(loc_p) = ProvAlloc machine_memory_prov⌝ ∗
      pg.(page_loc) ◁ₗ[π, Owned] #(<#> pg.(page_val)) @ ◁ array_t (page_size_in_words_nat pg.(page_sz)) (int usize)) ∗
    (([∗ list] pg ∈ xs, pg.(page_loc) ◁ₗ[π, Owned] #(<#> pg.(page_val)) @ ◁ array_t (page_size_in_words_nat pg.(page_sz)) (int usize)) -∗
     [∗ list] x; pg ∈ xs'; xs, (core_page_allocator_page_Page_inv_t_inv_spec S_rt S_attrs -[] -[S_ty]).(inv_P) π x pg)))%I with "[HP]" as "HP".
  { iInduction xs' as [|x xs'] "IH" forall (xs); destruct xs as [|pg xs]; simpl.
    - iNext. iSplit; first by iPureIntro; constructor. auto.
    - done.
    - done.
    - iDestruct "HP" as "(HP & HPs)".
      iPoseProof (borrow_page_token_invariant with "HP") as "HP".
      iPoseProof ("IH" with "HPs") as "HPs".
      iNext. iDestruct "HP" as "(%Hwf & %Hprov & Harr & Hclose)".
      iDestruct "HPs" as "(%Hwfs & Harrs & Hcloses)".
      iSplit. { iPureIntro. by constructor. }
      iSplitL "Harr Harrs". { iFrame. done. }
      iIntros "(Harr & Harrs)". iSplitL "Harr Hclose".
      + by iApply "Hclose".
      + by iApply "Hcloses". }
  iApply (lc_fupd_add_later with "Hc"). by iNext.
Qed.

(* !start proof(page.merge) *)
Lemma borrow_owned_invariant {X Y : RT} (P : ex_inv_def X Y)
    (ty : type X) π y l F :
  lftE ⊆ F →
  l ◁ₗ[π, Owned] #y @ ◁ (∃; P, ty) ={F}=∗
  ∃ x, P.(inv_P) π x y ∗
    (P.(inv_P) π x y ={F}=∗ l ◁ₗ[π, Owned] #y @ ◁ (∃; P, ty)).
Proof.
  iIntros (?) "Hl".
  iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hl".
  iDestruct "Hl" as "(%ly & %Hst & %Hly & #Hsc & #Hlb & %r & <- & Hl)".
  iMod (fupd_mask_mono with "Hl") as "(%v & Hl & Hv)"; first done.
  iEval (rewrite ex_plain_t_unfold_val) in "Hv".
  iDestruct "Hv" as "(%x & HP & Hv)".
  iExists x. iFrame "HP". iModIntro. iIntros "HP".
  iModIntro. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
  iExists ly. iFrame "#%". iExists _. iR.
  iModIntro. iExists v. iFrame "Hl".
  rewrite ex_plain_t_unfold_val. iExists x. iFrame.
Qed.

Lemma reshape_uniform_join {A : Type} (xs : list (list A)) n :
  Forall (λ x, length x = n) xs →
  reshape (replicate (length xs) n) (mjoin xs) = xs.
Proof.
  induction 1 as [|x xs Hlen Hxs IH]; first done.
  cbn [length replicate reshape mjoin list_join].
  rewrite -Hlen take_app_length drop_app_length Hlen IH. done.
Qed.

Lemma page_ghost_drop_array `{!onceG Σ memory_layout} `{!MachineConfig}
    {S_rt : RT} (S_attrs : core_page_allocator_page_PageState_spec_attrs S_rt)
    (S_ty : type S_rt) π pg :
  ty_ghost_drop (core_page_allocator_page_Page_inv_t S_rt S_attrs -[] -[S_ty]) π pg -∗
  pg.(page_loc) ◁ₗ[π, Owned] #(<#> pg.(page_val)) @ ◁ array_t (page_size_in_words_nat pg.(page_sz)) (int usize).
Proof.
  rewrite ty_ghost_drop_unfold /=.
  iIntros "(%inner & (%MEM & % & Harr & _) & _)". done.
Qed.
(* !end proof *)

Lemma core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_merge_proof (π : thread_id) :
  core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_merge_lemma π.
Proof.
  core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_merge_prelude.

  rep <-! liRStep; liShow.
  (* !start proof(page.merge) *)
  2: { exfalso. shelve_sidecond. }
  opose proof (lookup_lt_is_Some_2 from_pages (length from_pages - 1) _) as [pg_last Hlook_pg_last].
  { lia. }
  destruct pg_last as [pg_loc_last pg_sz_last pg_val_last].
  opose proof (page_size_multiplier_ge new_size) as ?.
  opose proof (lookup_lt_is_Some_2 from_pages 0%nat _) as [pg_0 Hlook_pg0].
  { lia. }
  destruct pg_0 as [pg_loc_0 pg_sz_0 pg_val_0].
  rep <-! liRStep; liShow.
  2-5: rep liRStep; liShow.
  all: try match goal with
  | Hzero : page_size_in_words_nat ?sz = 0%nat |- _ =>
      exfalso; specialize (page_size_in_words_nat_ge sz); lia
  | Hunaligned : ¬ _ `aligned_to` page_size_in_bytes_nat _ |- _ =>
      exfalso; apply Hunaligned; rewrite -page_size_align_is_size; done
  end.

  iRename select (arg_from_pages ◁ₗ[π, Owned] _ @ _)%I into "Hvec".
  iApply updateable_add_fupd.
  iAcquireCredit as "Hcred".
  iMod (borrow_vec_invariants with "Hcred Hvec") as "(%xs' & Hinv & Hrestore_vec)"; first done.
  iAcquireCredit as "Hcred".
  iMod (borrow_page_token_invariants with "Hcred Hinv") as "(%Hpages_wf & Harrs & Hrestore_pages)".
  iDestruct (big_sepL_sep with "Harrs") as "(Hprovs & Harrs)".
  iDestruct (big_sepL_pure with "Hprovs") as "%Hprovs".
  have Hsz0 : pg_sz_0 = smaller_sz by apply Hlook in Hlook_pg0 as [??].
  have Hprov0 : loc_p pg_loc_0 = ProvAlloc machine_memory_prov.
  { exact (Hprovs _ _ Hlook_pg0). }
  have Hlayout : ∀ (i : nat) pg, from_pages !! i = Some pg →
    page_sz pg = pg_sz_0 ∧
    page_loc pg = (pg_loc_0 offsetst{IntSynType usize}ₗ (i * page_size_in_words_nat pg_sz_0)).
  { intros i pg Hpg. specialize (Hprovs _ _ Hpg) as Hprov.
    apply Hlook in Hpg as [Hsz Hloc]. split; first congruence.
    rewrite (list_lookup_total_correct _ _ _ Hlook_pg0) /= in Hloc.
    rewrite Hsz -Hsz0 in Hloc.
    destruct (page_loc pg), pg_loc_0; simpl in *.
    rewrite /OffsetLocSt /offset_loc /use_layout_alg' /= /shift_loc.
    erewrite syn_type_has_layout_int; last done.
    simpl. rewrite /page_size_in_bytes_nat bytes_per_int_usize.
    rewrite /page_size_in_bytes_nat in Hloc.
    f_equal; congruence || nia. }
  have Hmerged_size : page_size_in_words_nat new_size =
    (length from_pages * page_size_in_words_nat pg_sz_0)%nat.
  { rewrite Hlen Hsz0 (page_size_multiplier_size_in_words _ smaller_sz); last by rewrite Hsmaller.
    apply Nat.mul_comm. }
  have Hchunks_len : Forall (λ vs : list (place_rfn ZRT), length vs = page_size_in_words_nat pg_sz_0)
    ((λ pg, <#> page_val pg) <$> from_pages).
  { apply Forall_fmap. apply Forall_lookup. intros i pg Hpg.
    apply (Forall_lookup_1 _ _ _ _ Hpages_wf) in Hpg as Hwf.
    destruct (Hlayout _ _ Hpg) as [Hsz _].
    rewrite /compose length_fmap -Hsz. exact (eq_sym (proj1 Hwf)). }
  have Hmerge_bound : (size_of_st (IntSynType usize) * page_size_in_words_nat pg_sz_0 *
    length from_pages ≤ MaxInt ISize)%Z.
  { rewrite /size_of_st /use_layout_alg'. erewrite syn_type_has_layout_int; last done.
    simpl. rewrite bytes_per_int_usize.
    specialize (page_size_in_bytes_nat_in_isize new_size) as [_ Hsz].
    rewrite /page_size_in_bytes_nat Hmerged_size in Hsz. lia. }

  iMod (array_t_ofty_merge_big_sep (int usize) π _ (page_size_in_words_nat pg_sz_0) ((λ p, <#> p.(page_val)) <$> from_pages) (pg_loc_0) with "[Harrs]") as "Harr"; first done.
  { rewrite length_fmap. lia. }
  { rewrite length_fmap. exact Hmerge_bound. }
  { rewrite big_sepL_fmap. iApply (big_sepL_impl with "Harrs").
    iModIntro. iIntros (i pg Hpg) "Hb".
    destruct (Hlayout _ _ Hpg) as [Hsz Hloc]. rewrite Hsz Hloc. done. }
  repeat iClear select (page_loc (from_pages !!! Z.to_nat 0) ◁ₗ[ π, Shared _] _ @ _)%I.
  iModIntro.
  rep liRStep; liShow.
  rewrite (list_lookup_total_correct _ 0 _ Hlook_pg0). simpl.
  rep liRStep; liShow.
  liInst Hevar_x0 (mjoin (page_val <$> from_pages)).
  rep <-! liRStep; liShow.

  (* Return the memory temporarily to the source tokens for vector drop. *)
  iRename select (local___0 ◁ₗ[π, Owned] _ @ _)%I into "Hresult".
  iApply updateable_add_fupd.
  iMod (borrow_owned_invariant with "Hresult") as "(%result_inner & Hresult_inv & Hrestore_result)"; first done.
  iPoseProof (borrow_page_token_invariant with "Hresult_inv") as "Hresult_inv".
  iAcquireCredit as "Hcred".
  iMod (lc_fupd_elim_later with "Hcred Hresult_inv") as "(_ & _ & Harr & Hrestore_result_inv)".
  simpl.
  iEval (rewrite Hmerged_size list_fmap_mjoin -!list_fmap_compose) in "Harr".
  iMod (array_t_ofty_split_reshape _ _ _ _ (length from_pages) (page_size_in_words_nat smaller_sz) with "Harr") as "Harrs"; [done | done |].
  iEval (rewrite -(length_fmap (λ pg : page, <#> page_val pg) from_pages)
    (reshape_uniform_join _ _ Hchunks_len) big_sepL_fmap) in "Harrs".
  iAssert ([∗ list] pg ∈ from_pages, page_loc pg ◁ₗ[π, Owned] #(<#> page_val pg) @ ◁ array_t (page_size_in_words_nat (page_sz pg)) (int usize))%I with "[Harrs]" as "Harrs".
  { iApply (big_sepL_impl with "Harrs"). iModIntro. iIntros (i pg Hpg) "Harr".
    destruct (Hlayout _ _ Hpg) as [Hsz Hloc]. rewrite Hsz Hloc. done. }
  iPoseProof ("Hrestore_pages" with "Harrs") as "Hinv".
  iMod ("Hrestore_vec" with "Hinv") as "Hvec".
  iModIntro.
  rep <-! liRStep; liShow.

  (* Drop returns the page memories through the element ghost-drop predicates. *)
  iClear "Hprovs".
  iRename select (big_sepL _ _)%I into "Hdrop".
  iApply updateable_add_fupd.
  iEval (rewrite big_sepL_fmap) in "Hdrop".
  iMod (array_t_ofty_merge_big_sep (int usize) π _ (page_size_in_words_nat smaller_sz)
    ((λ pg, <#> page_val pg) <$> from_pages) r' with "[Hdrop]") as "Harr".
  { done. }
  { rewrite length_fmap. lia. }
  { rewrite length_fmap. exact Hmerge_bound. }
  { rewrite big_sepL_fmap. iApply (big_sepL_impl with "Hdrop").
    iModIntro. iIntros (i pg Hpg) "(%pg' & <- & Hpg)".
    iPoseProof (page_ghost_drop_array with "Hpg") as "Harr".
    destruct (Hlayout _ _ Hpg) as [Hsz Hloc]. rewrite Hsz Hloc. done. }
  iEval (rewrite length_fmap -Hmerged_size) in "Harr".
  iAssert (r' ◁ₗ[π, Owned] #(<#> mjoin (page_val <$> from_pages)) @ ◁ array_t (page_size_in_words_nat new_size) (int usize))%I with "[Harr]" as "Harr".
  { rewrite list_fmap_mjoin -!list_fmap_compose. done. }
  iPoseProof ("Hrestore_result_inv" with "Harr") as "Hinv".
  iMod ("Hrestore_result" with "Hinv") as "Hresult".
  iModIntro.
  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - rewrite Hlen. specialize (page_size_multiplier_ge new_size). lia.
  - rewrite page_size_multiplier_quot_Z; first solve_goal.
    rewrite Hsmaller.
    erewrite list_lookup_total_correct; last done.
    apply Hlook in Hlook_pg0 as [-> _]. done.
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
  - rename select (¬ MinInt usize ≤ _ ≤ MaxInt usize) into Hoverflow.
    apply Hoverflow. split; first solve_goal.
    opose proof (Hlook (length from_pages - 1)%nat _) as [Hlast_sz Hlast_off]; first done.
    simpl in *.
    rename select (loc_a pg_loc_last + _ ≤ MaxInt USize) into Hbound.
    move: Hbound. rewrite Hlast_off Hlen.
    rewrite (page_size_multiplier_size_in_bytes new_size smaller_sz); last by rewrite Hsmaller.
    simpl. rewrite Hlast_sz. clear. nia.
  - revert select (_ `quot` _ ≠ length from_pages).
    rewrite page_size_multiplier_quot_Z; first solve_goal.
    rewrite Hsmaller.
    erewrite list_lookup_total_correct; last done.
    apply Hlook in Hlook_pg0 as [-> _]. done.
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
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Admitted. (* admitted due to long Qed *)
End proof.

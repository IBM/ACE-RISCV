From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageStorageTreeNode_store_page_token.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma page_storage_node_invariant_case_store_token sz base state children max_alloc opt_page new_state new_max_alloc (i : nat) child child' child_alloc child_alloc' :
  children !! i = Some child →
  page_node_can_allocate child = child_alloc →
  page_node_can_allocate child' = Some child_alloc' →
  child_alloc ≤o{option_cmp page_size_cmp} (Some child_alloc') →
  child_alloc' <ₚ sz →
  new_max_alloc = max_by (option_cmp page_size_cmp) (Some child_alloc') max_alloc →
  new_state = (PageTokenPartiallyAvailable child_alloc') ⊔ state →
  page_storage_node_invariant_case (mk_page_node sz base state true) max_alloc opt_page children →
  page_storage_node_invariant_case (mk_page_node sz base new_state true) new_max_alloc opt_page (<[i := child']> children).
Proof.
  intros Hlook Halloc Halloc' Halloc_lt Hlt -> ->.
  specialize (lookup_lt_Some _ _ _ Hlook) as ?.

  unfold page_storage_node_invariant_case; simpl.
  destruct state as [ | | available_sz]; simpl.
  - normalize_and_simpl_goal.
    eexists _.
    split_and!; try done.
    exists i, child'.
    solve_goal.
  - normalize_and_simpl_goal.
    eexists. split_and!; try done.
    apply max_by_r. apply not_ord_gt_iff.
    left. by apply Z.cmp_less_iff.
  - intros (-> & (allocable_sz & [= <-] & -> & ? & _ & Ha)).
    split; first done.
    destruct (decide (available_sz ≤ₚ child_alloc')) as [Hlt' | Hnlt].
    + (* the available size changes *)
      exists child_alloc'. split_and!; try done.
      { unfold join; simpl. f_equiv.
        apply page_size_max_l. done. }
      { apply max_by_l.
        apply not_ord_lt_iff.
        done. }
      { exists i, child'.
        rewrite list_lookup_insert_eq; last lia.
        done. }
    + (* no change *)
      apply not_ord_le_iff in Hnlt.
      exists available_sz. split_and!; try done.
      { unfold join; simpl. f_equiv.
        apply page_size_max_r. by left. }
      { apply max_by_r.
        apply not_ord_gt_iff.
        by left. }
      { (* need some monotonicity: at i, the size increases *)
        destruct Ha as (j & child_max & Hlook' & Halloc1).
        exists j, child_max. split; last done.
        enough (i ≠ j). { rewrite list_lookup_insert_ne; done. }
        intros <-.
        simplify_eq.
        move: Hnlt Halloc_lt.
        rewrite Halloc1.
        intros Hnlt Halloc_le.
        opose proof (ord_lt_ord_le_trans _ _ _ Hnlt Halloc_le) as Ha.
        by apply ord_lt_irrefl in Ha. }
Qed.

Lemma node_allocation_state_join_partially_available_l st st' sz' :
  st' = PageTokenPartiallyAvailable sz' ⊔ st →
  (st = PageTokenUnavailable ∧ st' = PageTokenPartiallyAvailable sz') ∨
  (∃ sz, st = PageTokenPartiallyAvailable sz ∧ st' = PageTokenPartiallyAvailable (sz' ⊔ sz)) ∨
  (st = PageTokenAvailable ∧ st' = PageTokenAvailable).
Proof.
  unfold join, node_allocation_state_join.
  destruct st as [ | | sz]; simpl; naive_solver.
Qed.
Lemma available_sz_lower_bound node max_sz tok children updated_node_state allocable_sz_rec stored_sz merged_available_sz tok' children' :
  page_storage_node_invariant_case node max_sz tok children →
  page_storage_node_invariant_case (mk_page_node node.(max_node_size) node.(base_address) updated_node_state node.(children_initialized)) (Some merged_available_sz) tok' children' →
  (updated_node_state = (PageTokenPartiallyAvailable allocable_sz_rec ⊔ allocation_state node) ∨ updated_node_state = PageTokenAvailable) →
  stored_sz <ₚ max_node_size node →
  stored_sz ≤ₚ allocable_sz_rec →
  stored_sz ≤ₚ merged_available_sz ∧ (page_node_can_allocate node) ≤o{option_cmp page_size_cmp} Some merged_available_sz.
Proof.
  intros Hinv1 Hinv2 Hupd ? ?.
  destruct Hupd as [Hupd%node_allocation_state_join_partially_available_l | ->]; first last.
  { apply page_storage_node_invariant_case_available_inv in Hinv2 as (tok'' & -> & [= ->] & ? & ?); last done.
    split; first by left.
    erewrite page_storage_node_invariant_case_can_allocate; last done.
    by eapply page_node_invariant_case_sized_bounded. }
  destruct Hupd as [[Heq1 Heq2] | [Ha | [? ->]]].
  - eapply page_storage_node_invariant_case_partially_available_inv in Hinv2 as [[= ->] ->]; last done.
    split; first done.
    opose proof (page_storage_node_invariant_case_unavailable_inv _ _ _ _ _  Hinv1) as [-> ->]; first done.
    erewrite page_storage_node_invariant_case_can_allocate; last done.
    by left.
  - destruct Ha as (sz & Hst & ->).
    eapply page_storage_node_invariant_case_partially_available_inv in Hinv2 as [[= ->] ->]; last done.
    split. { by etrans; last apply page_size_max_ge_l. }
    erewrite page_storage_node_invariant_case_can_allocate; last done.
    eapply page_storage_node_invariant_case_partially_available_inv in Hinv1 as [[= ?] ->]; last done.
    subst. eapply page_size_max_ge_r.
  -  apply page_storage_node_invariant_case_available_inv in Hinv2 as (tok'' & -> & [= ->] & ? & ?); last done.
    split; first by left.
    erewrite page_storage_node_invariant_case_can_allocate; last done.
    by eapply page_node_invariant_case_sized_bounded.
Qed.

Lemma core_page_allocator_allocator_PageStorageTreeNode_store_page_token_proof (π : thread_id) :
  core_page_allocator_allocator_PageStorageTreeNode_store_page_token_lemma π.
Proof.
  core_page_allocator_allocator_PageStorageTreeNode_store_page_token_prelude.

  rep liRStep; liShow.
  2: repeat liRStep.
  3: repeat liRStep.
  1: liInst Hevar self; rep liRStep; liShow.
  1: liInst Hevar (mk_page_node self.(max_node_size) self.(base_address) PageTokenAvailable self.(children_initialized)); rep liRStep.
  (* there is a smaller page size *)
  rep <-! liRStep.
  2: repeat liRStep.
  rep liRStep.
  liInst Hevar (mk_page_node self.(max_node_size) self.(base_address) self.(allocation_state) true).
  rep <-! liRStep.
  match goal with
  | H : page_node_can_allocate _ = Some ?a |- _ =>
      rename a into allocable_sz_rec
  end.
  set (new_state := (PageTokenPartiallyAvailable allocable_sz_rec) ⊔ self.(allocation_state)).

  repeat liRStep. liShow.
  liInst Hevar (mk_page_node self.(max_node_size) self.(base_address) new_state true).
  repeat liRStep.
  liInst Hevar (mk_page_node (max_node_size self) (base_address self) x'1 true).
  rename x'1 into updated_node_state.
  repeat liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: try lia.

  all: try match goal with
    | H : page_storage_node_children_wf _ _ ?x,
      H2: page_storage_node_invariant_case (mk_page_node _ _ _ _) _ _ ?x,
      H3: length ?x = page_size_multiplier _ |- _ =>
          rename x into children;
          rename H2 into INV_CASE2;
          rename H into INV_WF2;
          rename H3 into INV_INIT_CHILDREN2
    end.
  all: try rename x' into child_index.
  all: try set (child := children !!! Z.to_nat child_index).
  all: try match goal with
    | H : page_size_smaller (max_node_size _) = Some ?x |- _ =>
        rename x into child_size; rename H into Hsmaller
    end.
  all: try match goal with
    | H : ?x = PageTokenPartiallyAvailable _ ∨ ?x = PageTokenAvailable,
      H1 : page_storage_node_invariant_case (mk_page_node _ _ ?x _) _ _ _ |- _ =>
        rename x into merged_state;
        rename H1 into INV_CASE_MERGED;
        rename H into Hmerged
    end.

  - apply page_within_range_inv in Hrange; simpl in Hrange; done.
  - destruct Hsz_le as [Hsz_lt | Hsz_eq%Z.ord_eq_iff].
    + apply Z.ord_lt_iff in Hsz_lt. move: Hsz_lt. lia.
    + apply page_size_variant_inj in Hsz_eq. done.
  - eexists. done.
  - done.
  - move: INV_CASE.
    unfold page_storage_node_invariant_case.
    solve_goal.
  - eexists. done.
  - done.
  - done.
  - erewrite page_storage_node_invariant_case_can_allocate; last done.
    by eapply page_node_invariant_case_sized_bounded.
  - rename select (_ ∨_) into Hsz.
    destruct Hsz as [Hsz | <-]; last done.
    unfold ord_le, ord_lt, ord_eq.
    move: Hsz.
    unfold page_size_cmp.
    match goal with
    | H: page_size_variant _ = page_size_variant (max_node_size self) - 1 |- _ => rewrite H
    end.
    clear.
    solve_goal.
  - rewrite -page_size_align_is_size.
    eexists. done.
  - rename select (_ ∨_) into Hsz.
    destruct Hsz as [Hsz | <-]; last done.
    move: Hsz.
    rename select (max_node_size self = _) into Hsz. rewrite Hsz.
    destruct page_token0; done.
  - eexists. done.
  - done.
  - destruct INV_WF2 as [INV_WF1 INV_WF2].
    odestruct (INV_WF1 _ _ (Z.to_nat child_index) child _) as [Ha Hb].
    { done. }
    { assert (Z.to_nat child_index < length children); last solve_goal.
      rewrite INV_INIT_CHILDREN2.
      specialize (page_size_multiplier_ge (max_node_size self)); lia. }
    rewrite Hb.
    unfold child_base_address.
    lia.
  - destruct INV_WF2 as [INV_WF1 INV_WF2].
    odestruct (INV_WF1 _ _ (Z.to_nat child_index) child _) as [Ha Hb].
    { done. }
    { assert (Z.to_nat child_index < length children); last solve_goal.
      rewrite INV_INIT_CHILDREN2.
      specialize (page_size_multiplier_ge (max_node_size self)); lia. }
    done.
  - opose proof (list_lookup_lookup_total_lt children (Z.to_nat child_index) _) as Hlook_child.
    { lia. }
    fold child in Hlook_child.
    opose proof (page_storage_node_children_wf_child_lookup _ _ _ _ children _ _ _ _) as Hchild; [ | done | apply Hlook_child | ]; first done.
    destruct Hchild as [-> _].
    apply Z.ord_le_iff.
    move: Hsz_le. unfold ord_le.
    normalize_and_simpl_goal.
    lia.
  - match goal with
    | H: page_within_range (base_address self + _) _ _ |- _ => rename H into Hran
    end.
    move: Hran.
    unfold child_base_address.
    rewrite Z.mul_comm.
    done.
  - eapply page_storage_node_children_wf_insert; last done.
    all: done.
  - eexists _. done.
  - opose proof (list_lookup_lookup_total_lt children (Z.to_nat child_index) _) as Hlook_child.
    { lia. }
    fold child in Hlook_child.
    eapply page_storage_node_invariant_case_store_token; [ .. | done ].
    { apply Hlook_child. }
    { reflexivity. }
    { done. }
    { done. }
    { eapply (ord_le_ord_lt_trans _ (max_node_size child)); first last.
      - opose proof (page_storage_node_children_wf_child_lookup _ _ _ _ _ _ _ _ Hlook_child) as (Ha & _); [done.. | ].
        rewrite Ha.
        by apply page_size_smaller_lt.
      - done. }
    { clear. symmetry. case_bool_decide as Ha.
      - eapply max_by_l.
        apply not_ord_lt_iff. left. done.
      - eapply max_by_r. apply not_ord_gt_iff.
        move: Ha.
        destruct (option_cmp page_size_cmp _ (Some allocable_sz_rec)) eqn:Heq; first done.
        + right. done.
        + left. by apply correct_ord_antisym. }
    { done. }
  - match goal with
    | H : ?x = new_state ∨ ?x = PageTokenAvailable |- _ =>
        rename x into new_state';
        rename H into Hnew_state'
    end.
    exfalso. move: Hnew_state'.
    rename select (page_storage_node_invariant_case (mk_page_node _ _ new_state' _) _ _ _) into Hcase'.
    apply page_storage_node_invariant_not_available in Hcase' as [Ha ->].
    simpl in Ha. rewrite Ha. subst new_state.
    clear. intros [? | ?]; last done.
    destruct (allocation_state self); done.
  - eexists. done.
  - done.
  - (* did a merge, now it's available *)
    match goal with
    | H : page_storage_node_invariant_case _ (Some ?p') _ _ |- _ =>
        rename H into Hcase_merged;
        rename p into merged_available_sz
    end.
    eapply available_sz_lower_bound.
    + apply INV_CASE.
    + apply Hcase_merged.
    + done.
    + simpl.
      move: Hsz_le. unfold ord_le. normalize_and_simpl_goal.
    + solve_goal.
  - match goal with
    | H : page_storage_node_invariant_case _ (Some ?p') _ _ |- _ =>
        rename H into Hcase_merged;
        rename p into merged_available_sz
    end.
    match goal with
    | H : updated_node_state = new_state ∨ _ |- _ =>
        rename H into Hmerged
    end.
    by eapply page_storage_node_invariant_case_can_allocate.
  - (* same as above *)
    match goal with
    | H : page_storage_node_invariant_case _ (Some ?p') _ _ |- _ =>
        rename H into Hcase_merged;
        rename p into merged_available_sz
    end.
    eapply available_sz_lower_bound.
    + apply INV_CASE.
    + apply Hcase_merged.
    + done.
    + simpl. move: Hsz_le. unfold ord_le. normalize_and_simpl_goal.
    + solve_goal.
  - match goal with
    | H : page_storage_node_invariant_case _ (Some ?p') _ _ |- _ =>
        rename H into Hcase_merged;
        rename p into merged_available_sz
    end.
    opose proof (available_sz_lower_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) as Ha.
    + apply INV_CASE.
    + apply Hcase_merged.
    + done.
    + simpl. move: Hsz_le. unfold ord_le. normalize_and_simpl_goal.
    + solve_goal.
    + destruct Ha as [_ Ha]. apply Ha.
  - match goal with
    | H : page_storage_node_invariant_case _ (Some ?p') _ _ |- _ =>
        rename H into Hcase_merged;
        rename p into merged_available_sz
    end.
    opose proof (page_node_invariant_case_sized_bounded _ _ _ _ _) as Ha.
    { apply Hcase_merged. }
    done.

  Unshelve. all: print_remaining_sidecond.
(*Qed.*)
Admitted. (* admitted due to long Qed *)
End proof.

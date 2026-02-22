From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* !start proof(page_allocator.acquire_page_token) *)
Lemma update_allocation_state_inv self new_state max_alloc max_allocs children child_size :
  max_allocs = fmap page_node_can_allocate children →
  max_alloc = max_list_cmp (option_cmp page_size_cmp) max_allocs None →
  new_state = match max_alloc ≫= id with
  | Some max => PageTokenPartiallyAvailable max
  | None => PageTokenUnavailable
  end →
  page_size_smaller (max_node_size self)  = Some child_size →
  page_storage_node_children_wf (base_address self) (max_node_size self) children →
  page_storage_node_invariant_case
  {|
    max_node_size := max_node_size self;
    base_address := base_address self;
    allocation_state := new_state;
    children_initialized := true
  |} (max_alloc ≫= id) None children.
Proof.
  intros Hmax Hmaxs -> Hsmaller Hchildren.
  destruct (max_alloc ≫= id) as [max_alloc' | ] eqn:Heq; simpl.
  - apply bind_Some in Heq as (? & -> & Heq). simpl in Heq. subst.
    unfold page_storage_node_invariant_case; simpl.
    destruct (max_list_cmp_elem_of (cmp:=option_cmp page_size_cmp) (page_node_can_allocate <$> children) None) as [Hdef | Hel]; first congruence.
    destruct Hel as (ps & Hmax & Hel).
    apply list_elem_of_fmap in Hel as (child & -> & Hel).
    rewrite Hmax in Hmaxs. simplify_eq.
    apply list_elem_of_lookup_1 in Hel as (child_index & Hlook).

    opose proof* (page_storage_node_children_wf_child_lookup child_index) as (Hchild_sz & Hchild_base & Hbound); [done.. | ].
    split; first done.
    eexists.
    split_and!; try done.
    + rewrite -Hmaxs in Hbound. move: Hbound.
      normalize_and_simpl_impl false. intros Hbound.
      apply page_size_smaller_lt in Hsmaller.
      eapply ord_le_ord_lt_trans; done.
    + naive_solver.
  - apply bind_None in Heq.
    unfold page_storage_node_invariant_case; simpl.
    done.
Qed.

Lemma node_partially_available_exists_child node available_sz tok children sz :
  node.(allocation_state) ≠ PageTokenAvailable →
  node.(allocation_state) ≥o{node_allocation_state_cmp} PageTokenPartiallyAvailable sz →
  page_storage_node_invariant_case node available_sz tok children →
  ∃ child_index child,
    children !! child_index = Some child ∧
    Some sz ≤o{option_cmp page_size_cmp} page_node_can_allocate child.
Proof.
  intros Hnot_avail Havail.
  unfold page_storage_node_invariant_case.
  repeat case_decide.
  - intros [-> ->].
    rename select (allocation_state node = _) into Hstate.
    rewrite Hstate in Havail.
    exfalso. move: Havail.
    unfold ord_ge. solve_goal.
  - done.
  - intros [-> (alloca & Halloca & -> & ? & ? & Hchild)].
    rewrite Halloca in Havail.
    destruct Hchild as (i & child & Hchild & Halloc).
    exists i, child. split; first done.
    rewrite Halloc. move: Havail.
    unfold ord_ge, ord_le. solve_goal.
Qed.
(* !end proof *)

Lemma core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_proof (π : thread_id) :
  core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_lemma π.
Proof.
  core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_prelude.

  repeat liRStep; liShow.
  (* !start proof(page_allocator.acquire_page_token) *)
  { liInst Hevar_rf self. repeat liRStep; liShow. }
  2: { liInst Hevar_rf self. repeat liRStep; liShow. }

  liInst Hevar_rf self.
  rep <-! liRStep.

  set (position_pred := λ node, ((Some page_size_to_acquire) ≤o{ option_cmp page_size_cmp } page_node_can_allocate node)).
  rep 10 liRStep; liShow.
  rep 20 liRStep; liShow.
  unfold map_inv_ty. (* TODO *)
  rep liRStep; liShow.
  liInst Hevar_x0 (λ _ _ clos_state, (⌜clos_state = -[page_size_to_acquire]⌝ ∗ True)%I).
  liInst Hevar_x2 position_pred.

  rep <-! liRStep.
  2: repeat liRStep.
  2: repeat liRStep.

  match goal with
  | H : page_size_smaller (max_node_size self) = Some ?x |- _ =>
      rename x into child_size;
      rename H into Hsmaller
  end.
  rep <-! liRStep. liShow.

  set (nodes := (<[Z.to_nat z:=x'2]> (x' ++ e :: x'1))).
  set (max_allocs := ((λ p, page_node_can_allocate p.1) <$> zip nodes (replicate (length x' + S (length x'1)) ()))).
  set (max_alloc := max_list_cmp (option_cmp page_size_cmp) max_allocs None).
  set (new_state := match max_alloc ≫= id with | Some max => PageTokenPartiallyAvailable max | None => PageTokenUnavailable end).
  repeat liRStep.
  liInst Hevar_rf (mk_page_node self.(max_node_size) self.(base_address) new_state true).

  repeat liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer_normalize.
  all: clear_layout; clear_unused_vars.
  all: try lia.
  all: try match goal with
    | H : page_size_smaller (max_node_size _) = Some ?x |- _ =>
      rename x into smaller_size;
      rename H into Hsmaller
    end.
  all: try rename select (max_node_size self ≠ page_size_to_acquire) into Hlt_self.
  all: try rename x' into children_without_alloc.
  all: try rename e into allocable_node.
  all: try set (children_new := (children_without_alloc ++ allocable_node :: x'1)).
  all: try rename select (page_node_can_allocate allocable_node = Some _) into Hallocable_node.
  all: try match type of Hallocable_node with page_node_can_allocate _ = Some ?y => rename y into allocable_size end.
  all: try rename select (length children_without_alloc = Z.to_nat _) into Hpos.
  all: try match type of Hpos with _ = Z.to_nat ?z => rename z into pos end.
  all: try rename select (Forall _ children_without_alloc) into Hnot_found.

  -
    opose proof* (page_storage_node_invariant_no_tok) as [Ha ?]; first apply INV_CASE.
    rename select (_ ∨ _) into Hle.
    destruct Hle as [(max_sz' & -> & Hlt)| Heq].
    + move: Ha. normalize_and_simpl_goal.
      assert(max_sz' <o{page_size_cmp} max_sz') as Hlt'.
      { etrans; done. }
      eapply ord_lt_irrefl in Hlt'.
      done.
    + subst max_sz. apply ord_lt_irrefl in Ha. done.
 - (* we can allocate at least page_size_to_acquire (from partial comp),
      but the size to acquire is not equal to max_node_size, which is the smallest.
       contradiction. *)
    opose proof* page_node_invariant_case_sized_bounded as Hbound; first apply INV_CASE.
    move: Hbound.
    rename select (_ ∨ _) into Hsz_acquire_bound.
    rename select (max_node_size self = Size4KiB) into Heq.
    rewrite Heq.
    (* TODO factor into lemma *)
    destruct Hsz_acquire_bound as [Hlt | Heq'].
    + destruct Hlt as (sz & -> & Hlt).
      normalize_and_simpl_impl false.
      intros Hle.
      opose proof* (ord_lt_ord_le_trans (A:=page_size)) as Hlt2; first apply Hlt; first apply Hle.
      move: Hlt2. clear.
      destruct page_size_to_acquire; done.
    + rewrite Heq'.
      normalize_and_simpl_impl false.
      rewrite Heq in Hlt_self.
      intros [Hlt | Heq''].
      * clear -Hlt. by destruct page_size_to_acquire.
      * move: Heq''. normalize_and_simpl_impl false. done.
  - eexists. done.
  - apply page_storage_node_invariant_has_token in INV_CASE as (-> & _). done.
  - opose proof (page_storage_node_invariant_has_token _ _ _ _ INV_CASE) as (Hstate & Hsz & Haddr).
    simpl in Hsz, Haddr. subst.
    exists (max_node_size self). split; last reflexivity.
    unfold page_node_can_allocate. by rewrite Hstate.
  - eexists. done.
  - by eapply (page_node_invariant_case_can_allocate_bounded (mk_page_node _ _ _ _)).
  - intros (sz & Halloc & Hlb).
    opose proof (page_storage_node_invariant_case_can_allocate _ _ _ _ INV_CASE).
    subst max_sz.
    repeat revert select (¬ _).
    rewrite Halloc.
    intros Hneq Hnlt.
    destruct Hlb as [Hlt | Heq].
    + apply Hnlt.
      solve_goal.
    + apply Hneq.
      move: Heq. solve_goal.
  - eexists. done.
  - (* should prove that at z there is a child (by position_pred e). Then follows from invariant on children *)
    odestruct (lookup_lt_is_Some_2 children_new (Z.to_nat pos) _) as (child & Hlook_child).
    { rewrite length_app/=. lia. }
    erewrite list_lookup_total_correct; last done.
    opose proof (page_storage_node_children_wf_child_lookup (Z.to_nat pos) _ _ _ children_new _ _ _ _) as (? & Heq & _).
    { apply Hsmaller. }
    { done. }
    { done. }
    rewrite Heq. f_equiv. lia.
  - (* ditto *)
    odestruct (lookup_lt_is_Some_2 children_new (Z.to_nat pos) _) as (child & Hlook_child).
    { rewrite length_app/=. lia. }
    erewrite list_lookup_total_correct; last done.
    opose proof (page_storage_node_children_wf_child_lookup (Z.to_nat pos) _ _ _ children_new _ _ _ _) as (Heq & ?).
    { apply Hsmaller. }
    { done. }
    { done. }
    rewrite Heq. done.
  - eauto.
  - (* ditto; similar as above *)
    exfalso. rename select (¬ ∃ sz : page_size, _) into Hcontra. apply Hcontra.
    rewrite lookup_total_app_r; last lia.
    rewrite -Hpos. solve_goal.
  - (* contradiction: Forall (¬ position_pred), but we can allocate *)
    (* max_sz is at least page_size_to_acquire, but page_size_to_acquire is less then max_node_size self.

       Thus, self ≥ PageTokenPartiallyAvailable page_size_to_acquire.

       x' are the new children after initializing if necessary and dividing.

       new_state ≥ PageTokenPartiallyAvailable page_size_to_acquire.
       Thus, there exists a child satisfying position_pred.
    *)
    exfalso.
    opose proof* (page_storage_node_invariant_case_can_allocate) as Heq.
    { apply INV_CASE. }
    subst max_sz.

    rename select (page_storage_node_invariant_case _ _ _ children_without_alloc) into INV_CASE'.
    opose proof (node_partially_available_exists_child _ _ _ _ page_size_to_acquire _ _ INV_CASE') as (child_index & child & Hchild & Hchild_alloc).
    { simpl. destruct (allocation_state self); done. }
    { simpl. eapply ord_le_antisym.
      rename select (_ ∨ _) into Hsz_acquire_bound.
      eapply node_allocation_state_meet_le_lub.
      - apply page_node_can_allocate_lb.
        destruct Hsz_acquire_bound as [(sz & Halloc & Hlt)| Halloc].
        + rewrite Halloc. normalize_and_simpl_goal. by left.
        + rewrite Halloc. solve_goal.
      - normalize_and_simpl_goal.
        enough (page_size_to_acquire <ₚ max_node_size self) by lia.
        opose proof* page_node_invariant_case_sized_bounded as Hbound; first apply INV_CASE.
        move: Hbound.
        destruct Hsz_acquire_bound as [Hlt | Heq].
        + move: Hlt. intros (sz & -> & Hlt).
          normalize_and_simpl_goal.
          by eapply ord_lt_ord_le_trans.
        + rewrite Heq.
          normalize_and_simpl_impl false.
          intros [Hlt | Heq']; first done.
          move: Heq'. normalize_and_simpl_goal. }
    opose proof* (Forall_lookup_1) as Hpos.
    { apply Hnot_found. }
    { apply Hchild. }
    simpl in Hpos. apply Hpos. unfold position_pred.
    done.
  - apply page_storage_node_children_wf_insert; done.
  - rename select (page_storage_node_invariant_case _ _ _ (children_without_alloc ++ _)) into INV_CASE2.
    opose proof* page_storage_node_invariant_case_at_most_partially_available_inv as [Hle_sz ->]; [ | apply INV_CASE2 | ].
    { simpl. apply node_allocation_state_meet_le_r. }
    eapply update_allocation_state_inv.
    { done. }
    { subst max_alloc. f_equiv.
      rewrite /max_allocs.
      etrans. { eapply (list_fmap_ext _ (page_node_can_allocate ∘ fst)). intros ? []; done. }
      rewrite list_fmap_compose fst_zip; first done.
      rewrite /nodes. solve_goal. }
    { done. }
    { done. }
    { done. }
  - by eapply (page_node_invariant_case_can_allocate_bounded (mk_page_node _ _ _ _)).
  - rename select (_ ∨ _) into Hsz_acquire_bound.
    opose proof* page_storage_node_invariant_case_can_allocate as Halloc; first apply INV_CASE.
    move: Hsz_acquire_bound.
    rewrite Halloc.
    solve_goal.
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Admitted. (* admitted due to long Qed *)
End proof.

From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageStorageTreeNode_divide_page_token_if_necessary.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma divide_page_token_neutral node sz children smaller_size :
  page_size_smaller node.(max_node_size) = Some smaller_size →
  page_storage_node_invariant_case node sz None children →
  node.(allocation_state) ⊓ PageTokenPartiallyAvailable smaller_size = node.(allocation_state).
Proof.
  intros Hsmaller.
  unfold page_storage_node_invariant_case.
  destruct (allocation_state node) eqn:Heq; simpl.
  - done.
  - naive_solver.
  - intros [_ (? & [= <-] & -> & Hlt & ? & ?)].
    cbn. rewrite page_size_min_l; first done.
    apply page_size_smaller_page_size_variant in Hsmaller.
    apply Z.ord_lt_iff in Hlt.
    apply Z.ord_le_iff.  lia.
Qed.

Lemma core_page_allocator_allocator_PageStorageTreeNode_divide_page_token_if_necessary_proof (π : thread_id) :
  core_page_allocator_allocator_PageStorageTreeNode_divide_page_token_if_necessary_lemma π.
Proof.
  core_page_allocator_allocator_PageStorageTreeNode_divide_page_token_if_necessary_prelude.

  repeat liRStep.
  1: liInst Hevar (mk_page_node self.(max_node_size) self.(base_address) (PageTokenPartiallyAvailable smaller_size) true).
  2: liInst Hevar self.
  all: repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: try lia.
  all: try rename select (subdivided_pages _ _) into Hsubdivided.

  all: try match type of Hsubdivided with
      | subdivided_pages _ (?pref ++ (mk_page _ _ _) :: ?suff) =>
          rename pref into prefix;
          rename suff into suffix
      end.
  all: try (opose proof (page_storage_node_invariant_has_token _ _ _ _ INV_CASE) as Ha; simpl in Ha; destruct Ha as (? & <- & ?)).
  all: match type of INV_WF with page_storage_node_children_wf _ _ ?c => rename c into children end.
  all: rename select (children_initialized self = true) into Hchildren.
  all: rewrite Hchildren in INV_INIT_CHILDREN.
  all: try rename x'3 into child_index.


  - right.
    opose proof (subdivided_pages_lookup_size_lt (length prefix) _ _ _ _ _ Hsubdivided _) as Ha.
    { simpl. done. }
    { rewrite lookup_app.
      rewrite lookup_ge_None_2; last lia.
      solve_goal. }
    solve_goal.
  - opose proof (subdivided_pages_lookup_size_lt (length prefix) _ _ _ _ _ Hsubdivided _) as Ha.
    { simpl. done. }
    { rewrite lookup_app.
      rewrite lookup_ge_None_2; last lia.
      solve_goal. }
    simpl in Ha. subst.
    eapply (subdivided_pages_page_within_range' (length prefix)); solve_goal.
  - rewrite INV_INIT_CHILDREN.
    apply subdivided_pages_length in Hsubdivided.
    solve_goal.
  - (* point: prove length prefix = child_index *)
    rename select (page_within_range _ _ _) into Hrange.

    opose proof (subdivided_pages_lookup_size_lt (length prefix) _ _ _ _ _ Hsubdivided _) as Hsz.
    { done. }
    { rewrite lookup_app_r; last lia. rewrite Nat.sub_diag. done. }
    simpl in Hsz. subst.

    opose proof (subdivided_pages_lookup_inv _ _ _ _ _ (length prefix) _ _ Hsubdivided _ _ _ Hrange) as Heq; [solve_goal.. | ].
    assert (child_index = Z.of_nat (length prefix)) as -> by lia.

    odestruct (lookup_lt_is_Some_2 children (length prefix) _) as (child & Hchild).
    { lia. }
    opose proof (page_storage_node_children_wf_child_lookup (length prefix) _ _ _ _ _ _ INV_WF Hchild) as [Hchild_sz Hchild_loc].
    { done. }

    apply page_within_range_inv in Hrange; last done.
    simpl in Hrange.

    rewrite lookup_total_app_r; first last.
    { solve_goal. }
    normalize_and_simpl_goal.
    erewrite list_lookup_total_correct; last apply Hchild.
    done.
  - rename select (page_within_range _ _ _) into Hrange.

    opose proof (subdivided_pages_lookup_size_lt (length prefix) _ _ _ _ _ Hsubdivided _) as Hsz.
    { done. }
    { rewrite lookup_app_r; last lia. rewrite Nat.sub_diag. done. }
    simpl in Hsz. subst.

    opose proof (subdivided_pages_lookup_inv _ _ _ _ _ (length prefix) _ _ Hsubdivided _ _ _ Hrange) as Heq; [solve_goal.. | ].
    assert (child_index = Z.of_nat (length prefix)) as -> by lia.

    odestruct (lookup_lt_is_Some_2 children (length prefix) _) as (child & Hchild).
    { rewrite INV_INIT_CHILDREN. lia. }
    opose proof (page_storage_node_children_wf_child_lookup (length prefix) _ _ _ _ _ _ INV_WF Hchild) as [Hchild_sz Hchild_loc].
    { done. }

    opose proof (subdivided_pages_lookup_base_address (length prefix) _ _ _ _ _ Hsubdivided _) as Hloc.
    { done. }
    { rewrite lookup_app_r; last lia. rewrite Nat.sub_diag. done. }


    rewrite lookup_total_app_r; first last.
    { solve_goal. }
    normalize_and_simpl_goal.
    erewrite list_lookup_total_correct; last apply Hchild.

    rewrite Hchild_loc.
    simpl in Hloc. rewrite Hloc.
    rewrite /child_base_address. lia.
  - apply subdivided_pages_length in Hsubdivided.
    solve_goal.
  - rename select (page_within_range _ _ _) into Hrange.

    opose proof (subdivided_pages_lookup_size_lt (length prefix) _ _ _ _ _ Hsubdivided _) as Hsz.
    { done. }
    { rewrite lookup_app_r; last lia. rewrite Nat.sub_diag. done. }
    simpl in Hsz. subst.

    opose proof (subdivided_pages_lookup_inv _ _ _ _ _ (length prefix) _ _ Hsubdivided _ _ _ Hrange) as Heq; [solve_goal.. | ].
    assert (child_index = Z.of_nat (length prefix)) as -> by lia.

    rewrite lookup_total_app_r; first last.
    { solve_goal. }
    normalize_and_simpl_goal.
    + apply list_subequiv_split.
      { solve_goal. }
      normalize_and_simpl_goal.
      f_equiv. lia.
    + normalize_and_simpl_goal.
      odestruct (lookup_lt_is_Some_2 children (length prefix) _) as (node & ?); first lia.
      exists node. split; first done.
      erewrite list_lookup_total_correct; last done.
      destruct node; done.
  - rename select (max_node_size self = Size4KiB) into Hsz.
    rename select (page_size_smaller _ = Some _) into Hsmaller.
    move: Hsmaller. rewrite Hsz. done.
  - apply subdivided_pages_length in Hsubdivided. simpl in Hsubdivided. lia.
  - rewrite skipn_all2; last lia.
    rewrite app_nil_r.
    by apply page_storage_node_children_wf_upd_state.
  - eexists. done.
  - unfold name_hint. lia.
  - unfold name_hint.
    rewrite skipn_all2; last lia.
    rewrite app_nil_r.
    simplify_eq.

    rename select (allocation_state self = _) into Hstate.
    move: INV_CASE.
    unfold page_storage_node_invariant_case.
    rewrite Hstate. simpl.
    normalize_and_simpl_goal.
    eexists. split_and!; [done | done | | done | ].
    { apply Z.cmp_less_iff. lia. }
    setoid_rewrite list_lookup_fmap.
    opose proof (lookup_lt_is_Some_2 children 0%nat _) as (child & Hchild).
    { specialize (page_size_multiplier_ge (max_node_size self)). lia. }
    eexists 0%nat, (page_node_update_state child PageTokenAvailable).
    rewrite Hchild.
    split; first done.
    opose proof (page_storage_node_children_wf_child_lookup 0%nat _ _ _ _ _ _ INV_WF Hchild) as [Hchild_sz Hchild_loc].
    { done. }
    rewrite -Hchild_sz//.
  - rename select (allocation_state self = _) into Hstate.
    rewrite Hstate. done.
  - eexists. done.
  - solve_goal.
  - solve_goal.
  - erewrite divide_page_token_neutral; [ | done | done].
    destruct self as [? ? state ?].
    simpl. simpl in Hchildren. rewrite Hchildren//.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.



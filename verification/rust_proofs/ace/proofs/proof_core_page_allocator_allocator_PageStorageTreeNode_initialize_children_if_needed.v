From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageStorageTreeNode_initialize_children_if_needed.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageStorageTreeNode_initialize_children_if_needed_proof (π : thread_id) :
  core_page_allocator_allocator_PageStorageTreeNode_initialize_children_if_needed_lemma π.
Proof.
  core_page_allocator_allocator_PageStorageTreeNode_initialize_children_if_needed_prelude.

  rep <-! liRStep; liShow.
  (* !start proof(page_allocator.initialize_children_if_needed) *)
  { rep liRStep; liShow.
    (* pick map invariant *)
    liInst Hevar_Inv (λ π '(i, b) _, ⌜i ≤ page_size_multiplier self.(max_node_size)⌝ ∗ ⌜b = Z.of_nat $ page_size_multiplier self.(max_node_size)⌝)%I.
    (* instantiation of the params of PageNode::empty *)
    liInst Hevar_ParamPred (λ i '( *[p1; p2]),
      let '( *[i]) := i in
      p1 = child_base_address (base_address self) smaller_sz i ∧ p2 = smaller_sz).
    rep liRStep; liShow.
    liInst Hevar_rf (mk_page_node self.(max_node_size) self.(base_address) self.(allocation_state) true).
    rep liRStep; liShow.
  }
  { rep liRStep.
    liInst Hevar_rf self.
    rep liRStep.
  }
  (* !end proof *)

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  (* !start proof(page_allocator.initialize_children_if_needed) *)
  all: try rename select (Forall2 _ _ _) into Hf.
  - rewrite /number_of_smaller_pages Hsmaller. lia.
  - unfold child_base_address.
    apply Z.divide_add_r.
    + trans (page_size_align (max_node_size self)).
      2: by eexists.
      rewrite (page_size_multiplier_align (max_node_size self) smaller_sz); last done.
      rewrite Nat2Z.inj_mul.
      apply Z.divide_factor_l.
    + rewrite page_size_align_is_size.
      apply Z.divide_factor_l.
  - move: INV_IN_RANGE.
    opose proof (page_size_multiplier_size_in_bytes (max_node_size self) _ _) as ->.
    { rewrite Hsmaller//. }
    unfold child_base_address. nia.
  - case_bool_decide; simplify_eq. lia.
  - rewrite snd_zip; first last.
    { opose proof* Forall2_length as Hlen; first apply Hf. lia. }
    split; first last.
    { rewrite Hsmaller. done. }
    intros child_sz Hsmaller' i child Hlook.
    opose proof * Forall2_lookup_r as Hlook'; [apply Hf | apply Hlook | ].
    destruct Hlook' as (idx & Hlook_idx & idx' & -> & Haddr & ?).
    apply lookup_seqZ in Hlook_idx as (-> & ?).
    simpl.
    split_and!.
    + simplify_eq. done.
    + simplify_eq. done.
    + subst. solve_goal.
  - eexists. done.
  - opose proof* Forall2_length as Hlen; first apply Hf.
    rewrite -Hlen.
    rewrite length_seqZ.
    rewrite /number_of_smaller_pages Hsmaller.
    lia.
  - (* reasoning:
       if children were empty before, then either there is no smaller page size or we are not in PartiallyAvailable state. So this is trivial *)
    rewrite snd_zip; first last.
    { opose proof* Forall2_length as Hlen; first apply Hf. lia. }
    move: INV_CASE.
    unfold page_storage_node_invariant_case.
    simpl. repeat case_decide; try done.
    all: solve_goal.
  - eexists. done.
  - destruct self as [??? children_init]. simpl in *.
    destruct children_init; done.
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

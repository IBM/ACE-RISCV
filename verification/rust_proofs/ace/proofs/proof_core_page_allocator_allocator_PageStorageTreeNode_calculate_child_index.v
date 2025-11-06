From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageStorageTreeNode_calculate_child_index.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma rem_le_a_minus_b a b z :
  0 ≤ b →
  0 < a →
  Z.divide b a →
  Z.divide b z →
  a - b >= z mod a.
Proof.
  intros ? Ha [n Hmul_a] [m Hmul_z].
  subst a z.
  (* rewrite the modulus of multiples: (b*m) mod (b*n) = b * (m mod n) *)
  rewrite Zmult_mod_distr_r.

  opose proof (Z.mod_pos_bound m n _) as Hbound; first lia.
  destruct Hbound as [Hge Hlt].      (* 0 <= m mod n < n *)

  (* multiply the inequality chain by b *)
  assert (0 <= b * (m mod n)) by (apply Z.mul_nonneg_nonneg; lia).
  assert (b * (m mod n) <= b * (n - 1)).
  { apply Z.mul_le_mono_nonneg_l; try lia. }

  (* conclude: b * (m mod n) <= b*n - b *)
  replace (b * (n - 1)) with (b*n - b) in * by lia.
  lia.
Qed.

Lemma page_within_range_offset base off sz p child_sz :
  (page_size_in_bytes_Z (page_sz p) | (page_loc p).2) →
  (page_size_in_bytes_Z sz | base) →
  page_size_smaller sz = Some child_sz →
  p.(page_sz) ≤ₚ child_sz →
  off = ((p.(page_loc).2 - base) `quot` page_size_in_bytes_Z child_sz) * page_size_in_bytes_Z child_sz →
  page_within_range base sz p →
  page_within_range (base + off) child_sz p.
Proof.
  set (i := ((p.(page_loc).2 - base) `quot` page_size_in_bytes_Z child_sz)).
  intros Hal1 Hal2 Hsmaller Hle -> [Hran1 Hran2].
  split; first lia.

  assert (p.(page_loc).2 - base ≤ i * page_size_in_bytes_Z child_sz + Z.rem (p.(page_loc).2 - base) (page_size_in_bytes_Z child_sz)).
  { subst i.
    specialize (Z.quot_rem' ((page_loc p).2 - base) (page_size_in_bytes_Z child_sz)) as Heq.
    rewrite {1}Heq. lia. }
  enough (page_size_in_bytes_Z child_sz - page_size_in_bytes_Z (page_sz p) >= ((page_loc p).2 - base) `rem` page_size_in_bytes_Z child_sz) by lia.

  rewrite Z.rem_mod_nonneg; [ | lia | ]; first last.
  { specialize (page_size_in_bytes_nat_ge child_sz). lia. }
  apply rem_le_a_minus_b.
  - lia.
  - specialize (page_size_in_bytes_nat_ge child_sz). lia.
  - by apply page_size_in_bytes_nat_le_divide.
  - apply Z.divide_sub_r.
    + done.
    + etrans; last apply Hal2.
      apply page_size_in_bytes_nat_le_divide.
      etrans; first done.
      left. by apply page_size_smaller_lt.
Qed.

Lemma core_page_allocator_allocator_PageStorageTreeNode_calculate_child_index_proof (π : thread_id) :
  core_page_allocator_allocator_PageStorageTreeNode_calculate_child_index_lemma π.
Proof.
  core_page_allocator_allocator_PageStorageTreeNode_calculate_child_index_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { move: Hrange; unfold page_within_range. solve_goal. }
  { move: Hrange; unfold page_within_range; solve_goal. }
  { simplify_eq. specialize (page_size_in_words_nat_ge child_node_sz). sidecond_hammer. }
  { simplify_eq. specialize (page_size_in_words_nat_ge child_node_sz). sidecond_hammer. }
  { (* compute the index *)
    simplify_eq.
    etrans; last apply Z.quot_pos; first done; first lia.
    specialize (page_size_in_bytes_nat_ge child_node_sz).
    lia. }
  { simplify_eq.
    specialize (page_size_in_bytes_nat_ge child_node_sz) as ?.
    apply Z.quot_le_upper_bound; first lia.
    nia. }
  { simplify_eq.
    specialize (page_size_in_bytes_nat_ge child_node_sz) as ?.
    apply Z.quot_lt_upper_bound; [lia | lia | ].
    opose proof (page_size_multiplier_size_in_bytes this_node_page_size child_node_sz _) as  Ha.
    { by rewrite Hchild. }
    rewrite -Nat2Z.inj_mul. rewrite -Ha.

    destruct Hrange as [Hran1 Hran2].
    move: Hran2. simpl.
    specialize (page_size_in_bytes_nat_ge page_token0).
    lia.
  }
  { simplify_eq.
    eapply page_within_range_offset; simpl; [ | | done..].
    - rewrite -page_size_align_is_size. done.
    - eexists. done. }
  { destruct Hsz_lt as [Hsz_lt |Hsz_eq].
    - apply Z.cmp_less_iff in Hsz_lt. lia.
    - apply Z.cmp_equal_iff in Hsz_eq. apply page_size_variant_inj in Hsz_eq.
      simplify_eq. lia. }

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

From refinedrust Require Import typing.

(* This reflects the page sizes in [core/mmu/page_size.rs] *)
Inductive page_size : Set :=
  | Size4KiB
  | Size16KiB
  | Size2MiB
  | Size1GiB
  | Size512GiB
  | Size128TiB.

Global Instance page_size_inh : Inhabited page_size.
Proof. exact (populate Size4KiB). Qed.
Global Instance page_size_eqdec : EqDecision page_size.
Proof. solve_decision. Defined.
Global Instance page_size_countable : Countable page_size.
Proof.
  (* TODO *)
Admitted.

Definition page_size_in_words_nat (sz : page_size) : nat :=
  match sz with
  | Size4KiB => 512
  | Size16KiB => 4 * 512
  | Size2MiB => 512 * 512
  | Size1GiB => 512 * 512 * 512
  | Size512GiB => 512 * 512 * 512 * 512
  | Size128TiB => 512 * 512 * 512 * 512 * 256
  end.

Definition page_size_in_bytes_nat (sz : page_size) : nat :=
  bytes_per_addr * page_size_in_words_nat sz.
Definition page_size_in_bytes_Z (sz : page_size) : Z :=
  page_size_in_bytes_nat sz.


Definition page_size_smaller (sz : page_size) : option page_size :=
  match sz with
  | Size4KiB => None
  | Size16KiB => Some Size4KiB
  | Size2MiB => Some Size16KiB
  | Size1GiB => Some Size2MiB
  | Size512GiB => Some Size1GiB
  | Size128TiB => Some Size512GiB
  end.
Definition page_size_larger (sz : page_size) : option page_size :=
  match sz with
  | Size4KiB => Some Size16KiB
  | Size16KiB => Some Size2MiB
  | Size2MiB => Some Size1GiB
  | Size1GiB => Some Size512GiB
  | Size512GiB => Some Size128TiB
  | Size128TiB => None
  end.

(* Pages should be aligned to the size of the page *)
Definition page_size_align_log (sz : page_size) : nat :=
  match sz with
  | Size4KiB => 12
  | Size16KiB => 14
  | Size2MiB => 21
  | Size1GiB => 30
  | Size512GiB => 39
  | Size128TiB => 47
  end.
Definition page_size_align (sz : page_size) : nat :=
  2^(page_size_align_log sz).

Lemma page_size_align_is_size sz :
  (page_size_align sz = page_size_in_bytes_nat sz)%nat.
Proof.
  rewrite /page_size_align/page_size_in_bytes_nat/bytes_per_addr/bytes_per_addr_log.
  Local Arguments Nat.mul : simpl never.
  destruct sz; simpl; lia.
Qed.

Definition zero_page (sz : page_size) : list Z :=
  replicate (page_size_in_words_nat sz) 0.

Record page : Type := mk_page {
  page_loc : loc;
  page_sz : page_size;
  page_val : list Z
}.
Global Instance page_inh : Inhabited page.
Proof. exact (populate (mk_page inhabitant inhabitant inhabitant)). Qed.
Global Instance page_eqdec : EqDecision page.
Proof. solve_decision. Defined.
Global Instance page_countable : Countable page.
Proof.
  (* TODO *)
Admitted.

(** Well-formedness of a page *)
Definition page_wf (p : page) : Prop :=
  page_size_in_words_nat p.(page_sz) = length p.(page_val) ∧
  p.(page_loc) `aligned_to` page_size_align p.(page_sz).

(** The list of [pages] forms a contiguous region of memory, one page after another. *)
Fixpoint pages_are_contiguous (pages : list page) : Prop :=
  match pages with
  | [] => True
  | pg1 :: pgs =>
      match pgs with
      | [] => True
      | pg2 :: pgs' =>
          pages_are_contiguous pgs ∧
          pg1.(page_loc) +ₗ (page_size_in_bytes_Z pg1.(page_sz)) = pg2.(page_loc)
      end
  end.
Arguments pages_are_contiguous : simpl never.

Lemma pages_are_contiguous_cons p1 ps :
  pages_are_contiguous ps →
  (match head ps with | Some p2 => p2.(page_loc) = p1.(page_loc) +ₗ (page_size_in_bytes_nat p1.(page_sz)) | None => True end) →
  pages_are_contiguous (p1 :: ps).
Proof.
  intros Ha Hh.
  rewrite /pages_are_contiguous.
  destruct ps as [ | p2 ps]; first done.
  simpl in *. split; done.
Qed.


(* How many pages of the next smaller page size are there in this page size? *)
Definition page_size_multiplier_log (sz : page_size) : nat :=
  match sz with
  | Size4KiB => 0
  | Size16KiB => 2
  | Size2MiB => 7
  | Size1GiB => 9
  | Size512GiB => 9
  | Size128TiB => 8
  end.
Definition page_size_multiplier (sz : page_size) : nat :=
  2^(page_size_multiplier_log sz).

Lemma page_size_multiplier_size_in_words sz sz' :
  page_size_smaller sz = Some sz' →
  page_size_in_words_nat sz = (page_size_in_words_nat sz' * page_size_multiplier sz)%nat.
Proof.
  destruct sz; first done.
  all: unfold page_size_smaller; intros ?; simplify_eq.
  all: unfold page_size_in_words_nat, page_size_multiplier, page_size_multiplier_log.
  all: cbn [Nat.pow]; lia.
Qed.
Lemma page_size_multiplier_align_log sz sz' :
  page_size_smaller sz = Some sz' →
  page_size_align_log sz = (page_size_align_log sz' + page_size_multiplier_log sz)%nat.
Proof.
  destruct sz; first done.
  all: unfold page_size_smaller; intros ?; simplify_eq.
  all: unfold page_size_align_log, page_size_multiplier, page_size_multiplier_log.
  all: lia.
Qed.
Lemma page_size_multiplier_align sz sz' :
  page_size_smaller sz = Some sz' →
  page_size_align sz = (page_size_align sz' * page_size_multiplier sz)%nat.
Proof.
  intros Ha. rewrite /page_size_align /page_size_multiplier.
  rewrite -Nat.pow_add_r.
  f_equiv. by apply page_size_multiplier_align_log.
Qed.

(* Divide a page into pages of the next smaller page size *)
Definition subdivide_page (p : page) : list page :=
  match page_size_smaller p.(page_sz) with
  | None => [p]
  | Some smaller =>
      let count := page_size_multiplier p.(page_sz) in
      let sizes := replicate count (page_size_in_words_nat smaller) in
      let values := reshape sizes p.(page_val) in
      zip_with (λ value num,
        mk_page
          (p.(page_loc) +ₗ (page_size_in_bytes_nat smaller * num)%nat)
          smaller
          value
      ) values (seq 0 count)
  end.
Arguments subdivide_page : simpl never.

Lemma subdivide_page_length p :
  length (subdivide_page p) = page_size_multiplier p.(page_sz).
Proof.
  destruct p as [l sz vs].
  rewrite /subdivide_page/=.
  destruct (page_size_smaller sz) as [ sz' | ] eqn:Heq; simpl; first last.
  { destruct sz; done. }

  set (num := (page_size_multiplier sz)%nat).
  generalize num. clear Heq num.

  unfold page_size_in_bytes_nat. intros num.
  clear sz.
  set (start := 0%nat).
  set (words := page_size_in_words_nat sz').
  replace vs with (drop (start * words) vs); last done.
  generalize start. clear start => start.

  induction num as [ | num IH] in start |-*; first done.
  Local Arguments Nat.mul : simpl never. simpl. f_equiv.
  rewrite drop_drop.
  replace (start * words + words)%nat with ((S start) * words)%nat by lia.
  apply (IH (S start)).
Qed.

(* TODO move *)
Lemma aligned_to_mul_inv l al num :
  l `aligned_to` al * num →
  l `aligned_to` al.
Proof.
  rewrite /aligned_to.
  destruct caesium_config.enforce_alignment; last done.
  intros (k & Heq). intros. exists (k * num). lia.
Qed.

Lemma subdivide_page_wf p :
  page_wf p →
  Forall page_wf (subdivide_page p).
Proof.
  destruct p as [l sz vs].
  rewrite /subdivide_page/=.
  destruct (page_size_smaller sz) as [ sz' | ] eqn:Heq; simpl; first last.
  { econstructor; eauto. }

  specialize (page_size_multiplier_size_in_words _ _ Heq).
  specialize (page_size_multiplier_align _ _ Heq).
  set (num := (page_size_multiplier sz)%nat).
  rewrite /page_wf/= => -> ->.
  generalize num. clear Heq num sz.

  unfold page_size_in_bytes_nat. intros num.
  set (start := 0%nat).
  set (words := page_size_in_words_nat sz').
  replace vs with (drop (start * words) vs); last done.
  generalize start. clear start => start [] Hlen Hal.
  apply aligned_to_mul_inv in Hal.

  induction num as [ | num IH] in start, Hlen, Hal |-*; first done.
  Arguments Nat.mul : simpl never. simpl.
  econstructor.
  - simpl. split.
    { rewrite take_length -Hlen. lia. }
    { subst words. eapply aligned_to_offset; first done.
      rewrite page_size_align_is_size /page_size_in_bytes_nat.
      rewrite Nat2Z.divide. apply Nat.divide_factor_l. }
  - rewrite drop_drop.
    replace (start * words + words)%nat with ((S start) * words)%nat by lia.
    apply (IH (S start)); last done.
    rewrite Nat.mul_succ_l.
    rewrite -drop_drop drop_length -Hlen.
    lia.
Qed.

Lemma subdivide_page_is_contiguous p :
  pages_are_contiguous (subdivide_page p).
Proof.
  destruct p as [l sz vs].
  rewrite /subdivide_page/=.
  destruct (page_size_smaller sz) as [ sz' | ] eqn:Heq; simpl; last done.

  set (num := (page_size_multiplier sz)%nat).
  generalize num. clear Heq num.

  unfold page_size_in_bytes_nat. intros num.
  clear sz.

  set (start := 0%nat).
  set (words := page_size_in_words_nat sz').
  replace vs with (drop (start * words) vs); last done.
  generalize start. clear start => start.

  induction num as [ | num IH] in start |-*; first done.
  Arguments Nat.mul : simpl never. simpl.
  apply pages_are_contiguous_cons.
  - fold @replicate.
    rewrite drop_drop.
    replace (start * words + words)%nat with ((S start) * words)%nat by lia.
    apply (IH (S start)).
  - simpl.
    fold @replicate.
    destruct num; simpl; first done.
    rewrite shift_loc_assoc.
    f_equiv.
    rewrite /page_size_in_bytes_nat. lia.
Qed.

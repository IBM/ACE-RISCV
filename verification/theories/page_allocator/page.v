From refinedrust Require Import typing.
From rrstd.cmp.theories Require Import ordering.
From ace.theories.base Require Import base.

(** * Extra theories for page sizes and pages *)

(* This reflects the page sizes in [core/architecture/riscv/mmu/page_size.rs] *)
Inductive page_size : Set :=
  | Size4KiB
  | Size16KiB
  | Size2MiB
  | Size1GiB
  | Size512GiB
  | Size128TiB.
Canonical Structure page_sizeRT := directRT page_size.

Global Instance page_size_inh : Inhabited page_size.
Proof. exact (populate Size4KiB). Qed.
Global Instance page_size_eqdec : EqDecision page_size.
Proof. solve_decision. Defined.
Definition page_size_variant (a : page_size) : Z :=
  match a with
  | Size4KiB => 0
  | Size16KiB => 1
  | Size2MiB => 2
  | Size1GiB => 3
  | Size512GiB => 4
  | Size128TiB => 5
  end
.
Global Instance page_size_countable : Countable page_size.
Proof.
  refine (inj_countable (λ a, Z.to_nat (page_size_variant a))
    (λ a,
    match a with
    | 0 => Some Size4KiB
    | 1 => Some Size16KiB
    | 2 => Some Size2MiB
    | 3 => Some Size1GiB
    | 4 => Some Size512GiB
    | 5 => Some Size128TiB
    | _ => None
    end%nat) _).
  intros []; naive_solver.
Qed.

Global Instance page_size_variant_inj :
  Inj (=) (=) (page_size_variant).
Proof.
  intros sz1 sz2.
  destruct sz1, sz2; done.
Qed.

Definition page_size_cmp (a b : page_size) : ordering :=
  Z.cmp (page_size_variant a) (page_size_variant b).
Arguments page_size_cmp : simpl never.

Definition page_size_eq (a b : page_size) : bool :=
  bool_decide (a = b).

Global Instance page_size_eq_correct : CorrectEq page_size_eq.
Proof.
  unfold page_size_eq.
  econstructor.
  - intros ?. naive_solver.
  - intros ??. naive_solver.
  - intros ???. naive_solver.
Qed.
Global Instance page_size_cmp_correct : CorrectOrd page_size_eq page_size_cmp.
Proof.
  unfold page_size_eq, page_size_cmp.
  econstructor.
  - apply _.
  - intros ??. solve_goal.
  - intros ???. solve_goal.
  - intros ???. solve_goal.
  - solve_goal.
  - solve_goal.
Qed.

Notation "a '<ₚ' b" := (a <o{page_size_cmp} b) (at level 50).
Notation "a '=ₚ' b" := (a =o{page_size_cmp} b) (at level 50).
Notation "a '>ₚ' b" := (a >o{page_size_cmp} b) (at level 50).
Notation "a '≤ₚ' b" := (a ≤o{page_size_cmp} b) (at level 60).
Notation "a '≥ₚ' b" := (a ≥o{page_size_cmp} b) (at level 50).

Lemma page_size_le_max p :
  p ≤ₚ Size128TiB.
Proof.
  unfold ord_le.
  destruct p; last (by right); left.
  all: apply Z.cmp_less_iff.
  all: simpl; lia.
Qed.
Lemma page_size_le_min p :
  Size4KiB ≤ₚ p.
Proof.
  unfold ord_le.
  destruct p; first (by right); left.
  all: apply Z.cmp_less_iff.
  all: simpl; lia.
Qed.


(** Number of 64-bit machine words in a page size *)
Definition page_size_in_words_nat_def (sz : page_size) : nat :=
  match sz with
  | Size4KiB => 512
  | Size16KiB => 4 * 512
  | Size2MiB => 512 * 512
  | Size1GiB => 512 * 512 * 512
  | Size512GiB => 512 * 512 * 512 * 512
  | Size128TiB => 512 * 512 * 512 * 512 * 256
  end.
Definition page_size_in_words_nat_aux : seal (page_size_in_words_nat_def). Proof. by econstructor. Qed.
Definition page_size_in_words_nat := page_size_in_words_nat_aux.(unseal).
Definition page_size_in_words_nat_unfold : page_size_in_words_nat = page_size_in_words_nat_def := page_size_in_words_nat_aux.(seal_eq).

Definition page_size_in_bytes_nat (sz : page_size) : nat :=
  bytes_per_addr * page_size_in_words_nat sz.
Notation page_size_in_bytes_Z sz :=
  (Z.of_nat (page_size_in_bytes_nat sz)).

Lemma page_size_in_bytes_div_8 sz :
  (8 | page_size_in_bytes_nat sz).
Proof.
  unfold page_size_in_bytes_nat.
  exists (page_size_in_words_nat sz).
  rewrite bytes_per_addr_eq. lia.
Qed.
Lemma page_size_in_words_nat_ge sz :
  page_size_in_words_nat sz ≥ 512.
Proof.
  rewrite page_size_in_words_nat_unfold /page_size_in_words_nat_def.
  destruct sz; lia.
Qed.
Lemma page_size_in_bytes_nat_ge sz :
  page_size_in_bytes_nat sz ≥ 4096.
Proof.
  unfold page_size_in_bytes_nat.
  rewrite bytes_per_addr_eq.
  specialize (page_size_in_words_nat_ge sz).
  lia.
Qed.
Lemma page_size_in_bytes_nat_in_usize sz :
  (Z.of_nat $ page_size_in_bytes_nat sz) ∈ usize.
Proof.
  rewrite /page_size_in_bytes_nat page_size_in_words_nat_unfold /page_size_in_words_nat_def.
  rewrite bytes_per_addr_eq.
  split.
  all: unsafe_unfold_common_caesium_defs.
  all: unfold it_signed, it_byte_size_log, bytes_per_addr_log.
  all: destruct sz; try lia.
Qed.
Lemma page_size_in_bytes_Z_in_usize sz :
  (page_size_in_bytes_Z sz) ∈ usize.
Proof.
  apply page_size_in_bytes_nat_in_usize.
Qed.

Lemma page_size_in_words_nat_mono sz1 sz2 :
  page_size_variant sz1 < page_size_variant sz2 →
  page_size_in_words_nat sz1 < page_size_in_words_nat sz2.
Proof.
  rewrite page_size_in_words_nat_unfold /page_size_in_words_nat_def.
  unfold page_size_variant.
  destruct sz1, sz2; lia.
Qed.
Lemma page_size_in_bytes_nat_mono sz1 sz2 :
  page_size_variant sz1 < page_size_variant sz2 →
  page_size_in_bytes_nat sz1 < page_size_in_bytes_nat sz2.
Proof.
  unfold page_size_in_bytes_nat.
  intros ?%page_size_in_words_nat_mono.
  unfold bytes_per_addr.
  nia.
Qed.
Lemma page_size_in_bytes_Z_mono sz1 sz2 :
  page_size_variant sz1 < page_size_variant sz2 →
  page_size_in_bytes_Z sz1 < page_size_in_bytes_Z sz2.
Proof.
  unfold page_size_in_bytes_Z.
  intros ?%page_size_in_bytes_nat_mono.
  done.
Qed.

Lemma page_size_le_size_in_bytes sz1 sz2 :
  sz1 ≤ₚ sz2 →
  page_size_in_bytes_Z sz1 ≤ page_size_in_bytes_Z sz2.
Proof.
  intros [Hlt | Heq].
  - apply Z.cmp_less_iff in Hlt.
    apply page_size_in_bytes_Z_mono in Hlt. lia.
  - apply Z.cmp_equal_iff in Heq. apply page_size_variant_inj in Heq. subst.
    lia.
Qed.
Lemma page_size_in_words_nat_lt_divide sz1 sz2 :
  sz1 <ₚ sz2 →
  Nat.divide (page_size_in_words_nat sz1) (page_size_in_words_nat sz2).
Proof.
  intros Ha. apply Z.cmp_less_iff in Ha.
  unfold page_size_in_bytes_nat.
  destruct sz1, sz2; simpl in *; try lia.
  all: rewrite page_size_in_words_nat_unfold /page_size_in_words_nat_def.
  - exists 4%nat. lia.
  - exists 512%nat. lia.
  - exists (512 * 512)%nat. lia.
  - exists (512 * 512 * 512)%nat. lia.
  - exists (512 * 512 * 512 * 256)%nat. lia.
  - exists 128%nat. lia.
  - exists (128 * 512)%nat. lia.
  - exists (128 * 512 * 512)%nat. lia.
  - exists (64 * 512 * 512 * 512)%nat. lia.
  - exists 512%nat. lia.
  - exists (512 * 512)%nat. lia.
  - exists (512 * 512 * 256)%nat. lia.
  - exists (512)%nat. lia.
  - exists (512 * 256)%nat. lia.
  - exists (256)%nat. lia.
Qed.
Lemma page_size_in_words_nat_le_divide sz1 sz2 :
  sz1 ≤ₚ sz2 →
  Nat.divide (page_size_in_words_nat sz1) (page_size_in_words_nat sz2).
Proof.
  intros [Hlt | Heq].
  - by eapply page_size_in_words_nat_lt_divide.
  - apply Z.cmp_equal_iff in Heq.
    apply page_size_variant_inj in Heq as <-.
    done.
Qed.

Lemma page_size_in_bytes_nat_le_divide sz1 sz2 :
  sz1 ≤ₚ sz2 →
  Z.divide (page_size_in_bytes_Z sz1) (page_size_in_bytes_Z sz2).
Proof.
  intros Ha. unfold page_size_in_bytes_nat.
  apply (page_size_in_words_nat_le_divide) in Ha.
  apply Nat2Z.divide in Ha.
  rewrite !(Nat2Z.inj_mul bytes_per_addr).
  apply Z.mul_divide_mono_l.
  done.
Qed.

(** The next smaller page size *)
Definition page_size_smaller (sz : page_size) : option page_size :=
  match sz with
  | Size4KiB => None
  | Size16KiB => Some Size4KiB
  | Size2MiB => Some Size16KiB
  | Size1GiB => Some Size2MiB
  | Size512GiB => Some Size1GiB
  | Size128TiB => Some Size512GiB
  end.

Lemma page_size_smaller_None sz :
  page_size_smaller sz = None ↔ sz = Size4KiB.
Proof. destruct sz; done. Qed.
Lemma page_size_smaller_page_size_variant sz sz' :
  page_size_smaller sz = Some sz' →
  page_size_variant sz' = page_size_variant sz - 1.
Proof.
  destruct sz, sz'; simpl; naive_solver.
Qed.
Lemma page_size_smaller_lt sz sz' :
  page_size_smaller sz = Some sz' →
  sz' <ₚ sz.
Proof.
  intros Hsmaller.
  apply page_size_smaller_page_size_variant in Hsmaller.
  unfold ord_lt, page_size_cmp.
  apply Z.cmp_less_iff.
  lia.
Qed.

(** The next larger page size *)
Definition page_size_larger (sz : page_size) : option page_size :=
  match sz with
  | Size4KiB => Some Size16KiB
  | Size16KiB => Some Size2MiB
  | Size2MiB => Some Size1GiB
  | Size1GiB => Some Size512GiB
  | Size512GiB => Some Size128TiB
  | Size128TiB => None
  end.
Lemma page_size_larger_None sz :
  page_size_larger sz = None ↔ sz = Size128TiB.
Proof. destruct sz; done. Qed.
Lemma page_size_larger_page_size_variant sz sz' :
  page_size_larger sz = Some sz' →
  page_size_variant sz' = page_size_variant sz + 1.
Proof.
  destruct sz, sz'; simpl; naive_solver.
Qed.
Lemma page_size_larger_gt sz sz' :
  page_size_larger sz = Some sz' →
  sz' >ₚ sz.
Proof.
  intros Hlarger.
  apply page_size_larger_page_size_variant in Hlarger.
  unfold ord_gt, page_size_cmp.
  apply Z.cmp_greater_iff.
  lia.
Qed.

(** Pages should be aligned to the size of the page;
  compute the log2 of this page's alignment *)
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
  rewrite page_size_in_words_nat_unfold.
  Local Arguments Nat.mul : simpl never.
  destruct sz; simpl; lia.
Qed.

(** Join on page sizes (maximum) *)
Definition page_size_max (sz1 sz2 : page_size) : page_size :=
  match sz1, sz2 with
  | Size128TiB, _ => Size128TiB
  | _ , Size128TiB => Size128TiB
  | Size512GiB, _ => Size512GiB
  | _, Size512GiB => Size512GiB
  | Size1GiB, _ => Size1GiB
  | _, Size1GiB => Size1GiB
  | Size2MiB, _ => Size2MiB
  | _, Size2MiB => Size2MiB
  | Size16KiB, _ => Size16KiB
  | _, Size16KiB => Size16KiB
  | _, _ => Size4KiB
  end.
Global Instance page_size_join : Join page_size := page_size_max.

Lemma page_size_max_ge_l sz1 sz2 :
  sz1 ≤ₚ sz1 ⊔ sz2.
Proof.
  unfold ord_le.
  destruct sz1, sz2; cbn; naive_solver.
Qed.
Lemma page_size_max_ge_r sz1 sz2 :
  sz2 ≤ₚ sz1 ⊔ sz2.
Proof.
  unfold ord_le.
  destruct sz1, sz2; cbn; naive_solver.
Qed.
Lemma page_size_max_l sz1 sz2 :
  sz2 ≤ₚ sz1 → sz1 ⊔ sz2 = sz1.
Proof.
  intros [Hlt | Heq].
  - apply Z.cmp_less_iff in Hlt. destruct sz1, sz2; simpl in *; try done.
  - apply Z.cmp_equal_iff in Heq. destruct sz1, sz2; simpl; try done.
Qed.
Lemma page_size_max_r sz1 sz2 :
  sz1 ≤ₚ sz2 → sz1 ⊔ sz2 = sz2.
Proof.
  intros [Hlt | Heq].
  - apply Z.cmp_less_iff in Hlt. destruct sz1, sz2; simpl in *; try done.
  - apply Z.cmp_equal_iff in Heq. destruct sz1, sz2; simpl; try done.
Qed.

(** Meet on page sizes (minimum) *)
Definition page_size_min (sz1 sz2 : page_size) : page_size :=
  match sz1, sz2 with
  | Size4KiB, _ => Size4KiB
  | _, Size4KiB => Size4KiB
  | Size16KiB, _ => Size16KiB
  | _, Size16KiB => Size16KiB
  | Size2MiB, _ => Size2MiB
  | _, Size2MiB => Size2MiB
  | Size1GiB, _ => Size1GiB
  | _, Size1GiB => Size1GiB
  | Size512GiB, _ => Size512GiB
  | _, Size512GiB => Size512GiB
  |_, _ => Size128TiB
  end.
Global Instance page_size_meet : Meet page_size := page_size_min.

Lemma page_size_min_le_l sz1 sz2 :
  sz1 ⊓ sz2 ≤ₚ sz1.
Proof.
  unfold ord_le. destruct sz1, sz2; cbn; naive_solver.
Qed.
Lemma page_size_min_le_r sz1 sz2 :
  sz1 ⊓ sz2 ≤ₚ sz2.
Proof.
  unfold ord_le. destruct sz1, sz2; cbn; naive_solver.
Qed.
Lemma page_size_min_l sz1 sz2 :
  sz1 ≤ₚ sz2 → sz1 ⊓ sz2 = sz1.
Proof.
  intros [Hlt | Heq].
  - apply Z.cmp_less_iff in Hlt. destruct sz1, sz2; simpl in *; try done.
  - apply Z.cmp_equal_iff in Heq. destruct sz1, sz2; simpl in *; try done.
Qed.
Lemma page_size_min_r sz1 sz2 :
  sz2 ≤ₚ sz1 → sz1 ⊓ sz2 = sz2.
Proof.
  intros [Hlt | Heq].
  - apply Z.cmp_less_iff in Hlt. destruct sz1, sz2; simpl in *; try done.
  - apply Z.cmp_equal_iff in Heq. destruct sz1, sz2; simpl in *; try done.
Qed.

(** The maximum address at which a page may be located (one-past-the-end address), limited by the page allocator implementation. *)
(* Sealed because it is big and will slow down Coq *)
Definition MAX_PAGE_ADDR_def : Z :=
  page_size_in_bytes_Z Size128TiB.
Definition MAX_PAGE_ADDR_aux : seal MAX_PAGE_ADDR_def. Proof. by eexists. Qed.
Definition MAX_PAGE_ADDR := unseal MAX_PAGE_ADDR_aux.
Definition MAX_PAGE_ADDR_unfold : MAX_PAGE_ADDR = MAX_PAGE_ADDR_def :=
  seal_eq MAX_PAGE_ADDR_aux.

(** * Pages *)
(** Page containing zeroes *)
Definition zero_page (sz : page_size) : list Z :=
  replicate (page_size_in_words_nat sz) 0.

(** Logical representation of a page, consisting of:
   - its location in memory
   - its size
   - its list of words, represented as integers *)
Record page : Type := mk_page {
  page_loc : loc;
  page_sz : page_size;
  page_val : list Z
}.
Canonical Structure pageRT := directRT page.
Global Instance loc_eqdec : EqDecision loc.
Proof. solve_decision. Defined.
Global Instance loc_countable : Countable loc.
Proof. unfold loc. apply prod_countable. Qed.
Global Instance page_inh : Inhabited page.
Proof. exact (populate (mk_page inhabitant inhabitant inhabitant)). Qed.
Global Instance page_eqdec : EqDecision page.
Proof. solve_decision. Defined.
Global Instance page_countable : Countable page.
Proof.
  refine (inj_countable' (λ p, (p.(page_loc), p.(page_sz), p.(page_val)))
    (λ p, mk_page p.1.1 p.1.2 p.2) _).
  intros []; done.
Qed.

(** One-past-the-end location of this page *)
Definition page_end_loc (p : page) : loc :=
  p.(page_loc) +ₗ (page_size_in_bytes_Z p.(page_sz)).

(** Well-formedness of a page *)
Definition page_wf (p : page) : Prop :=
  (** The value has the right size *)
  page_size_in_words_nat p.(page_sz) = length p.(page_val) ∧
  (** The location has the right alignment *)
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


(** How many pages of the next smaller page size are there in this page size? *)
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


(** The above is not correct for the smallest page size *)
Definition number_of_smaller_pages (sz : page_size) : nat :=
  match page_size_smaller sz with
  | Some _ => page_size_multiplier sz
  | _ => 0
  end.

Lemma page_size_multiplier_size_in_words sz sz' :
  sz' = (match page_size_smaller sz with Some sz' => sz' | _ => sz end) →
  page_size_in_words_nat sz = (page_size_in_words_nat sz' * page_size_multiplier sz)%nat.
Proof.
  intros ->.
  destruct sz; simpl.
  all: unfold page_size_smaller; simplify_eq.
  all: rewrite page_size_in_words_nat_unfold /page_size_in_words_nat_def.
  all: unfold page_size_multiplier, page_size_multiplier_log.
  all: cbn [Nat.pow]; lia.
Qed.
Lemma page_size_multiplier_size_in_bytes sz sz' :
  sz' = (match page_size_smaller sz with Some sz' => sz' | _ => sz end) →
  page_size_in_bytes_nat sz = (page_size_in_bytes_nat sz' * page_size_multiplier sz)%nat.
Proof.
  intros Heq.
  unfold page_size_in_bytes_nat. erewrite (page_size_multiplier_size_in_words _ sz'); last done.
  lia.
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

Lemma page_size_multiplier_quot sz smaller_sz :
  smaller_sz = default sz (page_size_smaller sz) →
  page_size_multiplier sz = Z.to_nat (page_size_in_bytes_Z sz `quot` page_size_in_bytes_Z smaller_sz).
Proof.
  intros Hsz.
  rewrite (page_size_multiplier_size_in_bytes _ smaller_sz); last done.
  rewrite Nat.mul_comm.
  rewrite Nat2Z.inj_mul.
  rewrite Z.quot_mul; first lia.
  specialize (page_size_in_bytes_nat_ge smaller_sz). lia.
Qed.
Lemma page_size_multiplier_quot_Z sz smaller_sz :
  smaller_sz = default sz (page_size_smaller sz) →
  page_size_in_bytes_Z sz `quot` page_size_in_bytes_Z smaller_sz = page_size_multiplier sz.
Proof.
  intros ?.
  rewrite (page_size_multiplier_quot _ smaller_sz); last done.
  rewrite Z2Nat.id; first done.
  apply Z.quot_pos.
  - specialize (page_size_in_bytes_nat_ge sz). lia.
  -  specialize (page_size_in_bytes_nat_ge smaller_sz). lia.
Qed.

Lemma page_size_multiplier_in_usize sz :
  (Z.of_nat $ page_size_multiplier sz) ∈ usize.
Proof.
  unfold page_size_multiplier.
  destruct sz; simpl.
  all: split.
  all: unsafe_unfold_common_caesium_defs; simpl.
  all: lia.
Qed.

Lemma page_size_multiplier_ge sz :
  page_size_multiplier sz ≥ 1.
Proof.
  unfold page_size_multiplier.
  nia.
Qed.

(** States that the page is in the given memory range *)
(* TODO unify all the memory range stuff *)
Definition page_within_range (base_address : Z) (sz : page_size) (p : page) : Prop :=
  (base_address ≤ p.(page_loc).2 ∧ p.(page_loc).2 + page_size_in_bytes_Z p.(page_sz) ≤ base_address + page_size_in_bytes_Z sz)%Z.

Lemma page_within_range_inv base sz p :
  page_within_range base sz p →
  p.(page_sz) = sz →
  p.(page_loc).2 = base.
Proof.
  unfold page_within_range.
  intros [] <-.
  lia.
Qed.

Lemma page_within_range_incl base1 base2 sz1 sz2 p :
  base2 ≤ base1 →
  base1 + page_size_in_bytes_Z sz1 ≤ base2 + page_size_in_bytes_Z sz2 →
  page_within_range base1 sz1 p →
  page_within_range base2 sz2 p.
Proof.
  unfold page_within_range.
  simpl. intros ?? [].
  split; lia.
Qed.

Lemma page_within_range_sz_base_inj p sz base1 base2 :
  p.(page_sz) = sz →
  page_within_range base1 sz p →
  page_within_range base2 sz p →
  base1 = base2.
Proof.
  unfold page_within_range.
  intros <-.
  lia.
Qed.

Global Arguments page_within_range : simpl never.
Global Typeclasses Opaque page_within_range.



(** Divide a page into pages of the next smaller page size *)
(** Relational specification *)
Definition subdivided_pages (p : page) (ps : list page) : Prop :=
  let smaller_sz := default p.(page_sz) (page_size_smaller p.(page_sz)) in
  let num_pages := page_size_multiplier p.(page_sz) in
  length ps = num_pages ∧
  (∀ (i : nat) p', ps !! i = Some p' →
    p'.(page_loc) = p.(page_loc) offset{usize}ₗ (i * page_size_in_words_nat smaller_sz) ∧
    p'.(page_sz) = smaller_sz).

Global Arguments subdivided_pages : simpl never.
Global Typeclasses Opaque subdivided_pages.

Lemma subdivided_pages_lookup_size_lt i p ps p' sz' :
  page_size_smaller p.(page_sz) = Some sz' →
  subdivided_pages p ps →
  ps !! i = Some p' →
  page_sz p' = sz'.
Proof.
  unfold subdivided_pages.
  intros -> [Ha Hb] Hlook.
  apply Hb in Hlook. simpl in Hlook.
  destruct Hlook; done.
Qed.
Lemma subdivided_pages_lookup_size_le i p ps p' :
  subdivided_pages p ps →
  ps !! i = Some p' →
  page_sz p' ≤ₚ page_sz p.
Proof.
  unfold subdivided_pages.
  intros [Ha Hb] Hlook.
  apply Hb in Hlook. destruct Hlook as [? ->].
  destruct (page_size_smaller p.(page_sz)) eqn:Heq.
  - eapply page_size_smaller_lt in Heq. left. done.
  - simpl. right.
    apply Z.cmp_equal_iff. done.
Qed.

Lemma subdivided_pages_lookup_base_address (i : nat) p ps p' sz' :
  page_size_smaller p.(page_sz) = Some sz' →
  subdivided_pages p ps →
  ps !! i = Some p' →
  (page_loc p').2 = p.(page_loc).2 + (i * page_size_in_bytes_nat sz').
Proof.
  unfold subdivided_pages.
  intros -> [Ha Hb] Hlook.
  apply Hb in Hlook. simpl in Hlook.
  destruct Hlook as [-> _].
  unfold offset_loc; simpl.
  rewrite /page_size_in_bytes_nat.
  rewrite bytes_per_int_usize.
  lia.
Qed.

Lemma subdivided_pages_length p ps :
  subdivided_pages p ps →
  length ps = page_size_multiplier p.(page_sz).
Proof.
  intros [Ha _]. done.
Qed.

Lemma subdivided_pages_page_within_range (i : nat) p ps p' :
  page_size_smaller p.(page_sz) = Some p'.(page_sz) →
  subdivided_pages p ps →
  ps !! i = Some p' →
  page_within_range (p.(page_loc).2 + i * page_size_in_bytes_Z p'.(page_sz)) p'.(page_sz) p'.
Proof.
  intros ? Hsubdivided Hlook.
  opose proof (subdivided_pages_lookup_base_address i _ _ _ _ _ Hsubdivided _) as Hl.
  { done. }
  { done. }
  split; simpl; lia.
Qed.

Lemma subdivided_pages_page_within_range' i p ps p' sz base :
  page_size_smaller sz = Some p'.(page_sz) →
  subdivided_pages p ps →
  ps !! i = Some p' →
  base = p.(page_loc).2 →
  sz = p.(page_sz) →
  page_within_range base sz p'.
Proof.
  intros Hsmaller Hsubdivided Hlook -> ->.

  specialize (subdivided_pages_length _ _ Hsubdivided) as Hlen.
  opose proof (lookup_lt_Some _ _ _ Hlook) as ?.

  eapply page_within_range_incl; first last.
  { eapply subdivided_pages_page_within_range; done. }
  { opose proof (page_size_multiplier_size_in_bytes p.(page_sz) p'.(page_sz) _) as Heq.
    { rewrite Hsmaller//. }
    rewrite Heq.
    nia. }
  { lia. }
Qed.

Lemma subdivided_pages_lookup_inv p sz base ps p' (i : nat) (j : Z) :
  page_size_smaller p.(page_sz) = Some sz →
  subdivided_pages p ps →
  ps !! i = Some p' →
  p'.(page_sz) = sz →
  base = p.(page_loc).2 →
  page_within_range (base + j * page_size_in_bytes_Z sz) sz p' →
  i = Z.to_nat j.
Proof.
  intros Hsmaller Hsub Hlook <- -> Hran.
  eapply subdivided_pages_page_within_range in Hsub; [ | done | done].

  opose proof (page_within_range_sz_base_inj _ _ _ _ _ Hran Hsub) as Heq; first done.
  specialize (page_size_in_bytes_nat_ge p'.(page_sz)).
  nia.
Qed.


(** Stronger functional specification *)
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

Lemma subdivide_page_wf p :
  page_wf p →
  Forall page_wf (subdivide_page p).
Proof.
  destruct p as [l sz vs].
  rewrite /subdivide_page/=.
  destruct (page_size_smaller sz) as [ sz' | ] eqn:Heq; simpl; first last.
  { econstructor; eauto. }

  opose proof (page_size_multiplier_size_in_words sz _ _) as Hmul.
  { rewrite Heq. done. }
  specialize (page_size_multiplier_align _ _ Heq).
  revert Hmul.
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
    { rewrite length_take -Hlen. lia. }
    { subst words. eapply aligned_to_offset; first done.
      rewrite page_size_align_is_size /page_size_in_bytes_nat.
      rewrite Nat2Z.divide. apply Nat.divide_factor_l. }
  - rewrite drop_drop.
    replace (start * words + words)%nat with ((S start) * words)%nat by lia.
    apply (IH (S start)); last done.
    rewrite Nat.mul_succ_l.
    rewrite -drop_drop length_drop -Hlen.
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

Lemma address_aligned_to_page_size_smaller addr sz smaller_sz :
  addr `aligned_to` page_size_in_bytes_nat sz →
  page_size_smaller sz = Some smaller_sz →
  addr `aligned_to` page_size_in_bytes_nat smaller_sz.
Proof.
  rewrite -!page_size_align_is_size.
  unfold page_size_align.
  intros ? Hsmall.
  enough ((2^page_size_align_log sz)%nat = 2^page_size_align_log smaller_sz * (2^(page_size_align_log sz - page_size_align_log smaller_sz)))%nat as Heq.
  { eapply (base.aligned_to_mul_inv _ _ (2^(page_size_align_log sz - page_size_align_log smaller_sz))). rewrite -Heq. done. }
  destruct sz; simpl in Hsmall; try done.
  all: injection Hsmall as <-.
  all: simpl.
  all: lia.
Qed.


(** Lithium automation *)
Global Instance simpl_exist_page Q :
  SimplExist page Q (∃ (page_loc : loc) (page_sz : page_size) (page_val : list Z),
    Q (mk_page page_loc page_sz page_val)).
Proof.
  intros (? & ? & ? & ?). eexists (mk_page _ _ _). done.
Qed.

Global Instance simpl_forall_page Q :
  SimplForall page 3 Q (∀ (page_loc : loc) (page_sz : page_size) (page_val : list Z),
    Q (mk_page page_loc page_sz page_val)).
Proof.
  intros ?. intros []. done.
Qed.

Global Instance simpl_impl_page_size_smaller sz sz' :
  SimplImpl false (page_size_smaller sz = Some sz') (λ T, page_size_smaller sz = Some sz' → page_size_variant sz' = page_size_variant sz - 1 → T).
Proof.
  intros T. split.
  - intros Ha Hsmall. specialize (page_size_smaller_page_size_variant _ _ Hsmall) as ?.
    by apply Ha.
  - intros Ha. intros. by apply Ha.
Qed.
Global Instance simpl_impl_page_size_larger sz sz' :
  SimplImpl false (page_size_larger sz = Some sz') (λ T, page_size_larger sz = Some sz' → page_size_variant sz' = page_size_variant sz + 1 → T).
Proof.
  intros T. split.
  - intros Ha Hlarge. specialize (page_size_larger_page_size_variant _ _ Hlarge) as ?.
    by apply Ha.
  - intros Ha. intros. by apply Ha.
Qed.

Global Instance simpl_both_page_size_smaller_none sz :
  SimplBothRel (=) (page_size_smaller sz) None (sz = Size4KiB).
Proof.
  split; destruct sz; simpl; done.
Qed.
Global Instance simpl_both_page_size_larger_none sz :
  SimplBothRel (=) (page_size_larger sz) None (sz = Size128TiB).
Proof.
  split; destruct sz; simpl; done.
Qed.

From refinedrust Require Import typing.

(* This reflects the page sizes in [core/mmu/page_size.rs] *)
Inductive page_size : Set :=
  | Size4KiB
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
  | Size2MiB => 512 * 512
  | Size1GiB => 512 * 512 * 512
  | Size512GiB => 512 * 512 * 512
  | Size128TiB => 512 * 512 * 512 * 512 * 256
  end.

Definition page_size_in_bytes_nat (sz : page_size) : nat :=
  bytes_per_addr * page_size_in_words_nat sz.
Definition page_size_in_bytes_Z (sz : page_size) : Z :=
  page_size_in_bytes_nat sz.


Definition page_size_smaller (sz : page_size) : option page_size :=
  match sz with
  | Size4KiB => None
  | Size2MiB => Some Size4KiB
  | Size1GiB => Some Size2MiB
  | Size512GiB => Some Size1GiB
  | Size128TiB => Some Size512GiB
  end.
Definition page_size_larger (sz : page_size) : option page_size :=
  match sz with
  | Size4KiB => Some Size2MiB
  | Size2MiB => Some Size1GiB
  | Size1GiB => Some Size512GiB
  | Size512GiB => Some Size128TiB
  | Size128TiB => None
  end.

(* Pages should be aligned to the size of the page *)
Definition page_size_align_log (sz : page_size) : nat :=
  match sz with
  | Size4KiB => 12
  | Size2MiB => 21
  | Size1GiB => 30
  | Size512GiB => 39
  | Size128TiB => 47
  end.

Definition mk_page_layout (sz : page_size) : layout :=
  Layout (page_size_in_bytes_nat sz) (page_size_align_log sz).

(*
Definition zero_byte := MByte byte0 None.
Definition zero_word := replicate bytes_per_addr zero_byte.
Definition zero_page (sz : page_size) : list val :=
  replicate (page_size_in_words_nat sz) zero_word.
 *)
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

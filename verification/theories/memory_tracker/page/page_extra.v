From refinedrust Require Import typing.

(* This reflects the page sizes in [core/mmu/page_size.rs] *)
Inductive page_size : Set :=
  | Size4KiB
  | Size2MiB
  | Size1GiB
  | Size512GiB
  | Size128TiB.

Definition page_size_to_nat (sz : page_size) : nat :=
  match sz with
  | Size4KiB => 8 * 512
  | Size2MiB => 8 * 512 * 512
  | Size1GiB => 8 * 512 * 512 * 512
  | Size512GiB => 8 * 512 * 512 * 512
  | Size128TiB => 8 * 512 * 512 * 512 * 512 * 256
  end.
Definition page_size_to_Z (sz : page_size) : Z :=
  page_size_to_nat sz.

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
  Layout (page_size_to_nat sz) (page_size_align_log sz).

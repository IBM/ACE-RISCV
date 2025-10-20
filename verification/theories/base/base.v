From refinedrust Require Import typing.

(** * Lemmas that should probably be upstreamed *)

Lemma aligned_to_mul_inv l al num :
  l `aligned_to` al * num →
  l `aligned_to` al.
Proof.
  rewrite /aligned_to.
  intros (k & Heq). intros. exists (k * num). lia.
Qed.

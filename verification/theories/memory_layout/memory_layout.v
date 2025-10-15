From refinedrust Require Import typing.

(** * Additional definitions for the security monitor's global memory layout *)

Record memory_layout : Type := mk_memory_layout {
  conf_start : loc;
  conf_end : loc;
  non_conf_start : loc;
  non_conf_end : loc;

  conf_start_in_usize : conf_start.2 ∈ usize;
  conf_end_in_usize : conf_end.2 ∈ usize;
  non_conf_start_in_usize : non_conf_start.2 ∈ usize;
  non_conf_end_in_usize : non_conf_end.2 ∈ usize;
}.
Canonical Structure memory_layoutRT := directRT memory_layout. 

Global Program Instance memory_layout_inhabited : Inhabited memory_layout :=
  populate (mk_memory_layout 
    NULL_loc NULL_loc NULL_loc NULL_loc _ _ _ _).
Solve Obligations with split; unsafe_unfold_common_caesium_defs; sidecond_hammer.

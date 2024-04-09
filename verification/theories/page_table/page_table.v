From refinedrust Require Import typing.
From ace.theories.page Require Import page_extra.

(* TODO: have file for translated sail specs and then link up with this *)

Record page_table_config : Type := {
  pt_accessible_to_user : bool;
  pt_was_accessed : bool;
  pt_is_global_mapping : bool;
  pt_is_dirty : bool;
}.

Record page_table_permission : Type := {
  ptp_can_read : bool;
  ptp_can_write : bool;
  ptp_can_execute : bool;
}.

Record shared_page : Type := {
  (* TODO *)
}.

(* Can we avoid mutual inductives? *)
Inductive page_table_entry : Type :=
  | PointerToNextPageTable
      (next : page_table_tree)
      (conf : page_table_config)

  | PageWithConfidentialVmData
      (p : page)
      (conf : page_table_config)
      (perm : page_table_permission)

  | PageSharedWithHypervisor
      (sp : shared_page)
      (conf : page_table_config) 
      (perm : page_table_permission)

  | NotValid

with page_table_tree :=
  | PageTableTree
      (entries : list page_table_entry)
      (level : nat)
.

(* TODO: maybe make this intrinsic using dependent type *)
Definition page_table_wf (t : page_table_tree) :=
  (* ensure that levels are decreasing *)
  (* TODO *)
  True
.
(* TODO: ensure everything is in confidential memory *)

Definition is_byte_level_representation (pt_logical : page_table_tree) (pt_byte : page) :=
  page_table_wf pt_logical ∧
  (* FIXME *)
  True
.

Definition page_table_get_level (pt : page_table_tree) : nat :=
  match pt with
  | PageTableTree _ level => level
  end.

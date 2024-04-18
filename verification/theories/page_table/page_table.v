From refinedrust Require Import typing.
From ace.theories.page Require Import page_extra.

(** * Architectural ground-truth *)
(* TODO: have file for translated sail specs and then link up with this *)

Inductive pte_flags_bits : Type :=
  | PTValid
  | PTRead
  | PTWrite
  | PTExecute
  | PTUser
  | PTGlobal
  | PTAccessed
  | PTDirty
.
Definition pte_flags_bits_bits_position (b : pte_flags_bits) :=
  match b with
  | PTValid => 0
  | PTRead => 1
  | PTWrite => 2
  | PTExecute => 3
  | PTUser => 4
  | PTGlobal => 5
  | PTAccessed => 6
  | PTDirty => 7
  end.

(** * Logical representation *)
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

Inductive paging_system :=
  | Sv57x4.

Inductive page_table_level :=
  | PTLevel5
  | PTLevel4
  | PTLevel3
  | PTLevel2
  | PTLevel1.



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
      (system : paging_system)
      (entries : list page_table_entry)
      (level : page_table_level)
.

Definition pg_get_system (pg : page_table_tree) : paging_system :=
  match pt with
  | PageTableTree system _ _ => system
  end.

Definition pt_get_level (pt : page_table_tree) : page_table_level :=
  match pt with
  | PageTableTree _ level => level
  end.

Definition pt_get_entries (pt : page_table_tree) : list page_table_entry :=
  match pt with
  | PageTableTree entries _ => entries
  end.

(*Fixpoint page_table_levels_decreasing (p : page_table_tree) :=*)
  (*match p with*)
  (*| PageTableTree entries level =>*)
      (*Forall page_table_entry_levels_decreasing entries ∧*)
      (*max_list (fmap *)
(*with page_table_entry_levels_decreasing (pt : page_table_entry) :=*)
  (*match pt with*)
  (*| PointerToNextPageTable next conf =>*)

Definition paging_system_highest_level (system : paging_system) : page_table_level :=
  match system with
  | Sv57x4 => PTLevel5
  end.

Definition number_of_page_table_entries (system : paging_system) (level : page_table_level) : nat :=
  if decide (level = paging_system_highest_level system) then 2048 else 512.

Definition pt_number_of_entries (pt : page_table_tree) : nat :=
  match pt with
  | PageTableTree system level _ => number_of_page_table_entries system level
  end.

(* TODO: maybe make this intrinsic using dependent type *)
Definition page_table_wf (t : page_table_tree) :=
  (* number of page table entries is determined by the level *)
  (match t with | PageTableTree entries level => number_of_page_table_entries level = length entries end) ∧
  (* ensure that levels are decreasing *)
  (* TODO *)
  (* ensure that the system is the same across the whole page table *)
  (* TODO *)
  True
.
(* TODO: ensure everything is in confidential memory *)


(** Encoding *)
Definition encode_page_table_entry (pte : page_table_entry) : Z :=
  (* TODO *)
  0.

Definition encode_page_table_entries (entries : list page_table_entry) : list Z :=
  encode_page_table_entry <$> entries
.

Definition is_byte_level_representation (pt_logical : page_table_tree) (pt_byte : page) :=
  (* The logical representation is well-formed *)
  page_table_wf pt_logical ∧
  (* We have a 16KiB page for Level 5, and 4KiB pages otherwise *)
  (if pt_get_level pt_logical is PTLevel5 then pt_byte.(page_sz) = Size16KiB else pt_byte.(page_sz) = Size4KiB) ∧
  (* The encoding of the entries matches the physical content of the pages *)
  pt_byte.(page_val) = encode_page_table_entries (pt_get_entries pt_logical)
.


(** Operations modifying the page table *)
Definition pt_set_entry (pt : page_table_tree) (index : nat) (entry : page_table_entry) : page_table_tree :=
  match pt with
  | PageTableTree system level entries =>
      PageTableTree system level (<[index := entry]> entries)
  end.

Lemma pt_set_entry_wf : 
  pt_set

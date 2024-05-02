From refinedrust Require Import typing.
From ace.theories.page Require Import page_extra.
From stdpp Require Import bitvector.

(* Based on Release riscv-isa-release-7b8ddc9-2024-05-07 *)

(** Basic defs *)
Definition bv_to_bit {n : N} (m : nat) (bv : bv n) : bool :=
  bv_to_bits bv !!! m.

Definition bit_to_bv (b : bool) : bv 1 :=
  bool_to_bv 1 b.

(** * Architectural ground-truth *)
(* TODO: have file for translated sail specs and then link up with this *)

(** ** Paging system *)
(* Currently we only include the supported paging systems *)
Inductive paging_system :=
  | Sv57.

Global Instance paging_system_eqdec : EqDecision paging_system.
Proof. unfold EqDecision, Decision. intros. destruct x, y; decide equality. Qed.

(** The virtual address length *)
Definition paging_system_virtual_address_length (sys : paging_system) : N :=
  match sys with
  | Sv57 => 57
  end.

(** The physical address length *)
Definition physical_address_length : N := 56.

(** ** PTE Flags *)
Record pte_flags : Type := mk_pte_flags {
  (* 0 *)
  PTEValid : bool;
  (* 1 *)
  PTERead : bool;
  (* 2 *)
  PTEWrite : bool;
  (* 3 *)
  PTEExecute : bool;
  (* 4 *)
  PTEUser : bool;
  (* 5 *)
  PTEGlobal : bool;
  (* 6 *)
  PTEAccessed : bool;
  (* 7 *)
  PTEDirty : bool;
}.

Definition pte_flags_invalid : pte_flags :=
  mk_pte_flags false false false false false false false false.

(* Decode PTE flags *)
Definition pte_decode_flags (pte : bv 7) : pte_flags :=
  mk_pte_flags
    (bv_to_bit 0 pte)
    (bv_to_bit 1 pte)
    (bv_to_bit 2 pte)
    (bv_to_bit 3 pte)
    (bv_to_bit 4 pte)
    (bv_to_bit 5 pte)
    (bv_to_bit 6 pte)
    (bv_to_bit 7 pte)
.

(* Encode PTE flags *)
Definition pte_encode_flags (flags : pte_flags) : bv 8 :=
  bv_concat 8 (bit_to_bv flags.(PTEDirty))
    $ bv_concat 7 (bit_to_bv flags.(PTEAccessed))
    $ bv_concat 6 (bit_to_bv flags.(PTEGlobal))
    $ bv_concat 5 (bit_to_bv flags.(PTEUser))
    $ bv_concat 4 (bit_to_bv flags.(PTEExecute))
    $ bv_concat 3 (bit_to_bv flags.(PTEWrite))
    $ bv_concat 2 (bit_to_bv flags.(PTERead))
    (bit_to_bv flags.(PTEValid))
.

(* Check if PTE is a pointer to next level (non-leaf) *)
Definition pte_is_ptr (flags : pte_flags) : bool :=
  (negb flags.(PTERead)) && (negb flags.(PTEWrite)) && (negb flags.(PTEExecute))
.

(* Check if PTE is valid *)
Definition pte_is_invalid (flags : pte_flags) : bool :=
  (negb flags.(PTEValid)) 
  (* TODO: security monitor does not have to check for it *)
  || (flags.(PTEWrite) && negb flags.(PTERead))
.


(** ** PTE *)

(** Get the bits describing the flags *)
Definition pte_get_flags_bits (pte : bv 64) : bv 8 :=
  bv_extract 0 8 pte.

(** Get the bits describing the rsw *)
Definition pte_get_rsw_bits (pte : bv 64) : bv 2 :=
  bv_extract 8 2 pte.

(** Get the bits describing the ppn *)
Definition pte_ppn_length : N := 44.
Definition pte_get_ppn_bits (pte : bv 64) : bv pte_ppn_length :=
  bv_extract 10 pte_ppn_length pte.

(** Get the bits for the pbmt extension *)
Definition pte_get_pbmt_bits (pte : bv 64) : bv 2 :=
  bv_extract (pte_ppn_length + 10) 2 pte.

(** Get the bits for the napot extension *)
Definition pte_get_napot_bits (pte : bv 64) : bv 1 :=
  bv_extract (pte_ppn_length + 10 + 2) 1 pte.



(** Encode a physical address for a PPN entry *)
Definition encode_physical_address_to_ppn (addr : Z) : bv pte_ppn_length :=
  (* Ignore the 12 lowest bits. We have to wrap around for addresses which exceed physical size, as the higher bits are required to replicate the 56th bit. *)
  bv_extract 12 pte_ppn_length (Z_to_bv physical_address_length addr)
.

(** A valid physical address should fit into 64 bits. The highest 8 bits should replicate the 56th bit. *)
Definition is_valid_physical_address (addr : Z) :=
  ∃ bv_addr, 
    Z_to_bv_checked 64 addr = Some bv_addr ∧
    Forall (λ x, bv_to_bit (N.to_nat physical_address_length) bv_addr = x) (drop (N.to_nat physical_address_length) (bv_to_bits bv_addr)).

(** Encode a page table entry *)
Definition encode_pte
  (phys_addr : Z)
  (flags : pte_flags) : bv 64 :=
  (* The leading bits up to the PPN are zero, including pbmt and napot bits *)
  bv_concat 64 (encode_physical_address_to_ppn phys_addr) (* PPN *)
    $ bv_concat 10 (bv_0 2) (* RSW *)
    $ pte_encode_flags flags (* flags *)
.

(* 
  ∀ guest_physical_address, 
    memory_isolation_translate (some_hw_config) serialized_page_table guest_phyiscal_address = Some real_address →
   real_address belongs to this VM


   (* TODO: does it suffice to prove a weaker property? *)

   is_byte_level_logical_representation logical physical →

   we also need to require that the hardware actually does an exception if the translation fails.



   What is the right way to formalize this?
   Probably we need a logical version and a physical version.

   The physical version is used by the semantics, and it requires access to the whole state in order to follow pointers
   The logical version should be used in our spec, and correspond to the physical version, in that it translates to the same things.


 *)

    

(* Notes:
  all of RWX are zero => pointer to next level
  otherwise a leaf

  W implies R

  SUM bit determines whether supervisor can access user mode pages

  G exists in all address spaces. 

  leaves contain A D U; for non-leafs, they have to be cleared


  How does the shape of the page table relate between the one for guest translation and supervisor translation? 
   Sv57x4 is for guest physical to supervisor physical
  So does the hypervisor also go through this scheme, or is that using Sv57?
   => It's using Sv57. But the hypervisor page table is not managed by the security monitor.
    It's setup by the hypervisor boot process.
   The security monitor only cares about correctly backing up and restoring the satp config.


  Steps for formalization:
   - convert bit sequence to integer
   - stuff to concatenate bit sequences

 *)

Definition translate_address (pt_addr : Z) (σ : state) (addr : Z) : option Z :=
  None
. 


(** * Logical representation *)
(** Configuration of the page table entry *)
Record page_table_config : Type := mk_ptc {
  pt_accessible_to_user : bool;
  pt_was_accessed : bool;
  pt_is_global_mapping : bool;
  pt_is_dirty : bool;
}.
Global Instance page_table_config_inh : Inhabited page_table_config := populate (mk_ptc false false false false).


(** Permissions for this page table entry *)
Record page_table_permission : Type := mk_ptp {
  ptp_can_read : bool;
  ptp_can_write : bool;
  ptp_can_execute : bool;
}.
Global Instance page_table_permission_inh : Inhabited page_table_permission := populate (mk_ptp false false false).

Definition pt_permission_pointer : page_table_permission :=
  mk_ptp false false false.

(** Encode page table flags *)
Definition to_pte_flags (valid : bool) (ptc : page_table_config) (ptp : page_table_permission) : pte_flags := {|
  PTEValid := valid;
  PTERead := ptp.(ptp_can_read);
  PTEWrite := ptp.(ptp_can_write);
  PTEExecute := ptp.(ptp_can_execute);
  PTEUser := ptc.(pt_accessible_to_user);
  PTEGlobal := ptc.(pt_is_global_mapping);
  PTEAccessed := ptc.(pt_was_accessed);
  PTEDirty := ptc.(pt_is_dirty);
|}.

(** 
  How do we decode things? 
  Should we take an integer or another type? 
   Idea: define a bitvector type that at least requires that it's in the given bitwidth. 
   But I guess this is already given by the integer type itself.
   I could represent it as a list of bits, instead. 
   But encoding/decoding should anyways be reversible. So it wouldn't change much.
    decode (encode bits) = Some bits
    decode i = Some bits → encode bits = i

  I guess the main advantage is that it's easier to do stuff with masking etc. 
   
  Especially with or-ing stuff. 
   that will be difficult to do otherwise. 

*)
(*Definition *)

(** The valid PTE flag bits. *)
Inductive pte_flags_bits :=
  | PTValid
  | PTRead
  | PTWrite
  | PTExecute
  | PTUser
  | PTGlobal
  | PTAccessed
  | PTDirty
.

(*Definition pte_flags_bits_mask *)


Record shared_page : Type := {
  shared_page_hv_address : Z;
  shared_page_sz : page_size;
}.

Inductive page_table_level :=
  | PTLevel5
  | PTLevel4
  | PTLevel3
  | PTLevel2
  | PTLevel1.

Global Instance page_table_level_eqdec : EqDecision page_table_level.
Proof. solve_decision. Qed.

Definition paging_system_highest_level (system : paging_system) : page_table_level :=
  match system with
  | Sv57x4 => PTLevel5
  end.

Definition number_of_page_table_entries (system : paging_system) (level : page_table_level) : nat :=
  if decide (level = paging_system_highest_level system) then 2048%nat else 512%nat.

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
      (serialized_addr : Z)
      (entries : list page_table_entry)
      (level : page_table_level)
.

Definition pt_get_system (pt : page_table_tree) : paging_system :=
  match pt with
  | PageTableTree system _ _ _ => system
  end.

Definition pt_get_level (pt : page_table_tree) : page_table_level :=
  match pt with
  | PageTableTree _ _ _ level => level
  end.

Definition pt_get_entries (pt : page_table_tree) : list page_table_entry :=
  match pt with
  | PageTableTree _ _ entries _ => entries
  end.

Definition pt_get_serialized_addr (pt : page_table_tree) : Z :=
  match pt with
  | PageTableTree _ loc _ _ => loc
  end.

Definition pt_number_of_entries (pt : page_table_tree) : nat :=
  match pt with
  | PageTableTree system _ _ level => number_of_page_table_entries system level
  end.

(*Fixpoint page_table_levels_decreasing (p : page_table_tree) :=*)
  (*match p with*)
  (*| PageTableTree entries level =>*)
      (*Forall page_table_entry_levels_decreasing entries ∧*)
      (*max_list (fmap *)
(*with page_table_entry_levels_decreasing (pt : page_table_entry) :=*)
  (*match pt with*)
  (*| PointerToNextPageTable next conf =>*)

Fixpoint page_table_tree_has_system (system : paging_system) (pt : page_table_tree) :=
  match pt with
  | PageTableTree system' _ entries _ =>
      system = system' ∧
      Forall_cb (page_table_entry_has_system system) entries
  end
with page_table_entry_has_system (system : paging_system) (pte : page_table_entry) :=
  match pte with
  | PointerToNextPageTable pt _ =>
      page_table_tree_has_system system pt
  | _ => 
      True
  end.


(* TODO: maybe make this intrinsic using dependent type *)
Definition page_table_wf (pt : page_table_tree) :=
  (* number of page table entries is determined by the level *)
  number_of_page_table_entries (pt_get_system pt) (pt_get_level pt) = length (pt_get_entries pt) ∧
  (* ensure that levels are decreasing *)
  (* TODO *)
  (* ensure that the system is the same across the whole page table *)
  page_table_tree_has_system (pt_get_system pt) pt
.
(* TODO: ensure everything is in confidential memory *)


Definition make_empty_page_tree (system : paging_system) (level : page_table_level) (loc : Z) := 
  PageTableTree system loc [] level.

(** Encoding *)
Definition encode_page_table_entry_bv (pte : page_table_entry) : bv 64 :=
  match pte with
  | PointerToNextPageTable pt ptc =>
      (* This is not a leaf *)
      encode_pte (pt_get_serialized_addr pt) (to_pte_flags true ptc pt_permission_pointer)
  | PageWithConfidentialVmData pg ptc ptp =>
      encode_pte pg.(page_loc).2 (to_pte_flags true ptc ptp)
  | PageSharedWithHypervisor sp ptc ptp =>
      encode_pte sp.(shared_page_hv_address) (to_pte_flags true ptc ptp)
  | NotValid =>
      encode_pte 0 pte_flags_invalid
  end
.
Definition encode_page_table_entry (pte : page_table_entry) : Z :=
  bv_unsigned $ encode_page_table_entry_bv pte.
Definition encode_page_table_entries (entries : list page_table_entry) : list Z :=
  encode_page_table_entry <$> entries
.

(** Relation that states that [pt_byte] is a valid byte-level representation of [pt_logical]'s entries. *)
Definition is_byte_level_representation (pt_logical : page_table_tree) (pt_byte : page) :=
  (* The physical address matches up *)
  pt_byte.(page_loc).2 = pt_get_serialized_addr pt_logical ∧
  (* The logical representation is well-formed *)
  page_table_wf pt_logical ∧
  (* We have a 16KiB page for Level 5, and 4KiB pages otherwise *)
  (if pt_get_level pt_logical is PTLevel5 then pt_byte.(page_sz) = Size16KiB else pt_byte.(page_sz) = Size4KiB) ∧
  (* The encoding of the entries matches the physical content of the pages *)
  (* NOTE: if the list of entries is [], this should be trivial. *)
  pt_byte.(page_val) = encode_page_table_entries (pt_get_entries pt_logical)
.


(** Operations modifying the page table *)
Definition pt_set_entry (pt : page_table_tree) (index : nat) (entry : page_table_entry) : page_table_tree :=
  match pt with
  | PageTableTree system serialized_addr entries level =>
      PageTableTree system serialized_addr (<[index := entry]> entries) level
  end.

(*Lemma pt_set_entry_wf : *)
  (*pt_set*)

(** ** Using a page table *)
(** Translate an address according to the logical page table representation *)
Definition page_table_translate_address (pt : page_table_tree)  (addr : Z) : option Z :=
  None.

(** State that the page table is represented at a particular root address in memory *)
Definition pt_represented_at (σ : state) (pt : page_table_tree) (pt_addr : Z) :=
  (* TODO *)
  False.

(** Address translation should be consistent between the logical and physical version *)
Lemma page_table_translate_address_consistent_1 (pt : page_table_tree) addr pt_addr σ translated_addr : 
  pt_represented_at σ pt pt_addr →
  page_table_translate_address pt addr = Some translated_addr →
  translate_address pt_addr σ addr = Some translated_addr
.
Proof.
Abort.

Lemma page_table_translate_address_consistent_2 pt addr pt_addr σ translated_addr : 
  pt_represented_at σ pt pt_addr →
  translate_address pt_addr σ addr = Some translated_addr →
  page_table_translate_address pt addr = Some translated_addr
.
Proof.
Abort.

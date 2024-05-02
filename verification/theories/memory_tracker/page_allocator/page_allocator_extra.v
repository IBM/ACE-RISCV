From refinedrust Require Import typing.
From refinedrust Require Import ghost_var_dfrac.
From ace.theories.page Require Import page_extra.

(** * Page allocator ghost state *)
Record memory_region := {
  mreg_start : Z;
  mreg_size : nat;
}.
Definition mreg_end (mreg : memory_region) : Z :=
  mreg.(mreg_start) + mreg.(mreg_size).

(*Definition memory_region_incl *)

Class memory_regionG Σ := {
  mreg_ghost_var :: ghost_varG Σ memory_region;
}.
Section page_allocator.
  Context `{!typeGS Σ}.
  Context `{!memory_regionG Σ}.
  
  Definition has_memory_region_def (γ : gname) (mreg : memory_region) :=
    ghost_var γ DfracDiscarded mreg.
  Definition has_memory_region_aux : seal (@has_memory_region_def). Proof. by eexists. Qed.
  Definition has_memory_region := has_memory_region_aux.(unseal).
  Definition has_memory_region_eq : @has_memory_region = @has_memory_region_def := has_memory_region_aux.(seal_eq).

  Lemma has_memory_region_alloc mreg : 
    ⊢ |==> ∃ γ, has_memory_region γ mreg.
  Proof.
    rewrite has_memory_region_eq.
    iMod (ghost_var_alloc mreg) as (γ) "Hvar".
    iExists γ. by iApply ghost_var_discard.
  Qed.

  Lemma has_memory_region_agree γ mreg1 mreg2 :
    has_memory_region γ mreg1 -∗
    has_memory_region γ mreg2 -∗
    ⌜mreg1 = mreg2⌝.
  Proof.
    rewrite has_memory_region_eq.
    iApply ghost_var_agree.
  Qed.

  Global Instance has_memory_region_pers γ mreg : Persistent (has_memory_region γ mreg).
  Proof.
    rewrite has_memory_region_eq.
    apply _.
  Qed.
End page_allocator.

(* 
New reasoning:
   - we bound the memory region by a constant
   - the page allocator fully covers that region
   - so we get the initial precondition of the recursion

 *)


(*
(** [m1] is a correct abstraction of [m2] to only specify the number of pages at a given size. *)
Definition page_allocator_maps_related (m1 : gmap page_size nat) (m2 : gmap page_size (place_rfn (list (place_rfn page)))) : Prop :=
  ∀ (sz : page_size) num_pages, m1 !! sz = Some num_pages →
    ∃ list_pages : list page,
      (* There exists a list of pages at that size *)
      m2 !! sz = Some (# (<#> list_pages)) ∧
      (* The length matches up *)
      length list_pages = num_pages ∧
      (* The pages have the right size *)
      Forall (λ pg : page, pg.(page_sz) = sz) list_pages.
*)

(** * Page allocator invariants *)
Inductive node_allocation_state :=

  | PageTokenUnavailable

  | PageTokenAvailable

  | PageTokenPartiallyAvailable (allocable_sz : page_size)
.

Global Instance node_allocation_state_eqdec : EqDecision node_allocation_state.
Proof. solve_decision. Defined.

(** Our logical representation of storage nodes *)
Record page_storage_node : Type := mk_page_node {
  (* The size of memory this node controls *)
  max_node_size : page_size;
  (* The base address of the memory region of this node *)
  base_address : Z;
  (* TODO: this state should not really be part of the public state *)
  (* the current state of this node *)
  allocation_state : node_allocation_state;
  (* TODO: this state should not really be part of the public state *)
  (* whether the child nodes have been initialized *)
  children_initialized : bool;
}.

(** Compute the base address of a child node *)
Definition child_base_address (parent_base_address : Z) (child_size : page_size) (child_index : Z) : Z :=
  parent_base_address + (page_size_in_bytes_Z child_size * child_index).

(** Assert that the base address and node size of the children matches up, that the children are sorted.
  The list of children need not be complete (i.e. it might also be empty).
*)
Definition page_storage_node_children_wf (parent_base_address : Z) (parent_node_size : page_size) (children : list page_storage_node) : Prop :=
  (* If there is a smaller child node size *)
  (∀ child_node_size, 
    page_size_smaller parent_node_size = Some child_node_size →
    (* Then all children are sorted *)
    (∀ (i : nat) child, children !! i = Some child → 
      child.(max_node_size) = child_node_size ∧
      child.(base_address) = child_base_address parent_base_address parent_node_size i)) ∧
  (* If there can't be any children, there are no children *)
  (page_size_smaller parent_node_size = None →
    children = [])
.

Definition page_node_can_allocate (node : page_storage_node) : option page_size := 
  match node.(allocation_state) with
  | PageTokenUnavailable => None
  | PageTokenAvailable => Some node.(max_node_size)
  | PageTokenPartiallyAvailable allocable => Some allocable
  end.


Definition page_storage_node_invariant
  (node : page_storage_node)
  (max_sz : option page_size) (maybe_page_token : option page) (children : list page_storage_node) :=

  (* The children, if any, are well-formed *)
  page_storage_node_children_wf node.(base_address) node.(max_node_size) children ∧
  (* the base address is suitably aligned *)
  (page_size_align node.(max_node_size) | node.(base_address))%Z ∧

  (* initialization of child nodes *)
  (if node.(children_initialized) then length children = page_size_multiplier node.(max_node_size) else True) ∧

  (* invariant depending on the allocation state: *)
  if decide (node.(allocation_state) = PageTokenUnavailable) 
  then 
      (* No allocation is possible *)
      maybe_page_token = None ∧ max_sz = None ∧

      (* all children are unavailable *)
      (* TODO do we need this *)
      Forall (λ child, child.(allocation_state) = PageTokenUnavailable) children
  else if decide (node.(allocation_state) = PageTokenAvailable)
  then
      (* This node is completely available *) 
      ∃ token,
        (* there is some token *)
        maybe_page_token = Some token ∧
        (* the allocable size spans the whole page *)
        max_sz = Some (node.(max_node_size)) ∧
        (* the token spans the whole node *)
        token.(page_loc).2 = node.(base_address) ∧
        token.(page_sz) = node.(max_node_size) ∧
        
        (* all children are unavailable *)
        (* TODO: do we need this? *)
        Forall (λ child, child.(allocation_state) = PageTokenUnavailable) children
  else 

      (* This node is partially available with initialized children *)
      maybe_page_token = None ∧
      (* Some size is available *)
      ∃ allocable_sz, 
      node.(allocation_state) = PageTokenPartiallyAvailable allocable_sz ∧
      max_sz = Some allocable_sz ∧
      
      (* children need to be initialized *)
      node.(children_initialized) = true ∧

      (* The maximum size stored in this node needs to be available in one of the children *)
      ∃ i child, 
        children !! i = Some child ∧ 
        page_node_can_allocate child = Some allocable_sz
.

Lemma page_storage_node_invariant_empty node_size base_address :
  (page_size_align node_size | base_address) →
  page_storage_node_invariant (mk_page_node node_size base_address PageTokenUnavailable false) None None [].
Proof.
  intros.
  split_and!; simpl; last split_and!; try done.
  apply Nat2Z.divide. done.
Qed.

(* TODO unify all the memory range stuff *)
Definition page_within_range (base_address : Z) (sz : page_size) (p : page) : Prop :=
  (base_address ≤ p.(page_loc).2 ∧ p.(page_loc).2 + page_size_in_bytes_Z p.(page_sz) < base_address + page_size_in_bytes_Z sz)%Z.

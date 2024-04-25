From refinedrust Require Import typing.
From ace.theories.page Require Import page_extra.

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

Inductive node_allocation_state :=
  | PageNodeUnavailable
  | PageNodeAvailable
  | PageNodePartiallyAvailable
.

Global Instance node_allocation_state_eqdec : EqDecision node_allocation_state.
Proof. solve_decision. Defined.

Search "aligned".

(** Our logical representation of storage nodes *)
Record page_storage_node : Type := mk_page_node {
  (* The size of memory this node controls *)
  max_node_size : page_size;
  (* The base address of the memory region of this node *)
  base_address : Z;
  
  allocation_state : node_allocation_state;
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


Definition page_storage_node_invariant
  (node : page_storage_node)
  (max_sz : option page_size) (maybe_page_token : option page) (children : list page_storage_node) :=
  (* The children, if any, are well-formed *)
  page_storage_node_children_wf node.(base_address) node.(max_node_size) children ∧
  (* the base address is suitably aligned *)
  (page_size_align node.(max_node_size) | node.(base_address))%Z ∧
  (* invariant depending on the allocation state: *)
  if decide (node.(allocation_state) = PageNodeUnavailable) 
  then 
      (* No allocation is possible *)
      maybe_page_token = None ∧ max_sz = None
  else if decide (node.(allocation_state) = PageNodeAvailable)
  then
      (* This node is completely available *) 
      ∃ token,
        (* there is some token *)
        maybe_page_token = Some token ∧
        (* the token spans the whole node *)
        token.(page_loc).2 = node.(base_address) ∧
        token.(page_sz) = node.(max_node_size) ∧
        (* the allocable size spans the whole page *)
        max_sz = Some (node.(max_node_size)) ∧
        (* all children are unavailable *)
        Forall (λ child, child.(allocation_state) = PageNodeUnavailable) children
  else 
      (* This node is partially available with initialized children *)
      maybe_page_token = None ∧
      length children = page_size_multiplier node.(max_node_size) ∧
      (* The maximum size stored in this node needs to be available in one of the children *)
      ∃ i child, 
        children !! i = Some child ∧ 
        child.(allocation_state) = PageNodeAvailable
.

Lemma page_storage_node_invariant_empty node_size base_address :
  (page_size_align node_size | base_address) →
  page_storage_node_invariant (mk_page_node node_size base_address PageNodeUnavailable) None None [].
Proof.
  intros.
  split_and!; simpl; [ | done..].
  split; done.
Qed.




Definition page_within_range (base_address : Z) (sz : page_size) (p : page) : Prop :=
  base_address ≤ p.(page_loc).2 ∧ p.(page_loc).2 + page_size_in_bytes_Z p.(page_sz) < base_address + page_size_in_bytes_Z sz.
      
  

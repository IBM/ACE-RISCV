From refinedrust Require Import typing.
From refinedrust Require Import ghost_var_dfrac.
From rrstd.cmp.theories Require Import ordering.
From ace.theories.page_allocator Require Import page.

(** * Page allocator ghost state *)

Record memory_region := {
  mreg_start : Z;
  mreg_size : nat;
}.
Definition mreg_end (mreg : memory_region) : Z :=
  mreg.(mreg_start) + mreg.(mreg_size).

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

(** * Page allocator invariants *)
Inductive node_allocation_state :=
(** This page node is completely allocated *)
| PageTokenUnavailable
(** The page token in this node is available *)
| PageTokenAvailable
(** The page node is partially available, with a page of the given size being allocable *)
| PageTokenPartiallyAvailable (allocable_sz : page_size)
.
Global Instance node_allocation_state_eqdec : EqDecision node_allocation_state.
Proof. solve_decision. Defined.
Global Instance node_allocation_state_inhabited : Inhabited node_allocation_state.
Proof. apply (populate PageTokenUnavailable). Qed.

Global Instance node_allocation_state_join : Join node_allocation_state := λ s1 s2,
  match s1, s2 with
  | PageTokenAvailable, _ => PageTokenAvailable
  | _, PageTokenAvailable => PageTokenAvailable
  | PageTokenPartiallyAvailable sz1, PageTokenPartiallyAvailable sz2 =>
      PageTokenPartiallyAvailable (sz1 ⊔ sz2)
  | PageTokenPartiallyAvailable sz1, _ => PageTokenPartiallyAvailable sz1
  | _, PageTokenPartiallyAvailable sz1 => PageTokenPartiallyAvailable sz1
  | _, _ => PageTokenUnavailable
  end.
Global Instance node_allocation_state_meet : Meet node_allocation_state := λ s1 s2,
  match s1, s2 with
  | PageTokenUnavailable, _ => PageTokenUnavailable
  | _, PageTokenUnavailable => PageTokenUnavailable
  | PageTokenPartiallyAvailable sz1, PageTokenPartiallyAvailable sz2 =>
      PageTokenPartiallyAvailable (sz1 ⊓ sz2)
  | PageTokenPartiallyAvailable sz1, _ => PageTokenPartiallyAvailable sz1
  | _, PageTokenPartiallyAvailable sz1 => PageTokenPartiallyAvailable sz1
  | _, _ => PageTokenAvailable
  end.

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
Global Canonical Structure page_storage_nodeRT := directRT page_storage_node.

Global Instance page_storage_node_inh : Inhabited page_storage_node.
Proof.
  constructor. eapply mk_page_node.
  all: apply inhabitant.
Qed.

Definition page_node_update_state (node : page_storage_node) (new_state : node_allocation_state)  : page_storage_node :=
  mk_page_node node.(max_node_size) node.(base_address) new_state node.(children_initialized).

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
      child.(base_address) = child_base_address parent_base_address child_node_size i)) ∧
  (* If there can't be any children, there are no children *)
  (page_size_smaller parent_node_size = None →
    children = [])
.
Lemma page_storage_node_children_wf_child_lookup (i : nat) sz child_node_size base children child :
  page_size_smaller sz = Some child_node_size →
  page_storage_node_children_wf base sz children →
  children !! i = Some child →
  max_node_size child = child_node_size ∧
  base_address child = child_base_address base child_node_size i.
Proof.
  intros Hsmaller Hchildren Hchild.
  destruct Hchildren as [Hchildren _].
  ospecialize (Hchildren _ _ _ _ Hchild); first done.
  done.
Qed.
Lemma page_storage_node_children_wf_upd_state base sz children s :
  page_storage_node_children_wf base sz children →
  page_storage_node_children_wf base sz ((λ node, page_node_update_state node s) <$> children).
Proof.
  unfold page_storage_node_children_wf.
  destruct (page_size_smaller sz) as [smaller_size | ] eqn:Heq.
  - simpl. intros [Ha _]. split; last done.
    intros child_sz [=<-] i child Hlook.
    apply list_lookup_fmap_Some_1 in Hlook as (node & -> & Hlook).
    ospecialize (Ha _ _ _ _ Hlook).
    { done. }
    destruct Ha as [<- Ha].
    done.
  - intros [_ Ha].
    split; first done.
    intros _. rewrite Ha; done.
Qed.
Lemma page_storage_node_children_wf_insert base sz children child' (i : nat) :
  max_node_size child' = max_node_size (children !!! i) →
  base_address child' = base_address (children !!! i) →
  page_storage_node_children_wf base sz children →
  page_storage_node_children_wf base sz (<[i := child']> children).
Proof.
  intros Hsz Haddr [Hwf1 Hwf2]. split.
  - intros child_sz Hsmaller j ? Hlook.
    apply list_lookup_insert_Some in Hlook as [(<- & -> & ?) | (? & ?)]; first last.
    { by eapply Hwf1. }
    rewrite Haddr Hsz.
    opose proof (lookup_lt_is_Some_2 children i _) as (child' & ?); first done.
    erewrite list_lookup_total_correct; last done.
    by eapply Hwf1.
  - intros Hnone. specialize (Hwf2 Hnone). rewrite Hwf2. done.
Qed.

(** Computes the maximum size this page node can allocate *)
Definition page_node_can_allocate (node : page_storage_node) : option page_size :=
  match node.(allocation_state) with
  | PageTokenUnavailable => None
  | PageTokenAvailable => Some node.(max_node_size)
  | PageTokenPartiallyAvailable allocable => Some allocable
  end.

(** The logical invariant on a page node *)
Definition page_storage_node_invariant_case
  (node : page_storage_node)
  (max_sz : option page_size) (maybe_page_token : option page) (children : list page_storage_node) :=
  if decide (node.(allocation_state) = PageTokenUnavailable)
  then
      (* No allocation is possible *)
      maybe_page_token = None ∧ max_sz = None

      (* all children are unavailable *)
      (* TODO do we need this *)
      (*Forall (λ child, child.(allocation_state) = PageTokenUnavailable) children*)
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
        token.(page_sz) = node.(max_node_size)
        (* all children are unavailable *)
        (*Forall (λ child, child.(allocation_state) = PageTokenUnavailable) children*)
  else

      (* This node is partially available with initialized children *)
      maybe_page_token = None ∧
      (* Some size is available *)
      ∃ allocable_sz,
      node.(allocation_state) = PageTokenPartiallyAvailable allocable_sz ∧
      max_sz = Some allocable_sz ∧
      allocable_sz <ₚ node.(max_node_size) ∧

      (* children need to be initialized *)
      node.(children_initialized) = true ∧

      (* The maximum size stored in this node needs to be available in one of the children *)
      ∃ i child,
        children !! i = Some child ∧
        page_node_can_allocate child = Some allocable_sz
.

Lemma page_storage_node_invariant_case_can_allocate node max_sz tok children :
  page_storage_node_invariant_case node max_sz tok children →
  page_node_can_allocate node = max_sz.
Proof.
  unfold page_storage_node_invariant_case, page_node_can_allocate.
  destruct (allocation_state node) eqn:Heq; simpl; naive_solver.
Qed.
Lemma page_node_invariant_case_sized_bounded node max_sz tok children :
  page_storage_node_invariant_case node max_sz tok children →
  max_sz ≤o{option_cmp page_size_cmp} Some (max_node_size node).
Proof.
  unfold page_storage_node_invariant_case, page_node_can_allocate.
  destruct (allocation_state node) eqn:Heq; simpl; solve_goal.
Qed.

Global Typeclasses Opaque page_storage_node_children_wf.
Global Typeclasses Opaque page_storage_node_invariant_case.

Global Arguments page_storage_node_children_wf : simpl never.
Global Arguments page_storage_node_invariant_case : simpl never.


Definition page_storage_node_invariant
  (node : page_storage_node)
  (max_sz : option page_size) (maybe_page_token : option page) (children : list page_storage_node) :=

  (* The children, if any, are well-formed *)
  name_hint "INV_WF" (page_storage_node_children_wf node.(base_address) node.(max_node_size) children) ∧
  (* the base address is suitably aligned *)
  (page_size_align node.(max_node_size) | node.(base_address))%Z ∧

  (* initialization of child nodes *)
  (name_hint "INV_INIT_CHILDREN" (if node.(children_initialized) then length children = page_size_multiplier node.(max_node_size) else children = [])) ∧

  (* invariant depending on the allocation state: *)
  name_hint "INV_CASE" (page_storage_node_invariant_case node max_sz maybe_page_token children)
.

Lemma page_storage_node_invariant_empty node_size base_address :
  (page_size_align node_size | base_address) →
  page_storage_node_invariant (mk_page_node node_size base_address PageTokenUnavailable false) None None [].
Proof.
  intros.
  split_and!; simpl; last split_and!; try done.
  apply Nat2Z.divide. done.
Qed.

Lemma page_storage_node_invariant_case_available_inv node max_sz maybe_tok children :
  node.(allocation_state) = PageTokenAvailable →
  page_storage_node_invariant_case node max_sz maybe_tok children →
  ∃ tok, maybe_tok = Some tok ∧ max_sz = Some node.(max_node_size) ∧ tok.(page_loc).2 = node.(base_address) ∧ tok.(page_sz) = node.(max_node_size).
Proof.
  unfold page_storage_node_invariant_case.
  intros ->. naive_solver.
Qed.

Global Instance page_storage_node_invariant_simpl_available node max_sz maybe_tok children `{!TCDone (node.(allocation_state) = PageTokenAvailable)} `{!IsVar max_sz} `{!IsVar maybe_tok} :
  SimplImpl false (page_storage_node_invariant_case node max_sz maybe_tok children) (λ T,
    page_storage_node_invariant_case node max_sz maybe_tok children →
    max_sz = Some node.(max_node_size) →
    ∀ tok,
    maybe_tok = Some tok →
    tok.(page_loc).2 = node.(base_address) →
    tok.(page_sz) = node.(max_node_size) →
    T).
Proof.
  rename select (TCDone _) into Hstate. unfold TCDone in Hstate.
  intros T. split.
  - intros Ha Hinv.
    specialize (Ha Hinv).
    move: Hinv.
    unfold page_storage_node_invariant_case. rewrite Hstate.
    simpl. intros (? & ? & ? & ? & ?).
    eapply Ha; done.
  - naive_solver.
Qed.

Lemma page_storage_node_invariant_has_token node max_sz tok children :
  page_storage_node_invariant_case node max_sz (Some tok) children →
  node.(allocation_state) = PageTokenAvailable ∧
  node.(max_node_size) = tok.(page_sz) ∧
  node.(base_address) = tok.(page_loc).2.
Proof.
  unfold page_storage_node_invariant_case.
  repeat case_decide; simpl.
  all: naive_solver.
Qed.

Lemma page_storage_node_invariant_not_available node tok children :
  page_storage_node_invariant_case node None tok children →
  node.(allocation_state) = PageTokenUnavailable ∧
  tok = None.
Proof.
  unfold page_storage_node_invariant_case.
  repeat case_decide; simpl.
  all: naive_solver.
Qed.

Lemma page_storage_node_invariant_case_partially_available_inv node max_sz maybe_tok children sz :
  node.(allocation_state) = PageTokenPartiallyAvailable sz →
  page_storage_node_invariant_case node max_sz maybe_tok children →
  max_sz = Some sz ∧ maybe_tok = None.
Proof.
  unfold page_storage_node_invariant_case.
  intros ->. naive_solver.
Qed.

Global Instance page_storage_node_invariant_simpl_partially_available node max_sz maybe_tok children sz `{!TCDone (node.(allocation_state) = PageTokenPartiallyAvailable sz)} `{!IsVar max_sz} `{!IsVar maybe_tok} :
  SimplImpl false (page_storage_node_invariant_case node max_sz maybe_tok children) (λ T,
    page_storage_node_invariant_case node max_sz maybe_tok children →
    max_sz = Some sz → maybe_tok = None →
    T).
Proof.
  rename select (TCDone _) into Hstate. unfold TCDone in Hstate.
  intros T. split.
  - intros Ha Hinv. apply Ha.
    + done.
    + move: Hinv. unfold page_storage_node_invariant_case. rewrite Hstate.
      simpl. naive_solver.
    + move: Hinv. unfold page_storage_node_invariant_case. rewrite Hstate.
      simpl. naive_solver.
  - naive_solver.
Qed.

Lemma page_storage_node_invariant_case_unavailable_inv node max_sz maybe_tok children :
  node.(allocation_state) = PageTokenUnavailable →
  page_storage_node_invariant_case node max_sz maybe_tok children →
  max_sz = None ∧ maybe_tok = None.
Proof.
  unfold page_storage_node_invariant_case.
  intros ->. naive_solver.
Qed.

Global Instance page_storage_node_invariant_simpl_unavailable node max_sz maybe_tok children `{!TCDone (node.(allocation_state) = PageTokenUnavailable)} `{!IsVar max_sz} `{!IsVar maybe_tok} :
  SimplImpl false (page_storage_node_invariant_case node max_sz maybe_tok children) (λ T,
    page_storage_node_invariant_case node max_sz maybe_tok children →
    max_sz = None → maybe_tok = None →
    T).
Proof.
  rename select (TCDone _) into Hstate. unfold TCDone in Hstate.
  intros T. split.
  - intros Ha Hinv. apply Ha.
    + done.
    + move: Hinv. unfold page_storage_node_invariant_case. rewrite Hstate.
      simpl. naive_solver.
    + move: Hinv. unfold page_storage_node_invariant_case. rewrite Hstate.
      simpl. naive_solver.
  - naive_solver.
Qed.

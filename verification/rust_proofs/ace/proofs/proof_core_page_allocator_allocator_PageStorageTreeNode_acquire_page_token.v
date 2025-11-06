From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_proof (π : thread_id) :
  core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_lemma π.
Proof.
  core_page_allocator_allocator_PageStorageTreeNode_acquire_page_token_prelude.

  do 1000 liRStep; liShow.
  do 1000 liRStep; liShow.
  do 1000 liRStep; liShow.
  do 1000 liRStep; liShow.
  do 1000 liRStep; liShow.
  do 1000 liRStep; liShow.
  {
  do 1000 liRStep; liShow.
  do 1000 liRStep; liShow.
  do 1000 liRStep; liShow.
  do 1000 liRStep; liShow.
  {
  do 1000 liRStep; liShow.
  rep <-! liRStep; liShow.
  { rep liRStep; liShow.
    liInst Hevar self.
    do 1000 liRStep; liShow.
    do 1000 liRStep; liShow.
    do 1000 liRStep; liShow.
    do 1000 liRStep; liShow.
    do 1000 liRStep; liShow.
    do 1000 liRStep; liShow.
    do 1000 liRStep; liShow.
    do 1000 liRStep; liShow.
    do 1000 liRStep; liShow.
    do 1000 liRStep; liShow.
    do 1000 liRStep; liShow.
    do 1000 liRStep; liShow.
    do 10 liRStep.
    do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep.
    time do 100 liRStep. 
    time do 100 liRStep.
    time do 100 liRStep.
  }

    time do 100 liRStep. }
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  Unset Ltac Profiling.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  rep <-! liRStep.
  {
    rep liRStep; liShow.
    liInst Hevar self.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.

  rep <-! liRStep.
  set (position_pred := λ node, ((Some page_size_to_acquire) ≤o{ option_cmp page_size_cmp } page_node_can_allocate node)).
  rep liRStep.
  liInst Hevar0 (λ _ _ _, True%I).
  liInst Hevar position_pred.
  rep liRStep. liShow.
  iApply prove_with_subtype_default. iSplitR.
  { rep liRStep. }
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  rep <-! liRStep.
  match goal with 
  | H : page_size_smaller (max_node_size self) = Some ?x |- _ => 
      rename x into child_size;
      rename H into Hsmaller
  end.
  rep liRStep. liShow.
  liInst Hevar (mk_page_node self.(max_node_size) self.(base_address) (node_allocation_state_meet (allocation_state self) (PageTokenPartiallyAvailable child_size)) true).

  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  rep liRStep. liShow.
  iAssert (initialized π "MEMORY_LAYOUT") as "#Hinit".
  { admit. }

  time do 100 liRStep.
  time do 100 liRStep.
 time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
 time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  rep liRStep.
  { 
    unfold name_hint.
    liStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
   time do 100 liRStep.
   rep liRStep.
  (* pick invariant for map *)
  liInst Hevar (λ _ _ _, True%I).
  rep liRStep. liShow.
  (* prove invariant *)
  iApply prove_with_subtype_default. iSplitR.
  { rep liRStep. }
  iApply prove_with_subtype_default. iSplitR.
  { rep liRStep. }

  time do 50 liRStep.
  time do 50 liRStep.
  time do 100 liRStep.
  time do 50 liRStep.
  rep liRStep. liShow.
  iApply prove_with_subtype_default.
  iRename select (MapInv _ _ _ _ _) into "HMAP".
  iSplitL "HMAP". { done. }

  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.


  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.


time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.


  rep <-! liRStep. liShow.

  match goal with 
  | H : Forall2 _ _ ?x2 |- _ =>
      rename H into Hcan_allocate;
      rename x2 into max_allocs
  end.
  set (max_alloc := max_list_cmp (option_cmp page_size_cmp) max_allocs None).
  set (new_state := match max_alloc ≫= id with | Some max => PageTokenPartiallyAvailable max | None => PageTokenUnavailable end).
  rep liRStep.
  liInst Hevar (mk_page_node self.(max_node_size) self.(base_address) new_state true). 
  

  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.


time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.


time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.


time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.


time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.



  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep. }
  time do 100 liRStep. }
  time do 100 liRStep. }
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  rep liRStep.
  liInst Hevar self.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.
  time do 100 liRStep.

  all: print_remaining_goal.
  Unshelve. 
  400-424: sidecond_solver.
  300-400: sidecond_solver.
  200-300: sidecond_solver.
  100-200: sidecond_solver.
  1-100: sidecond_solver.
  Unshelve. 
  all: try lia.
  - eexists. done.
  - done.
  - done.
  - apply page_storage_node_invariant_has_token in INV_CASE as (-> & _). done.
  - opose proof (page_storage_node_invariant_has_token _ _ _ _ INV_CASE) as (Hstate & Hsz & Haddr).
    simpl in Hsz, Haddr. subst.
    exists (max_node_size self). split; last reflexivity.
    unfold page_node_can_allocate. by rewrite Hstate.
  - done.
  - (* contradiction with allocable sz *)
    (* TODO: lemma for no token inv, automation for partialord *)
    (*Ord_spec_attrs*)
    (*PartialOrd_POrd*)
    (*Search "POrd".*)
    (*Search option_partial_cmp.*)
    admit.
  - eexists. done.
  - done.
  - done.
  - rename select (_ ↔ _ = true) into Hpred. 
    rewrite -Hpred.
    unfold position_pred.
    (* we need to know that the page_size_to_acquire capture remains constant at the page_size_to_acquire. 
      This should probably be an invariant we keep when iterating position: the state is unchanged. Probably put this in the position invariant.
    *)
    admit.
  - (* this comes from an unwrap, I think. It might be a good idea to log this on the trace info. Probably from the position unwrap. 
       I'm probably not learning some pure info that I should learn. 
       Probably from Next _ None _ that is in the postcondition.
    *)
    admit.
  - eexists. done.
  - done.
  - (* z is what is returned from position. It seems like I'm not learning enough pure information about that (e.g. about what z actually is) *)
    admit.
  - (* ditto: should prove that at z there is a child. Then follows from invariant on children *)
    admit.
  - (* ditto *)
    admit. 
  - eexists. done.
  - (* ditto *)
    admit.
  - apply page_storage_node_children_wf_insert; done.
  - eexists. done.
  - (* this needs a lemma: under conditions for max_alloc (it is the max allocable size of x), 
  new_state = match max_alloc ≫= id with
  | Some max => PageTokenPartiallyAvailable max
  | None => PageTokenUnavailable
  end →
  page_storage_node_invariant_case
  {|
    max_node_size := max_node_size self;
    base_address := base_address self;
    allocation_state := new_state;
    children_initialized := true
  |} (max_alloc ≫= id) x24 x
     *)
    admit.
  - done.
  - (* contradiction *)
    rename select (¬ ∃ sz, _) into Hcontra.
    contradiction Hcontra.
    (* probably follows from correctness of position *)
    admit.
  - (* we can allocate at least page_size_to_acquire (from partial comp),
      but the size to acquire is not equal to max_node_size, which is the smallest.
       contradiction. *)
    admit.
  - eexists. done.
  - done.
  - done.
  - (* x18 is less than the required size (from partial comp), so we can't allocate anything. *)
    admit.
  - done.
  - (* one of the children can at least allocate it, so this works. *)
    admit.
  - done.
  - (* ditto: need more from position *)
    admit.









    CorrectOrd
    Set Nested Proofs Allowed.
    Lemma page_storage_node_invariant_case 
    Search page_storage_node_invariant_case. has_no_token

  all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

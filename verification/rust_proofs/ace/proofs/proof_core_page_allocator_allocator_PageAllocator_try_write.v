From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageAllocator_try_write.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* The guard's ownership invariant does not depend on its refinement. After
   the callback, subtyping can therefore expose the concrete refinement
   required by drop glue without constraining the callback's postcondition. *)
Local Lemma owned_subtype_write_guard_unit (R_rt : RT)
    (T_ty : type unit) (R_ty : type R_rt) κ π E L
    (r1 r2 : place_rfn unit) T :
  T L ⊢ owned_subtype π E L false r1 r2
    (rwlock_RwLockWriteGuard_inv_t unit R_rt -[κ] -[T_ty; R_ty])
    (rwlock_RwLockWriteGuard_inv_t unit R_rt -[κ] -[T_ty; R_ty]) T.
Proof.
  unfold owned_subtype.
  iIntros "HT". iIntros (????) "CTX HE HL".
  iExists L. iFrame. iModIntro.
  unfold owned_type_incl. iSplitR.
  { iPureIntro. apply syn_type_size_eq_refl. }
  iSplitR. { auto. }
  iIntros (v) "Hv".
  iApply (ex_plain_t_own_val_transport with "[] Hv").
  iIntros (x) "HP Hv". iExists x. iFrame.
Qed.
Local Definition owned_subtype_write_guard_unit_inst :=
  [instance @owned_subtype_write_guard_unit].
Local Existing Instance owned_subtype_write_guard_unit_inst | 5.

Lemma core_page_allocator_allocator_PageAllocator_try_write_proof (π : thread_id) :
  core_page_allocator_allocator_PageAllocator_try_write_lemma π.
Proof.
  core_page_allocator_allocator_PageAllocator_try_write_prelude.

  rep <-! liRStep; liShow.
  (* !start proof(page_allocator.try_write) *)
  rep liRStep. liShow.
  iRename select (∀ _, FnOnce_Pre _ _ _ _ _)%I into "Hpre".
  liInst Hevar_x1 p.
  iApply find_in_context_closure_pre.
  iExists p.
  iSplitR. { iApply "Hpre". }
  rep <-! liRStep; liShow.
  (* Expose the returned guard refinement before its drop glue borrows it. *)
  iRename select (RelEq _ _) into "Hrel".
  iEval (unfold RelEq) in "Hrel".
  iDestruct "Hrel" as (r1 r2) "(#Hpobs1 & Hobs2 & %Heq)".
  iAssert (RelEq γ0 γ) with "[Hobs2]" as "Hrel".
  { unfold RelEq. iExists r1, r2. iFrame "∗ #". done. }
  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  liInst Hevar_x2 γ0.
  rep <-! liRStep; liShow.
  (* !end proof *)

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  apply Hno_unwind. unfold closure_may_unwind.
  do 3 eexists. eassumption.
Qed.
End proof.

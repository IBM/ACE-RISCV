From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageAllocator_try_write.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageAllocator_try_write_proof (π : thread_id) :
  core_page_allocator_allocator_PageAllocator_try_write_lemma π.
Proof.
  core_page_allocator_allocator_PageAllocator_try_write_prelude.

  rep <-! liRStep; liShow.
  (* !start proof(page_allocator.try_write) *)
  rep liRStep. liShow.
  iRename select (∀ _, FnOnce_Pre _ _ _ _ _)%I into "Hpre".
  liInst Hevar_x1 p.
  iApply prove_with_subtype_default.
  iSplitR. { iApply "Hpre". }
  rep liRStep. liShow.
  liInst Hevar_x2 γ0.
  rep liRStep.
  (* !end proof *)

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

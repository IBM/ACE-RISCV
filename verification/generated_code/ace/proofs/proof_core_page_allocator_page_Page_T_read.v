From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace.
From sm.ace.generated Require Import generated_template_core_page_allocator_page_Page_T_read.

Set Default Proof Using "Type".

Lemma bytes_per_int_usize : 
  bytes_per_int usize_t = bytes_per_addr.
Proof. done. Qed.

Section proof.
Context `{!typeGS Σ}.
Lemma core_page_allocator_page_Page_T_read_proof (π : thread_id) :
  core_page_allocator_page_Page_T_read_lemma π.
Proof.
  core_page_allocator_page_Page_T_read_prelude.

  rep <-! liRStep; liShow.
  { (* accessing the element of the array for the read requires manual reasoning *)
    destruct H_off as (off' & ->).

    apply_update (updateable_typed_array_access l off' (IntSynType usize_t)).
    rep liRStep; liShow. }
  { rep liRStep; liShow. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { move: H_sz.
    rewrite /page_size_in_bytes_Z/page_size_in_bytes_nat bytes_per_int_usize.
    clear.
    assert (bytes_per_addr > 0). { solve_goal. }
    nia. }
  { revert H_off. rewrite -Z.rem_divide; done. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

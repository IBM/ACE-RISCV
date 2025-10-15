From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_page_Page_T_write.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_page_Page_T_write_proof (π : thread_id) :
  core_page_allocator_page_Page_T_write_lemma π.
Proof.
  core_page_allocator_page_Page_T_write_prelude.

  rep <-! liRStep; liShow.
  { 
    rename select (offset_in_bytes `rem` 8 = 0) into Hoffset.
    apply Z.rem_divide in Hoffset; last done.
    destruct Hoffset as (off' & ->).

    apply_update (updateable_typed_array_access self off' (IntSynType usize)).

    (*rep <-! liRStep; liShow.*)
    rep liRStep; liShow.
  } 
  { rep liRStep; liShow. }
  { rep liRStep; liShow. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { 
    revert select (_ + off' * 8 < _ + page_size_in_bytes_Z _).
    rewrite /page_size_in_bytes_Z/page_size_in_bytes_nat.
    rewrite bytes_per_addr_eq. nia. }
  { rewrite /name_hint.
    rewrite bytes_per_int_usize bytes_per_addr_eq.
    apply Z.divide_factor_r. }
  { rewrite /name_hint.
    assert (off' * 8 < page_size_in_bytes_Z self0) as Hx by lia.
    revert Hx. unfold page_size_in_bytes_Z.
    specialize (page_size_in_bytes_div_8 self0) as (? & ->).
    rewrite bytes_per_int_usize.
    rewrite bytes_per_addr_eq. lia. }
  { exists (Z.to_nat off'). 
    rewrite bytes_per_int_usize bytes_per_addr_eq.
    normalize_and_simpl_goal. }
  { rewrite /name_hint.
    rename select (¬ _ < _ < _) into Hnlt.
    intros []. apply Hnlt. split. { 
      enough (bytes_per_int usize > 0) by lia. 
      rewrite bytes_per_int_usize bytes_per_addr_eq.
      lia. }
    revert select (_ < (conf_end _).2).
    unfold page_size_in_bytes_Z. lia. }
  { rewrite /name_hint.
    intros []. 
    rename select (offset_in_bytes `rem` 8 ≠ 0) into Hen.
    apply Hen. unfold name_hint in *.
    apply Z.rem_divide; done. }

  Unshelve. all: print_remaining_sidecond.
Admitted. (* admitted due to admit_proofs config flag *)
End proof.

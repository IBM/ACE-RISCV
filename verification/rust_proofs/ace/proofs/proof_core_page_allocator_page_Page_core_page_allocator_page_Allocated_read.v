From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace.
From sm.ace.generated Require Import generated_template_core_page_allocator_page_Page_core_page_allocator_page_Allocated_read.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma core_page_allocator_page_Page_core_page_allocator_page_Allocated_read_proof (π : thread_id) :
  core_page_allocator_page_Page_core_page_allocator_page_Allocated_read_lemma π.
Proof.
  core_page_allocator_page_Page_core_page_allocator_page_Allocated_read_prelude.

  rep <-! liRStep; liShow.
  { (* accessing the element of the array for the read requires manual reasoning *)
    rename select (offset_in_bytes `rem` 8 = 0) into Hoffset.
    apply Z.rem_divide in Hoffset; last done.
    destruct Hoffset as (off' & ->).

    apply_update (updateable_typed_array_access self off' (IntSynType usize)).

    repeat liRStep; liShow.
  }
  all: repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  {
    revert select (_ + off' * 8 < _ + page_size_in_bytes_Z _).
    rewrite /page_size_in_bytes_nat.
    rewrite bytes_per_addr_eq. nia. }
  { assert (off' * 8 < page_size_in_bytes_Z self0) as Hx by lia.
    revert Hx.
    specialize (page_size_in_bytes_div_8 self0) as (? & ->).
    rewrite bytes_per_int_usize.
    rewrite bytes_per_addr_eq. lia. }
  { exists (Z.to_nat off').
    rewrite bytes_per_int_usize bytes_per_addr_eq.
    split; last done. nia. }
  { intros [].
    rename select (offset_in_bytes `rem` 8 ≠ 0) into Hen.
    apply Hen. unfold name_hint in *.
    apply Z.rem_divide; done. }

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

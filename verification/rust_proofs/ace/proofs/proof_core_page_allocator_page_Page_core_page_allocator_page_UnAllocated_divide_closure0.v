From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_closure0.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_closure0_proof (π : thread_id) :
  core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_closure0_lemma π.
Proof.
  core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_closure0_prelude.

  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft7" "ulft5").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "plft21" "vlft7").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft9" "ulft5").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft11" "ulft5").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "plft24" "vlft11").
  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "plft22" "ulft5").
  rep <-! liRStep; liShow.
  rename select (if_Err _ _) into Herr.
  rename select (if_Ok _ _) into Hok.
  destruct x' as [ | x']; first last.
  { exfalso. simpl in *. apply Herr. split; last lia.
    move: Hinrange Hpage_end. unfold page_size_in_bytes_Z. lia. }
  simpl in *. revert Hok.
  rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - (* add *)
    eapply aligned_to_offset.
    { apply Haligned. }
    rewrite page_size_align_is_size /page_size_in_bytes_Z.
    apply Z.divide_factor_r.
  - move: Hinrange Hpage_end. rewrite /page_size_in_bytes_Z. nia.

  Unshelve. all: print_remaining_sidecond.
Admitted. (* admitted due to admit_proofs config flag *)
End proof.

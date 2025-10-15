From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_architecture_riscv_mmu_page_size_PageSize_number_of_smaller_pages.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_architecture_riscv_mmu_page_size_PageSize_number_of_smaller_pages_proof (π : thread_id) :
  core_architecture_riscv_mmu_page_size_PageSize_number_of_smaller_pages_lemma π.
Proof.
  core_architecture_riscv_mmu_page_size_PageSize_number_of_smaller_pages_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: unsafe_unfold_common_caesium_defs; simpl; lia. 
  Unshelve. all: print_remaining_sidecond.
Admitted. (* admitted due to admit_proofs config flag *)
End proof.

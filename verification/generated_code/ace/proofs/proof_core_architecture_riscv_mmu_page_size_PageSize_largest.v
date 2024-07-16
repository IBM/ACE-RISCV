From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_architecture_riscv_mmu_page_size_PageSize_largest.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma core_architecture_riscv_mmu_page_size_PageSize_largest_proof (π : thread_id) :
  core_architecture_riscv_mmu_page_size_PageSize_largest_lemma π.
Proof.
  core_architecture_riscv_mmu_page_size_PageSize_largest_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Admitted. (* admitted due to admit_proofs config flag *)
End proof.

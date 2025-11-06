From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_closure0_call_once.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_closure0_call_once_proof (π : thread_id) :
  core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_closure0_call_once_lemma π.
Proof.
  core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_divide_closure0_call_once_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

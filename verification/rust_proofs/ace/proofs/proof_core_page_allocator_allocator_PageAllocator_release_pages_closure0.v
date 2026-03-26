From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageAllocator_release_pages_closure0.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_page_allocator_allocator_PageAllocator_release_pages_closure0_proof (π : thread_id) :
  core_page_allocator_allocator_PageAllocator_release_pages_closure0_lemma π.
Proof.
  core_page_allocator_allocator_PageAllocator_release_pages_closure0_prelude.

  rep <-! liRStep; liShow.
  (* !start proof(page_allocator.release_pages) *)
  apply_update (updateable_copy_lft "ulft2" "ulft_3").
  rep liRStep; liShow.
  (* !end proof *)

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  (* !start proof(page_allocator.release_pages) *)
  all: try congruence.
  all: clear_layout.
  - rename select (max_node_size root_node = Size128TiB) into Hsz_root.
    rewrite Hsz_root. solve_goal.
  - rewrite /page_within_range.
    rewrite Hroot_base.
    simpl.
    split. { lia. }
    rename select (_ ≤ MAX_PAGE_ADDR) into Hbounds.
    etrans; first apply Hbounds.
    rewrite MAX_PAGE_ADDR_unfold /MAX_PAGE_ADDR_def.
    rename select (max_node_size _ = max_node_size root_node) into Hsz.
    rename select (max_node_size root_node = Size128TiB) into Hsz'.
    rewrite Hsz Hsz'. lia.
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

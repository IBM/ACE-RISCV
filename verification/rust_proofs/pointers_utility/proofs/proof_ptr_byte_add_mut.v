From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From ace_ptr.pointers_utility.generated Require Import generated_code_pointers_utility generated_specs_pointers_utility generated_template_ptr_byte_add_mut.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma ptr_byte_add_mut_proof (π : thread_id) :
  ptr_byte_add_mut_lemma π.
Proof.
  ptr_byte_add_mut_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  (* !start proof(pointers_utility.ptr_byte_add_mut) *)
  all: try rename select ((wrap_unsigned (pointer.(loc_a) + offset_in_bytes) usize < owned_region_end.(loc_a))) into Hwrap_lt.
  all: try rename select (wrap_unsigned (pointer.(loc_a) + offset_in_bytes) usize ≤ pointer.(loc_a)) into Hoverflow.
  { opose proof (wrap_unsigned_le (pointer.(loc_a) + offset_in_bytes) usize _); lia. }
  { apply wrap_unsigned_add_did_wrap in Hoverflow; [ | done.. | lia].
    sidecond_hammer.
  }
  { rewrite wrap_unsigned_add_did_not_wrap in Hwrap_lt; sidecond_hammer. }
  { rewrite wrap_unsigned_add_did_not_wrap in Hwrap_lt; [ | sidecond_hammer..].
    apply wrapping_shift_loc_shift_loc.
    sidecond_hammer.
  }
  { (* offset is zero. So this is okay. *)
    assert (offset_in_bytes = 0) as -> by lia.
    rewrite Z.add_0_r in Hwrap_lt.
    rewrite wrap_unsigned_id in Hwrap_lt; [ lia | done..  ]. }
  { assert (offset_in_bytes = 0) as -> by lia.
    rewrite shift_loc_0 wrapping_shift_loc_0//. }
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.

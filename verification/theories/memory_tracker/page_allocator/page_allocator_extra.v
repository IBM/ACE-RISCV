From refinedrust Require Import typing.
From ace.theories.page Require Import page_extra.

(** [m1] is a correct abstraction of [m2] to only specify the number of pages at a given size. *)
Definition page_allocator_maps_related (m1 : gmap page_size nat) (m2 : gmap page_size (place_rfn (list (place_rfn page)))) : Prop :=
  ∀ (sz : page_size) num_pages, m1 !! sz = Some num_pages →
    ∃ list_pages : list page,
      (* There exists a list of pages at that size *)
      m2 !! sz = Some (# (<#> list_pages)) ∧
      (* The length matches up *)
      length list_pages = num_pages ∧
      (* The pages have the right size *)
      Forall (λ pg : page, pg.(page_sz) = sz) list_pages.


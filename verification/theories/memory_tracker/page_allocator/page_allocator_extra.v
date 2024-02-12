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

(** The list of [pages] forms a contiguous region of memory, one page after another. *)
Fixpoint pages_are_contiguous (pages : list page) : Prop :=
  match pages with
  | [] => True
  | pg1 :: pgs =>
      match pgs with
      | [] => True
      | pg2 :: pgs' =>
          pages_are_contiguous pgs ∧
          pg1.(page_loc) +ₗ (page_size_in_bytes_Z pg1.(page_sz)) = pg2.(page_loc)
      end
  end.

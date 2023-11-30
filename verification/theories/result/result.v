From refinedrust Require Import typing.

Notation Ok x := (inl x) (only parsing).
Notation Err x := (inr x) (only parsing).

Notation result A B := (sum A B) (only parsing).


Notation "'<#>' x" := (fmap (M := list) PlaceIn x) (at level 30).

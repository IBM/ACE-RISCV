From stdpp Require Import base.
From stdpp Require Import options.

Section wip.
Context (process:Type) (state:Type).
Context (loc:Set) (value:Set).
Context (lookup:state->loc->option value).
Context (run:process->state->(process * state)).
Definition something (p:process) (owns:loc->Prop) (declassified:loc->Prop)
  := forall (s1 s2:state),
    (forall (l:loc), owns l \/ declassified l -> lookup s1 l = lookup s2 l) ->
    forall (l:loc),
      (owns l -> lookup (snd (run p s1)) l = lookup (snd (run p s2)) l)
      /\ (~ owns l -> lookup (snd (run p s1)) l = lookup s1 l
                    /\ lookup (snd (run p s2)) l = lookup s2 l)
      /\ fst (run p s1) = fst (run p s2).

End wip.

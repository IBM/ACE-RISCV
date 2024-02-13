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


(** Notes from meeting with Wojciech:
   - we may need to investigate the system model further
   - in the above sketch, should the security monitor be modelled as a process as well?
      + yes, because it's behavior should also not be influenced by the concrete data in the state it doesn't own
        it may still access that memory, however.
   - Note: the reason why the above definition works is that hardware mechanisms + page table setup ensure that everyone but the security monitor can only access the memory they own or that was declassified
   - Problem with the model: in our system, ownership and declassification evolve over time and depend on the state
   - Problem with the model: non-determinism
 *)

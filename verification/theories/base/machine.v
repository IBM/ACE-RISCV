From refinedrust Require Import typing.

(** Configuration of the Rust abstract machine *)
Class MachineConfig := {
  (** We assume a provance ID for the memory ownership the security monitor gets passed from assembly on initialization.
    This provenance allows for access to all direct hardware memory, but not to memory that went through the Rust abstract machine (e.g. stack/heap allocated pointers).
    For now, we just use this to make sure that page token pointers don't get reduced to a more restrictive provenance; but eventually this should interface with the Radium semantics for exposed pointer-integer casts.
  *)
  machine_memory_prov : Z
}.

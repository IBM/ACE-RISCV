From refinedrust Require Import typing.

Record memory_layout : Type := mk_memory_layout {
  conf_start : loc;
  conf_end : loc;
  non_conf_start : loc;
  non_conf_end : loc;
}.

Global Instance memory_layout_inhabited : Inhabited memory_layout :=
  populate (mk_memory_layout inhabitant inhabitant inhabitant inhabitant).

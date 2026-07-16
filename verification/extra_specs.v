From Ltac2 Require Import Notations.
Ltac2 Set start_function_hook as old_start_function_hook :=
  fun () =>
    Control.plus (fun () =>
    match! goal with
    | [ _ : CACHED
          (use_enum_layout_alg error_Error_els = Some _)
        |- _ ] =>
        let h := Fresh.in_goal @_Hop in
        assert
          (ty_has_op_type
             (error_Error_ty -[] -[])
             (use_op_alg' error_Error_els))
          as $h
        > [ ltac1:(solve_ty_has_op_type)
          | let hop := Control.hyp h in
            ltac1:(hop |- enter_cache hop) (Ltac1.of_constr hop)
          ]
    end) (fun _ => ());
    old_start_function_hook ()
  .

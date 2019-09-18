Require Import Abstraction.
Ltac
 monad_simpl :=
  repeat
   match goal with
   | |- proc_spec _ (Bind (Ret _) _) _ _ =>
         eapply spec_exec_equiv; [ apply monad_left_id |  ]
   | |- proc_spec _ (Bind (Bind _ _) _) _ _ =>
         eapply spec_exec_equiv; [ apply monad_assoc |  ]
   end.

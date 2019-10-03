Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqUWkUYg"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Proc Abstraction.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqN0Djid"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqkKvFf6"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Ltac
 monad_simpl :=
  repeat
   match goal with
   | |- proc_spec _ (Bind (Ret _) _) _ _ =>
         eapply spec_exec_equiv; [ apply monad_left_id |  ]
   | |- proc_spec _ (Bind (Bind _ _) _) _ _ =>
         eapply spec_exec_equiv; [ apply monad_assoc |  ]
   end.
(* Auto-generated comment: Succeeded. *)


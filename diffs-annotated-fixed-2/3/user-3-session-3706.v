Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqEagoXM"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Helpers.Helpers.
Require Import Proc.
Require Import ProcTheorems.
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
Ltac
 step_proc_basic :=
  match goal with
  | |- forall _, _ => intros; step_proc_basic
  | |- proc_spec _ (Ret _) _ _ => eapply ret_spec
  | |- proc_spec _ _ _ _ =>
        monad_simpl; eapply proc_spec_rx; [ solve [ eauto ] |  ]
  | H:proc_spec _ ?p _ _
    |- proc_spec _ ?p _ _ =>
        eapply proc_spec_weaken; [ eapply H | unfold spec_impl ]
  end.
Ltac
 simplify :=
  simpl; cbn[pre post recovered] in *;
   repeat
    match goal with
    | H:_ /\ _ |- _ => destruct H
    | |- rec_wipe _ _ _ => eauto
    | |- forall _, _ => intros
    | |- exists _ : unit, _ => exists tt
    | |- _ /\ _ => split; [ solve [ trivial ] |  ]
    | |- _ /\ _ => split; [  | solve [ trivial ] ]
    | _ => solve [ trivial ]
    | _ => progress subst
    | _ => progress autounfold in *
    end.
Ltac
 step_proc :=
  intros;
   match goal with
   | |- proc_spec _ (Ret _) _ _ => eapply ret_spec
   | |- proc_spec _ _ _ _ =>
         monad_simpl; eapply proc_spec_rx; [ solve [ eauto ] |  ]
   | H:proc_spec _ ?p _ _
     |- proc_spec _ ?p _ _ =>
         eapply proc_spec_weaken; [ eapply H | unfold spec_impl ]
   end; intros; simplify.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq8LvvnA"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq8x4vEH"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
(* Auto-generated comment: Succeeded. *)


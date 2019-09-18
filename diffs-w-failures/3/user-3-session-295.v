Require Import Spec.Proc Spec.ProcTheorems.
From Tactical Require Import Propositional.
From Tactical Require Import ExistentialVariants.
From Tactical Require Import Misc.
Require Import Spec.Hoare.
From Transitions Require Import Relations Rewriting.
Import RelationNotations.
Ltac
 spec_intros :=
  intros; (first [ eapply rspec_intros | eapply hspec_intros ]); intros.
Ltac
 monad_simpl :=
  repeat
   match goal with
   | |- proc_hspec _ (Bind (Ret _) _) _ =>
         eapply proc_hspec_exec_equiv; [ apply monad_left_id |  ]
   | |- proc_hspec _ (Bind (Bind _ _) _) _ =>
         eapply proc_hspec_exec_equiv; [ apply monad_assoc |  ]
   end.
Ltac
 step_proc :=
  intros;
   match goal with
   | |- proc_hspec _ (Ret _) _ => eapply ret_hspec
   | |- proc_hspec _ _ _ =>
         monad_simpl; eapply proc_hspec_rx; [ solve [ eauto ] |  ]
   | H:proc_hspec _ ?p _
     |- proc_hspec _ ?p _ =>
         eapply proc_hspec_impl; [ unfold spec_impl | eapply H ]
   end; intros; simpl; cbn[pre post alternate] in *;
   repeat
    match goal with
    | H:_ /\ _ |- _ => destruct H
    | |- rec_noop _ _ _ => eauto
    | |- forall _, _ => intros
    | |- exists _ : unit, _ => exists tt
    | |- _ /\ _ => split; [ solve [ trivial ] |  ]
    | |- _ /\ _ => split; [  | solve [ trivial ] ]
    | _ => solve [ trivial ]
    | _ => progress subst
    | _ => progress autounfold in *
    end.
Ltac
 finish :=
  repeat
   match goal with
   | _ => solve_false
   | _ => congruence
   | _ => solve [ intuition subst; eauto; try congruence ]
   | _ =>
       descend; intuition eauto;
        lazymatch goal with
        | |- proc_hspec _ _ _ => idtac
        | |- proc_rspec _ _ _ _ => idtac
        | _ => fail
        end
   end.

Require Import List.
Ltac
 break_and :=
  match goal with
  | H:_ /\ _ |- _ => destruct H
  | |- _ /\ _ => constructor
  end.
Ltac
 break_pair :=
  match goal with
  | H:_ * _ |- _ => destruct H
  | |- _ * _ => constructor
  end.
Ltac break_or := match goal with
                 | H:_ \/ _ |- _ => destruct H
                 end.
Ltac break_exists := match goal with
                     | H:exists _, _ |- _ => destruct H
                     end.
Ltac
 solve_by_inversion := match goal with
                       | H:_ |- _ => solve [ inversion H ]
                       end.
Ltac obvious := subst; intuition auto; solve_by_inversion.
Require Import List.
Require Import String.
Ltac inj1 := match goal with
             | H:_ |- _ => injection H; clear H; intros
             end.
Ltac inj := repeat inj1.
Ltac inv H := inversion H; clear H; subst.
Ltac inversion_then T := match goal with
                         | H:_ |- _ => inv H; T
                         end.
Ltac
 break_match_hyp :=
  match goal with
  | H:context [ match ?X with
                | _ => _
                end ]
    |- _ =>
        match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
        end
  end.
Ltac
 break_match_goal :=
  match goal with
  | |- context [ match ?X with
                 | _ => _
                 end ] =>
        match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
        end
  end.
Ltac break_match := break_match_goal || break_match_hyp.
Lemma modus_ponens : forall A B, A -> (A -> B) -> B.
Proof.
intuition.
Qed.
Ltac exploit H := eapply modus_ponens; [ eapply H | intro ].
Ltac
 erewrite_hyp_then K :=
  match goal with
  | H:_ |- _ => erewrite H; (solve [ K ])
  end.
Ltac eapply_in_hyp lemma := match goal with
                            | H:_ |- _ => eapply lemma in H
                            end.
Ltac
 eapply_hyp_then K := match goal with
                      | H:_ |- _ => eapply H; (solve [ K ])
                      end.
Ltac eapply_hyp := eapply_hyp_then eauto.
Import ListNotations.
Import ListNotations.
Inductive Zip {A} {B} : list A -> list B -> list (A * B) -> Prop :=
  | ZipNil : Zip [] [] []
  | ZipCons :
      forall a b arest brest zrest,
      Zip arest brest zrest ->
      Zip (a :: arest) (b :: brest) ((a, b) :: zrest).
Fixpoint zip {A B} (a : list A) (b : list B) : option (list (A * B)) :=
  match a, b with
  | [], [] => Some []
  | ahead :: atail, bhead :: btail =>
      match zip atail btail with
      | Some tail => Some ((ahead, bhead) :: tail)
      | None => None
      end
  | _, _ => None
  end.
Definition Id := string.
Definition id_eq_dec := string_dec.

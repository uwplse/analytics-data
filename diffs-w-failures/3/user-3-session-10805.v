Ltac
 simpl_match :=
  let repl_match_goal d d' :=
   replace d with d';
    lazymatch goal with
    | |- context [ match d' with
                   | _ => _
                   end ] => fail
    | _ => idtac
    end
  in
  let repl_match_hyp H d d' :=
   replace d with d' in H;
    lazymatch type of H with
    | context [ match d' with
                | _ => _
                end ] => fail
    | _ => idtac
    end
  in
  match goal with
  | Heq:?d = ?d'
    |- context [ match ?d with
                 | _ => _
                 end ] => repl_match_goal d d'
  | Heq:?d' = ?d
    |- context [ match ?d with
                 | _ => _
                 end ] => repl_match_goal d d'
  | Heq:?d = ?d', H:context [ match ?d with
                              | _ => _
                              end ] |- _ => repl_match_hyp H d d'
  | Heq:?d' = ?d, H:context [ match ?d with
                              | _ => _
                              end ] |- _ => repl_match_hyp H d d'
  end.
Ltac
 destruct_matches_in e :=
  lazymatch e with
  | context [ match ?d with
              | _ => _
              end ] => destruct_matches_in d
  | _ => destruct e eqn:?; intros
  end.
Ltac
 destruct_all_matches :=
  repeat
   (try simpl_match;
     try
      match goal with
      | |- context [ match ?d with
                     | _ => _
                     end ] => destruct_matches_in d
      | H:context [ match ?d with
                    | _ => _
                    end ] |- _ => destruct_matches_in d
      end); subst; try congruence; auto.
Ltac
 destruct_nongoal_matches :=
  repeat
   (try simpl_match;
     try
      match goal with
      | H:context [ match ?d with
                    | _ => _
                    end ] |- _ => destruct_matches_in d
      end); subst; try congruence; auto.
Ltac
 destruct_goal_matches :=
  repeat
   (try simpl_match;
     match goal with
     | |- context [ match ?d with
                    | _ => _
                    end ] => destruct_matches_in d
     end); try congruence; auto.
Ltac
 destruct_tuple :=
  match goal with
  | H:context [ let '(a, b) := ?p in _ ]
    |- _ => let a := fresh a in
            let b := fresh b in
            destruct p as [a b]
  | |- context [ let '(a, b) := ?p in _ ] =>
        let a := fresh a in
        let b := fresh b in
        destruct p as [a b]
  end.
Tactic Notation "destruct" "matches" "in" "*" := destruct_all_matches.
Tactic Notation "destruct" "matches" "in" "*|-" := destruct_nongoal_matches.
Tactic Notation "destruct" "matches" := destruct_goal_matches.
Require Import Arith.
Require Import Bool.
Require Import List.
Require Import EquivDec.
Set Implicit Arguments.
Definition maybe_holds T (p : T -> Prop) : option T -> Prop :=
  fun mt => match mt with
            | Some t => p t
            | None => True
            end.
Theorem holds_in_none_eq :
  forall T (p : T -> Prop) mt, mt = None -> maybe_holds p mt.
Proof.
(intros; subst).
(simpl; auto).
Qed.
Theorem holds_in_some :
  forall T (p : T -> Prop) (v : T), p v -> maybe_holds p (Some v).
Proof.
(simpl; auto).
Qed.
Theorem holds_in_some_eq :
  forall T (p : T -> Prop) (v : T) mt, mt = Some v -> p v -> maybe_holds p mt.
Proof.
(intros; subst).
(simpl; auto).
Qed.
Theorem holds_some_inv_eq :
  forall T (p : T -> Prop) mt v, mt = Some v -> maybe_holds p mt -> p v.
Proof.
(intros; subst).
auto.
Qed.
Theorem pred_weaken :
  forall T (p p' : T -> Prop) mt,
  maybe_holds p mt -> (forall t, p t -> p' t) -> maybe_holds p' mt.
Proof.
(unfold maybe_holds; destruct mt; eauto).
Qed.
Notation "m ?|= F" := (maybe_holds F m) (at level 20, F  at level 50).
Definition missing {T} : T -> Prop := fun _ => False.
Theorem pred_missing :
  forall T (p : T -> Prop) mt, mt ?|= missing -> mt ?|= p.
Proof.
(unfold missing; intros).
(eapply pred_weaken; eauto).
contradiction.
Qed.

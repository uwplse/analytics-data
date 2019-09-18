Require Import Helpers.Helpers.
Require Import Helpers.Helpers.
Require Import Proc.
Require Import Proc.
Require Import ProcTheorems.
Require Import Abstraction.
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
Hint Constructors rexec: core.
Hint Constructors exec: core.
Hint Constructors exec_recover: core.
Theorem clos_refl_trans_1n_unit_tuple :
  forall `(R : unit * A -> unit * A -> Prop) x y u u',
  Relation_Operators.clos_refl_trans_1n R (u, x) (u', y) ->
  Relation_Operators.clos_refl_trans_1n (fun x y => R (tt, x) (tt, y)) x y.
Proof.
(intros).
(destruct u, u').
(remember (tt, x)).
(remember (tt, y)).
generalize dependent x.
generalize dependent y.
(induction H; intuition subst).
-
(inversion Heqp; subst).
constructor.
-
(destruct y).
(destruct u).
(especialize IHclos_refl_trans_1n; intuition).
(especialize IHclos_refl_trans_1n; intuition).
(econstructor; eauto).
Qed.
Definition proc_loopspec `(spec : Specification A unit unit State)
  `(rec' : proc unit) `(rec : proc unit) (abs : Abstraction State) :=
  forall a w state,
  abstraction abs w state ->
  pre (spec a state) ->
  forall rv rv' w',
  Relation_Operators.clos_refl_trans_1n
    (fun '(_, w) '(rv', w') => rexec rec' rec w (Recovered rv' w')) 
    (rv, w) (rv', w') ->
  forall rv'' w'',
  exec rec' w' (Finished rv'' w'') ->
  exists state'',
    abstraction abs w'' state'' /\ post (spec a state) rv'' state''.
Definition idempotent `(spec : Specification A T unit State) :=
  forall a state,
  pre (spec a state) ->
  forall v state',
  recovered (spec a state) v state' ->
  exists a',
    pre (spec a' state') /\
    (forall rv state'',
     post (spec a' state') rv state'' -> post (spec a state) rv state'').
Theorem idempotent_loopspec :
  forall `(rec : proc unit) `(rec' : proc unit)
    `(spec : Specification A unit unit State) (abs : Abstraction State),
  forall Hspec : proc_spec spec rec' rec abs,
  idempotent spec -> proc_loopspec spec rec' rec abs.
Proof.
(unfold proc_loopspec; intros).
(apply clos_refl_trans_1n_unit_tuple in H2).
(repeat match goal with
        | u:unit |- _ => destruct u
        end).
generalize dependent a.
generalize dependent state.
(induction H2; intros).
-
(eapply RExec in H3).
(eapply Hspec in H3; eauto).
-
(eapply Hspec in H0; simpl in *; safe_intuition repeat deex; eauto).
(eapply H in H4; eauto; repeat deex).
(specialize (H4 _ _ _); repeat deex; intuition).
specialize (IHclos_refl_trans_1n _ _ _ _).
safe_intuition repeat deex; eauto.
Qed.
Theorem compose_recovery :
  forall `(spec : Specification A'' T unit State)
    `(rspec : Specification A' unit unit State)
    `(spec' : Specification A T unit State) `(p : proc T) 
    `(rec : proc unit) `(rec' : proc unit) `(abs : Abstraction State),
  forall (Hspec : proc_spec spec p rec abs)
    (Hrspec : proc_loopspec rspec rec' rec abs)
    (Hspec_spec' : forall (a : A) state,
                   pre (spec' a state) ->
                   exists a'' : A'',
                     pre (spec a'' state) /\
                     (forall v state',
                      post (spec a'' state) v state' ->
                      post (spec' a state) v state') /\
                     (forall v state',
                      recovered (spec a'' state) v state' ->
                      exists a',
                        pre (rspec a' state') /\
                        (forall v' state'',
                         post (rspec a' state') v' state'' ->
                         recovered (spec' a state) v' state''))),
  proc_spec spec' p (_ <- rec; rec') abs.
Proof.
(intros).
(unfold proc_spec; intros).
(eapply Hspec_spec' in H0; safe_intuition; repeat deex).
clear Hspec_spec'.
(destruct r).
-
(match goal with
 | Hexec:rexec p _ _ _
   |- _ => eapply rexec_finish_any_rec in Hexec; eapply Hspec in Hexec
 end; simpl in *; intuition repeat deex; eauto).
-
inv_rexec.
(match goal with
 | Hexec:exec_recover _ _ _ _ |- _ => eapply exec_recover_bind_inv in Hexec
 end; repeat deex).
(match goal with
 | Hexec:exec_recover rec _ _ _ |- _ => eapply RExecCrash in Hexec; eauto
 end; repeat deex).
(match goal with
 | Hexec:rexec p _ _ _ |- _ => eapply Hspec in Hexec
 end; simpl in *; safe_intuition repeat deex; eauto).
(eapply H3 in H6; repeat deex).
(match goal with
 | Hexec:exec rec' _ _ |- _ => eapply Hrspec in Hexec
 end; simpl in *; safe_intuition repeat deex; eauto).
Qed.
Theorem rec_wipe_compose :
  forall `(rec : proc unit) `(rec2 : proc unit) `(abs1 : Abstraction State1)
    (wipe1 : State1 -> State1 -> Prop)
    `(spec : Specification A unit unit State1)
    `(abs2 : LayerAbstraction State1 State2)
    (wipe2 : State2 -> State2 -> Prop),
  rec_wipe rec abs1 wipe1 ->
  proc_loopspec spec rec2 rec abs1 ->
  forall
    Hspec : forall state0 state0' state,
            abstraction abs2 state0 state0' ->
            wipe1 state0 state ->
            exists a,
              pre (spec a state) /\
              (forall state' r,
               post (spec a state) r state' ->
               exists state2',
                 wipe2 state0' state2' /\ abstraction abs2 state' state2'),
  rec_wipe (_ <- rec; rec2) (abstraction_compose abs1 abs2) wipe2.
Proof.
(unfold rec_wipe; intros).
(eapply spec_abstraction_compose; simpl).
(eapply compose_recovery; eauto).
(destruct a; simpl; intuition).
(descend; intuition eauto).
specialize (Hspec _ _ _ _ _).
(repeat deex).
(descend; intuition eauto).
Qed.
Definition Semantics State T := State -> T -> State -> Prop.
Definition pre_step {opT} {State} (bg_step : State -> State -> Prop)
  (step : forall `(op : opT T), Semantics State T) :
  forall T (op : opT T), Semantics State T :=
  fun T (op : opT T) state v state'' =>
  exists state', bg_step state state' /\ step op state' v state''.
Definition post_step {opT} {State}
  (step : forall `(op : opT T), Semantics State T)
  (bg_step : State -> State -> Prop) :
  forall T (op : opT T), Semantics State T :=
  fun T (op : opT T) state v state'' =>
  exists state', step op state v state' /\ bg_step state' state''.
Definition op_spec `(sem : Semantics State T) :
  Specification unit T unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun v state' => sem state v state';
  recovered := fun r state' =>
               r = tt /\ (state' = state \/ (exists v, sem state v state')) |}.
Definition no_wipe {State} (state state' : State) : Prop := state' = state.
Hint Unfold no_wipe: core.
Definition no_crash {State} (state state' : State) : Prop := False.
Hint Unfold no_crash: core.

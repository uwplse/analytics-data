Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqdnPYOo"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Coq.Strings.String.
Import StringSyntax.
Require Import Helpers.Helpers.
Require Import Proc.
Require Import ProcTheorems.
Record LayerAbstraction State1 State2 :={abstraction :
                                          State1 -> State2 -> Prop}.
Definition Abstraction State := LayerAbstraction world State.
Definition abstraction_compose `(abs1 : Abstraction State1)
  `(abs2 : LayerAbstraction State1 State2) :=
  {|
  abstraction := fun w state' =>
                 exists state,
                   abstraction abs2 state state' /\ abstraction abs1 w state |}.
Definition IdAbstraction State : LayerAbstraction State State :=
  {| abstraction := fun state state' => state' = state |}.
Record SpecProps T R State :=
 Spec {pre : Prop; post : T -> State -> Prop; recovered : R -> State -> Prop}.
Definition Specification A T R State := A -> State -> SpecProps T R State.
Definition proc_spec `(spec : Specification A T R State) 
  `(p : proc T) `(rec : proc R) `(abs : Abstraction State) :=
  forall a w state,
  abstraction abs w state ->
  pre (spec a state) ->
  forall r,
  rexec p rec w r ->
  match r with
  | RFinished v w' =>
      exists state',
        abstraction abs w' state' /\ post (spec a state) v state'
  | Recovered v w' =>
      exists state',
        abstraction abs w' state' /\ recovered (spec a state) v state'
  end.
Definition spec_impl `(spec1 : Specification A' T R State)
  `(spec2 : Specification A T R State) :=
  forall a state,
  pre (spec2 a state) ->
  exists a',
    pre (spec1 a' state) /\
    (forall v state',
     post (spec1 a' state) v state' -> post (spec2 a state) v state') /\
    (forall rv state',
     recovered (spec1 a' state) rv state' ->
     recovered (spec2 a state) rv state').
Theorem proc_spec_weaken :
  forall `(spec1 : Specification A T R State)
    `(spec2 : Specification A' T R State) `(p : proc T) 
    `(rec : proc R) (abs : Abstraction State),
  proc_spec spec1 p rec abs ->
  spec_impl spec1 spec2 -> proc_spec spec2 p rec abs.
Proof.
(unfold proc_spec at 2; intros).
(eapply H0 in H2; eauto; repeat deex).
(eapply H in H3; eauto).
(destruct r; simpl in *; repeat deex; intuition eauto).
Qed.
Hint Resolve tt: core.
Inductive Marker (s : string) {T} (p : proc T) : Type :=
    mark : _.
Hint Resolve mark: core.
Theorem proc_spec_rx :
  forall `(spec : Specification A T R State) `(p : proc T) 
    `(rec : proc R) `(rx : T -> proc T')
    `(spec' : Specification A' T' R State) `(abs : Abstraction State),
  proc_spec spec p rec abs ->
  (forall a' state,
   pre (spec' a' state) ->
   exists a,
     pre (spec a state) /\
     (forall r state',
      recovered (spec a state) r state' ->
      forall L : Marker "recovered condition" p,
      recovered (spec' a' state) r state') /\
     (forall r,
      forall Lproc : Marker "after" p,
      proc_spec
        (fun (_ : unit) state' =>
         {|
         pre := post (spec a state) r state';
         post := fun r state'' => post (spec' a' state) r state'';
         recovered := fun r state'' => recovered (spec' a' state) r state'' |})
        (rx r) rec abs)) -> proc_spec spec' (Bind p rx) rec abs.
Proof.
(unfold proc_spec at 3; intros).
inv_rexec.
-
inv_exec.
(match goal with
 | Hexec:exec p _ _ |- _ => eapply RExec in Hexec
 end).
(eapply H0 in H2; repeat deex).
(eapply H in H9; simpl in *; safe_intuition repeat deex; eauto).
(match goal with
 | Hexec:exec (rx _) _ _
   |- _ => eapply RExec in Hexec; eapply H4 in Hexec; eauto
 end).
-
inv_exec.
+
(match goal with
 | Hexec:exec p _ _ |- _ => eapply RExec in Hexec
 end).
(eapply H0 in H2; repeat deex).
(eapply H in H10; simpl in *; safe_intuition repeat deex; eauto).
(match goal with
 | Hexec:exec (rx _) _ _
   |- _ => eapply RExecCrash in Hexec; eauto; eapply H4 in Hexec; eauto
 end).
+
(assert (Hexec : exec p w' (Crashed w')) by (constructor; eauto)).
(eapply RExecCrash in Hexec; eauto).
(eapply H0 in H2; repeat deex).
(eapply H in Hexec; simpl in *; safe_intuition repeat deex; eauto).
+
inv_exec.
(match goal with
 | Hexec:exec p _ _ |- _ => eapply RExec in Hexec
 end).
(eapply H0 in H2; repeat deex).
(eapply H in H10; simpl in *; safe_intuition repeat deex; eauto).
(match goal with
 | Hexec:exec (rx _) _ _
   |- _ =>
       apply ExecCrashEnd in Hexec; eapply RExecCrash in Hexec; eauto;
        eapply H4 in Hexec; eauto
 end).
+
(match goal with
 | Hexec:exec p _ _ |- _ => eapply RExecCrash in Hexec; eauto
 end).
(eapply H0 in H2; repeat deex).
(eapply H in H10; simpl in *; safe_intuition repeat deex; eauto).
Qed.
Theorem spec_intros :
  forall `(spec : Specification A T R State) `(p : proc T) 
    `(rec : proc R) `(abs : Abstraction State),
  (forall a state0,
   pre (spec a state0) ->
   proc_spec
     (fun (_ : unit) state =>
      {|
      pre := state = state0;
      post := fun r state' => post (spec a state) r state';
      recovered := fun r state' => recovered (spec a state) r state' |}) p
     rec abs) -> proc_spec spec p rec abs.
Proof.
(unfold proc_spec at 2; intros).
(apply H in H1).
(eapply H1 in H2; eauto).
(simpl in *; eauto).
Qed.
Ltac spec_intros := intros; eapply spec_intros; intros.
Ltac
 spec_case pf :=
  eapply proc_spec_weaken; [ solve [ apply pf ] | unfold spec_impl ].
Theorem spec_exec_equiv :
  forall `(spec : Specification A T R State) (p p' : proc T) 
    `(rec : proc R) `(abs : Abstraction State),
  exec_equiv p p' -> proc_spec spec p' rec abs -> proc_spec spec p rec abs.
Proof.
(unfold proc_spec; intros).
(eapply H0; eauto).
(eapply rexec_equiv; eauto).
(symmetry; auto).
Qed.
Definition rec_wipe `(rec : proc R) `(abs : Abstraction State)
  (wipe : State -> State -> Prop) :=
  forall T (v : T),
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' => r = v /\ state' = state;
     recovered := fun _ state' => wipe state state' |}) 
    (Ret v) rec abs.
Theorem ret_spec :
  forall `(abs : Abstraction State) (wipe : State -> State -> Prop)
    `(spec : Specification A T R State) (v : T) (rec : proc R),
  rec_wipe rec abs wipe ->
  (forall a state,
   pre (spec a state) ->
   forall L : Marker "post" (Ret v),
   post (spec a state) v state /\
   (forall state',
    wipe state state' -> forall r, recovered (spec a state) r state')) ->
  proc_spec spec (Ret v) rec abs.
Proof.
(intros).
(unfold proc_spec; intros).
(eapply H in H3; simpl in *; eauto).
(eapply H0 in H2; eauto).
(destruct r; intuition eauto).
Qed.
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
        eapply proc_spec_weaken;
         [ eapply H
         | unfold spec_impl;
            (let L := fresh "L" in
             pose proof (mark "using spec for" p) as L) ]
  | |- proc_spec _ _ _ _ =>
        eapply proc_spec_weaken; [ solve [ eauto ] | unfold spec_impl ]
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqjEfwtu"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqsN6Kan"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
(* Auto-generated comment: Succeeded. *)


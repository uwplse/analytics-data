Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqac4Cqz"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Set Silent.
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
Unset Silent.
Set Diffs "off".
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Set Printing Width 78.
Inductive Marker (s : string) {T} (p : proc T) : Type :=
    mark : _.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqEIgS8G"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqImLfN4"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Hint Resolve mark: core.
Timeout 1 Check @Tauto.rxcnf.
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
      proc_spec
        (fun (_ : unit) state' =>
         {|
         pre := forall L : Marker "post condition" p,
                post (spec a state) r state';
         post := fun r state'' => post (spec' a' state) r state'';
         recovered := fun r state'' => recovered (spec' a' state) r state'' |})
        (rx r) rec abs)) -> proc_spec spec' (Bind p rx) rec abs.
Set Silent.
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
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(match goal with
 | Hexec:exec (rx _) _ _
   |- _ => eapply RExec in Hexec; eapply H4 in Hexec; simpl; eauto
 end).
Set Silent.
-
inv_exec.
+
(match goal with
 | Hexec:exec p _ _ |- _ => eapply RExec in Hexec
 end).
(eapply H0 in H2; repeat deex).
(eapply H in H10; simpl in *; safe_intuition repeat deex; eauto).
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(match goal with
 | Hexec:exec (rx _) _ _
   |- _ =>
       eapply RExecCrash in Hexec; eauto; eapply H4 in Hexec; simpl; eauto
 end).
Set Silent.
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

Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqVOSw5L"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
Require Import Coq.Strings.String.
Unset Silent.
Import StringSyntax.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqrFgtUU"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqIuiiUa"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Silent.
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
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Inductive Marker : string -> Type :=
    mark : forall s, Marker s.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqaM0FGo"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqulu2Yx"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
      Marker "recovered condition" -> recovered (spec' a' state) r state') /\
     (forall r,
      Marker "post condition" ->
      proc_spec
        (fun (_ : unit) state' =>
         {|
         pre := post (spec a state) r state';
         post := fun r state'' => post (spec' a' state) r state'';
         recovered := fun r state'' => recovered (spec' a' state) r state'' |})
        (rx r) rec abs)) -> proc_spec spec' (Bind p rx) rec abs.
Proof.
Set Silent.
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

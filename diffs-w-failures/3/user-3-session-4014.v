Require Import POCS.
Require Import Lab0.HeapVariablesAPI.
Module HeapExamples (vars: VarsAPI).
Definition swapXY : proc unit :=
  x <- vars.read VarX;
  y <- vars.read VarY; _ <- vars.write VarX y; _ <- vars.write VarY x; Ret tt.
Inductive ProcMarker {T} (p : proc T) : Type :=
    AProc : _.
Definition change_marker {T'} (p' : proc T') `(@ProcMarker T p) :
  ProcMarker p' := AProc p'.
Notation "p" := (ProcMarker p) (at level 100, only printing).
Theorem swapXY_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' = mkState (StateY state) (StateX state) (StateZ state);
     recovered := fun _ state' => True |}) swapXY vars.recover vars.abstr.
Proof.
(match goal with
 | |- proc_spec _ ?p _ _ => pose proof (AProc p) as Hbefore
 end).
(unfold swapXY).
monad_simpl.
(match goal with
 | |- proc_spec _ ?p _ _ => apply (change_marker p) in Hbefore
 end).
(eapply proc_spec_rx; [ solve [ eauto ] |  ]).
(cbn[pre post recovered]).
(let state := fresh "state" in
 intros ? state Hpre).
exists tt.

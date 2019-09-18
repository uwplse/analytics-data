Require Import Helpers.RelationAlgebra.
Require Import List.
#[global]Set Implicit Arguments.
#[global]Generalizable Variables T R Op State.
#[global]Set Printing Projections.
Set Warnings "-undeclared-scope".
Import RelationNotations.
Inductive proc (Op : Type -> Type) (T : Type) : Type :=
  | Call : forall op : Op T, _
  | Ret : forall v : T, _
  | Bind : forall (T1 : Type) (p1 : proc Op T1) (p2 : T1 -> proc Op T), _.
Arguments Call {Op} {T}.
Arguments Ret {Op} {T} v.
Inductive proc_seq (Op : Type -> Type) (R : Type) : Type :=
  | Seq_Nil : _
  | Seq_Bind :
      forall (T : Type) (p : proc Op T) (rx : T + R -> proc_seq Op R), _.
Arguments Seq_Nil {Op} {R}.
Arguments Seq_Bind {Op} {R} {T}.
Definition OpSemantics Op State := forall T, Op T -> relation State State T.
Definition CrashSemantics State := relation State State unit.
Record Dynamics Op State :={step : OpSemantics Op State;
                            crash_step : CrashSemantics State}.
Section Dynamics.
Context `(sem : Dynamics Op State).
Notation proc := (proc Op).
Notation proc_seq := (proc_seq Op).
Notation step := sem.(step).
Notation crash_step := sem.(crash_step).
Fixpoint exec {T} (p : proc T) : relation State State T :=
  match p with
  | Ret v => pure v
  | Call op => step op
  | Bind p p' => v <- exec p; exec (p' v)
  end.
Fixpoint exec_crash {T} (p : proc T) : relation State State unit :=
  match p with
  | Ret v => crash_step
  | Call op => crash_step + (step op;; crash_step)
  | Bind p p' => exec_crash p + (v <- exec p; exec_crash (p' v))
  end.
Definition exec_recover {R} (rec : proc R) : relation State State R :=
  seq_star (exec_crash rec);; exec rec.
Definition exec_recover_unfold {R} (rec : proc R) :
  exec_recover rec = seq_star (exec_crash rec);; exec rec := eq_refl.
Definition rexec {T} {R} (p : proc T) (rec : proc R) :
  relation State State R := exec_crash p;; exec_recover rec.
Definition rexec_unfold {T} {R} (p : proc T) (rec : proc R) :
  rexec p rec = exec_crash p;; exec_recover rec := eq_refl.
Definition exec_or_rexec {T} {R} (p : proc T) (rec : proc R) :
  relation State State (T + R) :=
  (v <- exec p; pure (inl v)) + (v <- rexec p rec; pure (inr v)).
Fixpoint exec_seq {R} (p : proc_seq R) (rec : proc R) :
relation State State (list {X : Type & X}) :=
  match p with
  | Seq_Nil => pure nil
  | Seq_Bind p f => v <- exec_or_rexec p rec; l <- exec_seq (f v) rec;
      pure (existT _ _ v :: l)
  end.
Lemma exec_seq_unfold {R} (p : proc_seq R) (rec : proc R) :
  exec_seq p rec =
  match p with
  | Seq_Nil => pure nil
  | Seq_Bind p f => v <- exec_or_rexec p rec; l <- exec_seq (f v) rec;
      pure (existT _ _ v :: l)
  end.
Proof.
(destruct p; auto).
Qed.
End Dynamics.
Module ProcNotations.
Delimit Scope proc_scope with proc.
Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
  (at level 54, right associativity) : proc_scope.
End ProcNotations.

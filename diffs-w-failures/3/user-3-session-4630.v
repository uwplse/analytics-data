Time From Armada Require Import Spec.Proc.
Time Set Implicit Arguments.
Time
Class Injectable (Op1 Op : Type -> Type) :=
    inject : forall T, Op1 T -> Op T.
Time Arguments inject {Op1} {Op} {_} {T}.
Time
Fixpoint lift Op1 Op {i : Injectable Op1 Op} T (p : proc Op1 T) : 
proc Op T :=
  match p with
  | Call op => Call (inject op)
  | Ret v => Ret v
  | Bind p1 p2 => Bind (lift p1) (fun v => lift (p2 v))
  | Loop body init => Loop (fun v => lift (body v)) init
  | Spawn p => Spawn (lift p)
  | Unregister => Unregister
  | Wait => Wait
  end.
Time Module OpSums.
Time
Inductive OpSum (Op1 Op2 : Type -> Type) : Type -> Type :=
  | Inl : forall T, Op1 T -> OpSum Op1 Op2 T
  | Inr : forall T, Op2 T -> OpSum Op1 Op2 T.
Time Arguments Inl {Op1} {Op2} {T}.
Time Arguments Inr {Op1} {Op2} {T}.
Time Infix "\226\138\149" := OpSum (at level 60).
Time
Instance Inl_inject  Op1 Op2: (Injectable Op1 (Op1 \226\138\149 Op2)) := (@Inl _ _).
Time
Instance Inr_inject  Op1 Op2: (Injectable Op2 (Op1 \226\138\149 Op2)) := (@Inr _ _).
Time End OpSums.

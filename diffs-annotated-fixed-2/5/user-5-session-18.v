Require Import String.
Definition Identifier := string.
Definition id_eq_dec := string_dec.
Inductive Term : Set :=
  | Var : Identifier -> Term
  | Eq : Term -> Term -> Term
  | Choose : Identifier -> Term -> Term.
Module Type EpsilonLogic.
Parameter (Value : Type).
Parameter (vTrue : Value).
Parameter (vFalse : Value).
Axiom (trueAndFalseDistinct : vTrue <> vFalse).
Definition Environment := Identifier -> Value.
Definition extendEnv (env : Environment) (var : Identifier)
  (newValue : Value) : Environment :=
  fun id => if id_eq_dec id var then newValue else env id.
Parameter (eval : Environment -> Term -> Value).
Axiom (evalVar : forall env id, eval env (Var id) = env id).
Axiom (evalEqTrue : forall env term, eval env (Eq term term) = vTrue).
Axiom
  (evalEqFalse : forall env t1 t2, t1 <> t2 -> eval env (Eq t1 t2) = vFalse).
Axiom
  (evalChoose :
     forall env x P,
     (exists value, eval (extendEnv env x value) P = vTrue) ->
     exists out, eval env (Eq (Choose x P) out) = vTrue).
Axiom
  (evalChooseDet :
     forall env x P Q,
     eval env P = vTrue <-> eval env Q = vTrue ->
     eval env (Choose x P) = eval env (Choose x Q)).
Definition isTheorem (t : Term) := forall env, eval env t = vTrue.
End EpsilonLogic.
Fixpoint simplify (t : Term) : Term :=
  match t with
  | Var x => Var x
  | Eq a b => Eq (simplify a) (simplify b)
  | Choose x P => Choose x (simplify P)
  end.
Theorem simplify_correct :
  forall t : Term,
  EpsilonLogic.isTheorem t <-> EpsilonLogic.isTheorem (simplify t).
(* Auto-generated comment: Succeeded. *)


Require Import String.
Require Import ZArith.
Definition Identifier := string.
Definition id_eq_dec := string_dec.
Inductive Term : Set :=
  | Var : Identifier -> Term
  | Int : Z -> Term
  | Eq : Term -> Term -> Term
  | Plus : Term -> Term -> Term
  | Times : Term -> Term -> Term
  | Minus : Term -> Term -> Term
  | Choose : Identifier -> Term -> Term.
Definition extendEnv {Value} (env : Identifier -> Value) 
  (var : Identifier) (newValue : Value) : Identifier -> Value :=
  fun id => if id_eq_dec id var then newValue else env id.
Record EpsilonLogic :=
 mkLogic {Value : Type;
          value_eq_dec : forall v1 v2 : Value, {v1 = v2} + {v1 <> v2};
          vTrue : Value;
          vFalse : Value;
          trueAndFalseDistinct : vTrue <> vFalse;
          eval : (Identifier -> Value) -> Term -> Value;
          evalVar : forall env id, eval env (Var id) = env id;
          evalIntConst :
           forall env1 env2 i, eval env1 (Int i) = eval env2 (Int i);
          evalIntInj :
           forall env i j, i <> j -> eval env (Int i) <> eval env (Int j);
          evalEqTrue :
           forall env a b,
           eval env a = eval env b <-> eval env (Eq a b) = vTrue;
          evalEqFalse :
           forall env a b,
           eval env a <> eval env b <-> eval env (Eq a b) = vFalse;
          evalPlus :
           forall env iE jE i j,
           eval env iE = eval env (Int i) ->
           eval env jE = eval env (Int j) ->
           eval env (Plus iE jE) = eval env (Int (i + j));
          evalChoose :
           forall env x P,
           (exists value, eval (extendEnv env x value) P = vTrue) ->
           eval (extendEnv env x (eval env (Choose x P))) P = vTrue;
          evalChooseDet :
           forall env x P Q,
           eval env P = vTrue <-> eval env Q = vTrue ->
           eval env (Choose x P) = eval env (Choose x Q)}.
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-08-12 18:49:08.320000.*)


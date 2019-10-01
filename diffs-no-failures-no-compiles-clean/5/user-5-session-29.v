Require Import String.
Require Import ZArith.
Require Import List.
Import ListNotations.
Definition Identifier := string.
Definition id_eq_dec := string_dec.
Inductive Term : Set :=
  | Var : Identifier -> Term
  | Bool : bool -> Term
  | Eq : Term -> Term -> Term
  | And : Term -> Term -> Term
  | Or : Term -> Term -> Term
  | Not : Term -> Term
  | If : Term -> Term -> Term -> Term
  | Int : Z -> Term
  | Plus : Term -> Term -> Term
  | Times : Term -> Term -> Term
  | Minus : Term -> Term -> Term
  | Bools : Term
  | Ints : Term
  | In : Term -> Term -> Term
  | Choose : Identifier -> Term -> Term.
Definition extendEnv {Value} (env : Identifier -> Value) 
  (var : Identifier) (newValue : Value) : Identifier -> Value :=
  fun id => if id_eq_dec id var then newValue else env id.
Record EpsilonLogic :=
 mkLogic {Value : Type;
          value_eq_dec : forall v1 v2 : Value, {v1 = v2} + {v1 <> v2};
          eval : (Identifier -> Value) -> Term -> Value;
          evalVar : forall env id, eval env (Var id) = env id;
          evalIntConst :
           forall env1 env2 i, eval env1 (Int i) = eval env2 (Int i);
          evalIntInj :
           forall env i j, i <> j -> eval env (Int i) <> eval env (Int j);
          evalBoolConst :
           forall env1 env2 b, eval env1 (Bool b) = eval env2 (Bool b);
          evalBoolInj :
           forall env, eval env (Bool true) <> eval env (Bool false);
          evalIn :
           forall env x S,
           eval env (In x S) = eval env (Bool true) \/
           eval env (In x S) = eval env (Bool false);
          evalInBools :
           forall env b S,
           eval env S = eval env Bools ->
           eval env (In b S) = eval env (Bool true) <->
           (exists b, eval env b = eval env (Bool b));
          evalEqTrue :
           forall env a b,
           eval env a = eval env b <->
           eval env (Eq a b) = eval env (Bool true);
          evalEqFalse :
           forall env a b,
           eval env a <> eval env b <->
           eval env (Eq a b) = eval env (Bool false);
          evalIfTrue :
           forall env cond a b,
           eval env cond = eval env (Bool true) ->
           eval env (If cond a b) = eval env a;
          evalIfFalse :
           forall env cond a b,
           eval env cond = eval env (Bool false) ->
           eval env (If cond a b) = eval env b;
          evalAnd :
           forall env a b,
           eval env (And a b) = eval env (If a b (Bool false));
          evalOr :
           forall env a b, eval env (Or a b) = eval env (If a (Bool true) b);
          evalNot :
           forall env a,
           eval env (Not a) = eval env (If a (Bool false) (Bool true));
          evalPlus :
           forall env iE jE i j,
           eval env iE = eval env (Int i) ->
           eval env jE = eval env (Int j) ->
           eval env (Plus iE jE) = eval env (Int (i + j));
          evalMinus :
           forall env iE jE i j,
           eval env iE = eval env (Int i) ->
           eval env jE = eval env (Int j) ->
           eval env (Minus iE jE) = eval env (Int (i - j));
          evalTimes :
           forall env iE jE i j,
           eval env iE = eval env (Int i) ->
           eval env jE = eval env (Int j) ->
           eval env (Times iE jE) = eval env (Int (i * j));
          evalChoose :
           forall env x P,
           (exists value,
              eval (extendEnv env x value) P = eval env (Bool true)) ->
           eval (extendEnv env x (eval env (Choose x P))) P =
           eval env (Bool true);
          evalChooseDet :
           forall env x P Q,
           eval env P = eval env (Bool true) <->
           eval env Q = eval env (Bool true) ->
           eval env (Choose x P) = eval env (Choose x Q)}.

Require Import String.
Require Import ZArith.
Require Import List.
Import ListNotations.
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
           (exists value, eval (extendEnv env x value) P = vTrue) ->
           eval (extendEnv env x (eval env (Choose x P))) P = vTrue;
          evalChooseDet :
           forall env x P Q,
           eval env P = vTrue <-> eval env Q = vTrue ->
           eval env (Choose x P) = eval env (Choose x Q)}.
Definition isTheorem (L : EpsilonLogic) (t : Term) :=
  forall env, L.(eval) env t = L.(vTrue).
Fixpoint identity (t : Term) : Term :=
  match t with
  | Var x => Var x
  | Int i => Int i
  | Eq a b => Eq (identity a) (identity b)
  | Plus a b => Plus (identity a) (identity b)
  | Times a b => Times (identity a) (identity b)
  | Minus a b => Minus (identity a) (identity b)
  | Choose x P => Choose x (identity P)
  end.
Theorem eval_eq_true_or_false :
  forall (L : EpsilonLogic) env (t1 t2 : Term),
  L.(eval) env (Eq t1 t2) = L.(vTrue) \/ L.(eval) env (Eq t1 t2) = L.(vFalse).
Proof.
(intros).
(destruct (L.(value_eq_dec) (L.(eval) env t1) (L.(eval) env t2)) eqn:E).
-
left.
(apply L.(evalEqTrue)).
assumption.
-
right.
(apply L.(evalEqFalse)).
assumption.
Qed.
Theorem identity_correct :
  forall (L : EpsilonLogic) (t : Term), isTheorem L (Eq t (identity t)).
Proof.
(unfold isTheorem).
(induction t; intros; simpl in *).
-
(apply evalEqTrue).
reflexivity.
-
(apply evalEqTrue).
reflexivity.
-
(apply evalEqTrue).
specialize IHt1 with env.
specialize IHt2 with env.
(apply evalEqTrue in IHt1).
(apply evalEqTrue in IHt2).
(destruct (eval_eq_true_or_false L env t1 t2)).
+
(rewrite H).
(apply evalEqTrue in H).
(rewrite H in IHt1).
(rewrite IHt1 in IHt2).
symmetry.
(apply evalEqTrue).
assumption.
+
(rewrite H).
(apply evalEqFalse in H).
(assert (eval L env (identity t1) <> eval L env (identity t2)) by congruence).
symmetry.
(apply evalEqFalse).
assumption.
Admitted.
Fixpoint free_vars (t : Term) : list Identifier :=
  match t with
  | Var x => [x]
  | Int _ => []
  | Eq a b => free_vars a ++ free_vars b
  | Plus a b => free_vars a ++ free_vars b
  | Times a b => free_vars a ++ free_vars b
  | Minus a b => free_vars a ++ free_vars b
  | Choose x P =>
      filter (fun y => if id_eq_dec x y then false else true) (free_vars P)
  end.
Axiom (fresh_var : list Identifier -> Identifier).
Axiom (fresh_var_unique : forall exclude, ~ In (fresh_var exclude) exclude).
Definition Divide (t1 : Term) (t2 : Term) :=
  let x := fresh_var (free_vars t1 ++ free_vars t2) in
  Choose x (Eq t1 (Times (Var x) t2)).
Lemma divide_test :
  forall L env, L.(eval) env (Divide (Int 6) (Int 2)) = L.(eval) env (Int 3).
Proof.
(intros).
(unfold Divide).
(match goal with
 | |- context [ Choose ?x _ ] => generalize x
 end).
intro x.
(assert
  (forall res,
   eval L env (Choose x (Eq (Int 6) (Times (Var x) (Int 2)))) = res ->
   res = eval L env (Int 3))).
{
(intros).
(assert
  (eval L
     (extendEnv env x
        (eval L env (Choose x (Eq (Int 6) (Times (Var x) (Int 2))))))
     (Eq (Int 6) (Times (Var x) (Int 2))) = L.(vTrue))).
{
(apply evalChoose).
exists (eval L env (Int 3)).
(apply evalEqTrue).
(rewrite evalTimes).
(* Auto-generated comment: Succeeded. *)


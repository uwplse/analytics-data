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
           forall env x S,
           eval env S = eval env Bools ->
           eval env (In x S) = eval env (Bool true) <->
           (exists b, eval env x = eval env (Bool b));
          evalInInts :
           forall env x S,
           eval env S = eval env Ints ->
           eval env (In x S) = eval env (Bool true) <->
           (exists i, eval env x = eval env (Int i));
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
Definition isTheorem (L : EpsilonLogic) (t : Term) :=
  forall env, L.(eval) env t = L.(eval) env (Bool true).
Fixpoint identity (t : Term) : Term :=
  match t with
  | Var x => Var x
  | Bool b => Bool b
  | Bools => Bools
  | Ints => Ints
  | In a b => In (identity a) (identity b)
  | Eq a b => Eq (identity a) (identity b)
  | And a b => And (identity a) (identity b)
  | Or a b => Or (identity a) (identity b)
  | Not a => Not (identity a)
  | If a b c => If (identity a) (identity b) (identity c)
  | Int i => Int i
  | Plus a b => Plus (identity a) (identity b)
  | Times a b => Times (identity a) (identity b)
  | Minus a b => Minus (identity a) (identity b)
  | Choose x P => Choose x (identity P)
  end.
Theorem eval_eq_true_or_false :
  forall (L : EpsilonLogic) env (t1 t2 : Term),
  L.(eval) env (Eq t1 t2) = L.(eval) env (Bool true) \/
  L.(eval) env (Eq t1 t2) = L.(eval) env (Bool false).
Proof.
(intros).
(destruct (L.(value_eq_dec) (L.(eval) env t1) (L.(eval) env t2))).
-
left.
apply -> L.(evalEqTrue).
assumption.
-
right.
apply -> L.(evalEqFalse).
assumption.
Qed.
Theorem identity_correct :
  forall (L : EpsilonLogic) (t : Term), isTheorem L (Eq t (identity t)).
Proof.
(unfold isTheorem).
(induction t; intros; simpl in *).
-
apply -> evalEqTrue.
reflexivity.
-
apply -> evalEqTrue.
reflexivity.
-
apply -> evalEqTrue.
specialize IHt1 with env.
specialize IHt2 with env.
apply <- evalEqTrue in IHt1.
apply <- evalEqTrue in IHt2.
(destruct (eval_eq_true_or_false L env t1 t2)).
+
(rewrite H).
(apply evalEqTrue in H).
(rewrite H in IHt1).
(rewrite IHt1 in IHt2).
symmetry.
apply -> evalEqTrue.
assumption.
+
(rewrite H).
(apply evalEqFalse in H).
(assert (eval L env (identity t1) <> eval L env (identity t2)) by congruence).
symmetry.
apply -> evalEqFalse.
assumption.
Admitted.
Fixpoint free_vars (t : Term) : list Identifier :=
  match t with
  | Var x => [x]
  | Int _ => []
  | Bool _ => []
  | Bools => []
  | Ints => []
  | In a b => free_vars a ++ free_vars b
  | Eq a b => free_vars a ++ free_vars b
  | And a b => free_vars a ++ free_vars b
  | Or a b => free_vars a ++ free_vars b
  | Not a => free_vars a
  | If a b c => free_vars a ++ free_vars b ++ free_vars c
  | Plus a b => free_vars a ++ free_vars b
  | Times a b => free_vars a ++ free_vars b
  | Minus a b => free_vars a ++ free_vars b
  | Choose x P =>
      filter (fun y => if id_eq_dec x y then false else true) (free_vars P)
  end.
Axiom (fresh_var : list Identifier -> Identifier).
Axiom
  (fresh_var_unique : forall exclude, ~ List.In (fresh_var exclude) exclude).
Definition Divide (t1 : Term) (t2 : Term) :=
  let x := fresh_var (free_vars t1 ++ free_vars t2) in
  Choose x (And (In (Var x) Ints) (Eq t1 (Times (Var x) t2))).
Lemma extendEnv_eq :
  forall Value env x (val : Value), (extendEnv env x val) x = val.
Proof.
(intros).
(unfold extendEnv).
(destruct (id_eq_dec x x); congruence).
Qed.
Lemma evalIntEq :
  forall L env x y, L.(eval) env (Int x) = L.(eval) env (Int y) -> x = y.
Proof.
(intros).
(destruct (Z.eq_dec x y)).
-
assumption.
-
exfalso.
refine (_ _).
(apply evalIntInj; eassumption).
Admitted.
Lemma six_div_two_unique : (forall z, 6 = z * 2 -> z = 3)%Z.
Proof.
(intros).
omega.
Qed.
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
   eval L env
     (Choose x (And (In (Var x) Ints) (Eq (Int 6) (Times (Var x) (Int 2))))) =
   res -> res = eval L env (Int 3))).
{
(intros).
(assert
  (eval L
     (extendEnv env x
        (eval L env
           (Choose x
              (And (In (Var x) Ints) (Eq (Int 6) (Times (Var x) (Int 2)))))))
     (And (In (Var x) Ints) (Eq (Int 6) (Times (Var x) (Int 2)))) =
   L.(eval) env (Bool true))).
{
(apply evalChoose).
exists (eval L env (Int 3)).
(erewrite evalBoolConst).
(rewrite evalAnd).
(eapply eq_trans).
-
(apply evalIfTrue).
(apply evalInInts).
+
reflexivity.
+
eexists.
(rewrite evalVar).
(rewrite extendEnv_eq).
(apply evalIntConst).
-
apply -> evalEqTrue.
(rewrite evalTimes with (i := 3%Z) (j := 2%Z)).
+
reflexivity.
+
(rewrite evalVar).
(rewrite extendEnv_eq).
(apply evalIntConst).
+
reflexivity.
}
(rewrite H in H0).
clear H.
(rewrite evalAnd in H0).
(match goal with
 | H:eval ?L ?env (If (In ?x ?S) _ _) = _ |- _ => destruct (evalIn L env x S)
 end).
-
(rewrite evalIfTrue in H0; auto).
(apply evalInInts in H; auto).
(destruct H).
(erewrite evalBoolConst in H0).
(rewrite <- evalEqTrue in H0).
(rewrite evalVar in H).
(rewrite extendEnv_eq in H).
(assert (x0 = 3%Z)).
{
(apply six_div_two_unique).
(eapply evalIntEq).
-
(erewrite evalTimes in H0; auto).
+
exact H0.
+
(rewrite evalVar).
(rewrite extendEnv_eq).
assumption.
}
subst.
(rewrite H).
(apply evalIntConst).
-
exfalso.
(rewrite evalIfFalse in H0).
+
refine (_ _).
(apply evalBoolInj).
(rewrite H0).
(apply evalBoolConst).
+
assumption.
}
(erewrite <- H; reflexivity).
Qed.

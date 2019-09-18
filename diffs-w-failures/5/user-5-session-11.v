Require Import Bool.
Require Import String.
Require Import List.
Require Import Impl.Programs.
Require Import Impl.Typecheck.
Require Import Definitions.WellTyped.
Require Import Definitions.Zip.
Require Import Proofs.Tactics.
Require Import Proofs.InductionSchemes.
Lemma typeOfValue_correct :
  forall val t, typeOfValue val = t -> ValueWt val t.
Proof.
(intros).
subst.
(destruct val; constructor).
Qed.
Ltac break_unit := match goal with
                   | x:unit |- _ => destruct x
                   end.
Ltac
 fwd_combine :=
  unfold combinel in *; unfold combine in *; unfold require in *;
   unfold addError in *; repeat (break_match; try discriminate); inj; subst;
   repeat break_unit.
Lemma lookupVarType_some :
  forall v vs t, lookupVarType v vs = Some t -> LookupVarType vs v t.
Proof.
(induction vs; intros).
-
discriminate.
-
(simpl in *).
break_pair.
(break_match; inj; subst; constructor; auto; congruence).
Qed.
Lemma lookupFuncType_some :
  forall f fs args ret,
  lookupFuncType f fs = Some (args, ret) -> LookupFunctionType fs f args ret.
Proof.
(induction fs; intros).
-
discriminate.
-
(simpl in *).
(repeat break_pair).
(break_match; inj; subst; constructor; auto; congruence).
Qed.
Lemma typesEq_true : forall t1 t2, typesEq t1 t2 = true -> t1 = t2.
Proof.
(destruct t1; destruct t2; try discriminate; reflexivity).
Qed.
Ltac
 exploit_typesEq :=
  match goal with
  | H:typesEq ?a ?b = true |- _ => apply typesEq_true in H; subst a
  end.
Lemma typeOfExpr_ok :
  forall e env t, typeOfExpr env e = Ok t -> ExpWt env e t.
Proof.
(induction e using good_Exp_ind; intros; try constructor; try discriminate;
  cbn-[String.append] in *; repeat (break_match; try discriminate); inj;
  subst).
-
(solve [ auto using lookupVarType_some ]).
-
(solve [ auto using typeOfValue_correct ]).
-
fwd_combine.
(constructor; auto).
-
(match goal with
 | H:_ ?args ?argtypes = Ok _
   |- _ =>
       assert
        (exists z,
           Zip args argtypes z /\ (forall a t, In (a, t) z -> ExpWt env a t))
 end).
{
clear Heqo.
generalize dependent l.
generalize dependent t.
generalize dependent t0.
(induction args; intros; fwd_combine).
-
(repeat econstructor).
intuition try solve_by_inversion.
-
(match goal with
 | H:ListAll.All (_ :: _) _ |- _ => destruct H
 end).
(exploit IHargs; try (solve [ eauto ])).
break_exists.
break_and.
(repeat econstructor).
+
eassumption.
+
(intros).
(match goal with
 | H:In _ (_ :: _) |- _ => apply in_inv in H; destruct H
 end).
*
exploit_typesEq.
(inj; subst).
(solve [ auto ]).
*
(solve [ auto ]).
}
(repeat break_exists).
(repeat break_and).
(econstructor; try eassumption).
replace t with t0.
+
(solve [ eauto using lookupFuncType_some ]).
+
clear Heqo.
clear H1.
clear H.
(assert (Ok t0 = Ok t); try congruence).
generalize dependent l.
(induction args; intros; fwd_combine; try congruence).
(solve [ eauto ]).
Qed.
Lemma isLVal_true : forall e, isLVal e = true -> IsLVal e.
Proof.
(destruct e; intros; try discriminate).
constructor.
Qed.
Lemma stmWellTyped_ok :
  forall s env t, stmWellTyped env t s = Ok tt -> StmWt env s t.
Proof.
(induction s; intros; simpl in *; fwd_combine; econstructor;
  try exploit_typesEq; (solve [ eauto using typeOfExpr_ok, isLVal_true ])).
Qed.
Lemma allPathsReturn_true :
  forall s, allPathsReturn s = true -> AllPathsReturn s.
Proof.
(induction s; intros; try discriminate; simpl in *).
-
(apply orb_true_elim in H).
(destruct H;
  (solve [ auto using SSeq_returns_l ]) || (solve
   [ auto using SSeq_returns_r ])).
-
(apply andb_true_iff in H).
(constructor; (solve [ intuition ])).
-
constructor.
Qed.
Lemma declWt_ok : forall env decl, declWt env decl = Ok tt -> DeclWt env decl.
Proof.
(destruct decl; intros; constructor; simpl in *;
  repeat (break_match; try discriminate); repeat break_unit).
-
(solve [ auto using stmWellTyped_ok ]).
-
(solve [ auto using allPathsReturn_true ]).
Qed.
Lemma typecheckProgram_ok : forall p, typecheckProgram p = Ok tt -> ProgWt p.
Proof.
(unfold typecheckProgram).
(unfold ProgWt).
intro p.
(generalize (makeEnv p)).
(induction p; intros).
-
solve_by_inversion.
-
(simpl in *).
fwd_combine.
(break_or; subst; (solve [ eauto using declWt_ok ])).
Qed.

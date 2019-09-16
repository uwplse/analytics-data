Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.
Require Import Impl.Ids.
Require Import Impl.Programs.
Require Import Impl.EvaluationState.
Require Import Impl.Interpreter.
Require Import Proofs.ZipFacts.
Require Import Proofs.Tactics.
Require Import Proofs.InductionSchemes.
Require Import Definitions.Trusted.Semantics.
Require Import Definitions.WellTyped.
Require Import Definitions.Zip.
Ltac
 contradict_sseq_is_not_sseq := solve
 [ match goal with
   | H:_ |- _ => contradiction  H; constructor
   end ].
Lemma lookup_some :
  forall env id val, lookup env id = Return val <-> Lookup env id val.
Proof.
(induction env; split; intros).
-
discriminate.
-
(inversion H).
-
(simpl in H).
(destruct a).
(destruct (id_eq_dec i id)).
+
injection H.
(intros).
subst.
constructor.
+
constructor.
*
assumption.
*
(apply IHenv).
assumption.
-
(inversion H; subst; clear H).
+
(simpl).
(destruct (id_eq_dec id id); congruence).
+
(simpl).
(destruct (id_eq_dec ida id); try congruence).
(apply IHenv).
assumption.
Qed.
Lemma lookup_none :
  forall env id val msg, lookup env id = Error msg -> ~ Lookup env id val.
Proof.
(intros).
intro Z.
(apply lookup_some in Z).
(rewrite H in Z).
discriminate.
Qed.
Lemma nope : forall P, ~ P -> P -> False.
Proof.
intuition.
Qed.
Lemma lookup_none2 :
  forall env id,
  (forall val, ~ Lookup env id val) -> exists msg, lookup env id = Error msg.
Proof.
(intros).
(destruct (lookup env id) eqn:Z).
-
exfalso.
(eapply nope).
+
(apply H).
+
(eapply lookup_some).
eassumption.
-
eexists.
reflexivity.
Qed.
Lemma reduceExp_some :
  forall env e e', reduceExp env e = Return (Some e') <-> ExpReduce env e e'.
Proof.
(destruct e; split; intros; try (solve [ inversion H ])).
-
(simpl in H).
(destruct (lookup env i) eqn:Z; try discriminate).
inj.
subst.
constructor.
(apply lookup_some).
assumption.
-
(inv H).
(simpl).
(apply lookup_some in H1).
(rewrite H1).
reflexivity.
-
(simpl in H).
(repeat (break_match; try discriminate)).
subst.
inj.
subst.
constructor.
-
(inv H).
reflexivity.
Qed.
Definition IsLit e := exists v, e = ELit v.
Hint Unfold IsLit.
Definition IsCall e := exists f args, e = ECall f args.
Hint Unfold IsCall.
Definition ExpCanBeReducedInEnv (e : Exp) (env : Environment) : Prop :=
  (exists e', ExpReduce env e e') \/
  (exists f args argv, e = ECall f args /\ AllValues args argv).
Definition ExpCanBeReduced (e : Exp) : Prop :=
  (exists env e', ExpReduce env e e') \/
  (exists f args argv, e = ECall f args /\ AllValues args argv).
Ltac
 prove_not_literal :=
  match goal with
  | |- ~ IsLit _ =>
        unfold IsLit; intro; repeat break_exists; solve_by_inversion
  end.
Lemma reduceExp_err :
  forall env e err,
  reduceExp env e = Error err -> ~ IsLit e /\ ~ ExpCanBeReducedInEnv e env.
Proof.
(intros).
(destruct e; try discriminate; split; try prove_not_literal).
-
(unfold ExpCanBeReducedInEnv).
intro.
(break_or; repeat break_exists).
+
(inv H0).
(simpl in *).
(apply lookup_some in H2).
(rewrite H2 in H).
discriminate.
+
break_and.
discriminate.
-
(simpl in *).
(solve [ repeat break_match; try discriminate ]).
Qed.
Lemma reduceExp_swap_env :
  forall env1 env2 e x,
  reduceExp env1 e = Return (Some x) -> reduceExp env2 e <> Return None.
Proof.
(induction e; simpl; intros; repeat (try discriminate; break_match)).
Qed.
Lemma findExpContext_none :
  forall e, findExpContext e = None -> exists val, e = ELit val.
Proof.
(destruct e; intros; simpl in *; try discriminate;
  repeat (break_match; try discriminate)).
eexists.
reflexivity.
Qed.
Lemma findExpContext_real :
  forall e e' ctx, findExpContext e = Some (e', ctx) -> e = ctx e'.
Proof.
(induction e using good_Exp_ind; intros; simpl in *; try discriminate).
-
inj.
subst.
reflexivity.
-
(repeat (break_match; try discriminate)).
+
inj.
subst.
(erewrite IHe1; reflexivity).
+
inj.
subst.
(erewrite IHe2; reflexivity).
+
inj.
subst.
reflexivity.
-
(break_match; try (solve [ inj; subst; reflexivity ])).
(destruct p).
inj.
subst.
f_equal.
generalize dependent l.
(induction args; intros; simpl in *).
+
discriminate.
+
(repeat (break_match; try discriminate); inj; subst; f_equal; intuition).
Qed.
Lemma findExpContext_is_legal_ctx :
  forall e e' ctx, findExpContext e = Some (e', ctx) -> ExpCtx ctx.
Proof.
(induction e using good_Exp_ind; intros; simpl in *; try discriminate; inj;
  subst).
-
constructor.
-
(repeat break_match; inj; subst).
+
constructor.
eauto.
+
(apply findExpContext_none in Heqo).
(destruct Heqo).
subst.
constructor.
eauto.
+
constructor.
-
break_match.
+
(destruct p).
(assert (Q : ctx = (fun e => ECall f (l e)) /\ ExpCtxSeq l)).
*
generalize dependent ctx.
generalize dependent l.
(induction args; intros; try discriminate).
break_match.
{
(destruct p).
inj.
subst.
(split; try reflexivity).
constructor.
(simpl in *).
break_and.
(solve [ eauto ]).
}
{
(break_match; try discriminate).
(destruct p).
inj.
subst.
(simpl in *).
break_and.
(split; try reflexivity).
(apply findExpContext_none in Heqo0).
(destruct Heqo0).
subst.
constructor.
(eapply IHargs in H0; try reflexivity).
break_and.
assumption.
}
*
break_and.
subst.
constructor.
assumption.
+
inj.
subst.
constructor.
Qed.
Lemma findExpContext_finds :
  forall e ectx,
  ExpCtx ectx ->
  ExpCanBeReduced e -> findExpContext (ectx e) = Some (e, ectx).
Proof.
(intros).
generalize dependent e.
(induction H using good_ExpCtx_ind with
   (P0 := 
     fun (l : Exp -> list Exp) (lctx : ExpCtxSeq l) =>
     forall e, ExpCanBeReduced e -> findContextInList (l e) = Some (e, l));
  intros).
-
(destruct H0; repeat break_exists).
+
(inv H; reflexivity).
+
(repeat break_and).
subst.
(simpl).
(break_match; try reflexivity).
exfalso.
generalize dependent p.
(match goal with
 | H:AllValues ?A ?V |- _ => generalize dependent V; induction A
 end; intros).
*
discriminate.
*
(repeat (break_match; try discriminate)).
{
(inversion_then discriminate).
}
{
(inv H0).
(eapply IHx0; (solve [ eauto ])).
}
-
(simpl).
(rewrite IHExpCtx by assumption).
reflexivity.
-
(simpl).
(rewrite IHExpCtx by assumption).
reflexivity.
-
(simpl).
(rewrite IHExpCtx by assumption).
reflexivity.
-
(simpl).
(rewrite IHExpCtx by assumption).
reflexivity.
-
(simpl).
(rewrite IHExpCtx by assumption).
reflexivity.
Qed.
Lemma findExpContext_finds_call :
  forall ectx f args argv,
  ExpCtx ectx ->
  AllValues args argv ->
  findExpContext (ectx (ECall f args)) = Some (ECall f args, ectx).
Proof.
(intros).
(apply findExpContext_finds).
-
assumption.
-
right.
eauto.
Qed.
Ltac
 inv_wt :=
  match goal with
  | H:ValueWt _ _ |- _ => inv H
  | H:ExpWt _ (_ _) _ |- _ => inv H
  | H:ExpWt _ (_ _ _) _ |- _ => inv H
  | H:StmWt _ (_ _) _ |- _ => inv H
  | H:StmWt _ (_ _ _) _ |- _ => inv H
  end.
Lemma findExpContext_can_be_reduced :
  forall e tenv t x ectx,
  ExpWt tenv e t -> findExpContext e = Some (x, ectx) -> ExpCanBeReduced x.
Proof.
(induction e using good_Exp_ind; simpl; intros; inj; subst).
-
left.
(solve [ repeat econstructor ]).
Unshelve.
+
(repeat constructor).
+
(repeat constructor).
-
discriminate.
-
inv_wt.
(repeat (break_match; try discriminate); inj; subst; try (solve [ eauto ])).
(repeat eapply_in_hyp findExpContext_none).
(repeat break_exists).
subst.
left.
(repeat inv_wt).
(repeat econstructor).
Unshelve.
constructor.
-
(repeat break_match; inj; subst).
+
generalize dependent l.
generalize dependent x.
inv_wt.
clear H3.
generalize dependent argTypes.
generalize dependent argsZipped.
clear t.
(induction args; intros).
*
discriminate.
*
(match goal with
 | H:Zip (_ :: _) _ _ |- _ => inv H
 end).
(repeat (break_match; try discriminate); inj; subst).
{
(eapply H; try eassumption).
(match goal with
 | H:_ |- _ => apply H
 end).
left.
reflexivity.
}
{
(eapply IHargs with (argsZipped := zrest); try reflexivity).
-
eapply_hyp.
-
(intros).
(eapply_hyp_then intuition).
-
eassumption.
}
+
right.
(assert (exists argv, AllValues args argv)).
{
clear H.
clear H0.
(induction args).
-
(repeat econstructor).
-
(repeat (break_match; try discriminate)).
(exploit IHargs; try auto).
(eapply_in_hyp findExpContext_none).
(repeat break_exists).
subst.
(repeat econstructor; (solve [ eauto ])).
}
break_exists.
(repeat econstructor; eauto).
Qed.
Lemma findExpToEvaluate_real :
  forall s e ctx, findExpToEvaluate s = Some (e, ctx) -> s = ctx e.
Proof.
(induction s; intros; simpl in *; try discriminate;
  try (solve [ inj; subst; reflexivity ])).
(break_match; try discriminate).
(destruct p).
inj.
subst.
f_equal.
(apply IHs1).
reflexivity.
Qed.
Lemma findExpToEvaluate_is_legal_ctx :
  forall s e ctx, findExpToEvaluate s = Some (e, ctx) -> StmExpCtx ctx.
Proof.
(induction s; intros; simpl in *; try discriminate;
  try (solve [ inj; subst; constructor ])).
(break_match; try discriminate).
(destruct p).
inj.
subst.
constructor.
eauto.
Qed.
Lemma findExpToEvaluate_finds :
  forall sctx e,
  StmExpCtx sctx -> findExpToEvaluate (sctx e) = Some (e, sctx).
Proof.
(intros).
(induction H; try reflexivity).
(simpl).
(rewrite IHStmExpCtx).
reflexivity.
Qed.
Lemma findExpToEvaluate_none :
  forall s,
  findExpToEvaluate s = None -> forall sctx e, StmExpCtx sctx -> s <> sctx e.
Proof.
(induction s using left_induction; intros).
-
(destruct s; try discriminate).
+
(inversion_then discriminate).
+
contradict_sseq_is_not_sseq.
+
(inversion_then discriminate).
+
(inversion_then discriminate).
-
(simpl in *).
break_match.
+
break_pair.
discriminate.
+
(inv H0; try discriminate).
intro.
inj.
subst.
(eapply IHs1; eauto).
Qed.
Lemma reduceStm_correct :
  forall s s', reduceStm s = Some s' <-> StmReduce s s'.
Proof.
(split; intros).
-
(unfold reduceStm in *).
(repeat (break_match; try discriminate); subst; inj; subst; constructor).
-
(inv H; reflexivity).
Qed.
Lemma stepExpInStm_correct :
  forall s envs globals st',
  stepExpInStm s envs globals = Return (Some st') ->
  StmStep (MakeStmState s envs globals) st'.
Proof.
(intros).
(unfold stepExpInStm in *).
(repeat break_match; try discriminate).
subst.
inj.
subst.
replace s with s0 (e1 e0).
-
constructor.
+
eauto using findExpToEvaluate_is_legal_ctx.
+
eauto using findExpContext_is_legal_ctx.
+
(apply reduceExp_some).
assumption.
-
(apply eq_sym).
(apply findExpToEvaluate_real).
(rewrite Heqo).
(repeat f_equal).
(apply findExpContext_real).
assumption.
Qed.
Definition noExpressionCanBeReducedIn (s : Stm) : Prop :=
  forall sctx ectx env e e',
  StmExpCtx sctx -> ExpCtx ectx -> s = sctx (ectx e) -> ~ ExpReduce env e e'.
Lemma stepExpInStm_none :
  forall s envs globals,
  stepExpInStm s envs globals = Return None ->
  findExpToEvaluate s = None \/
  (exists e sctx,
     findExpToEvaluate s = Some (e, sctx) /\ findExpContext e = None) \/
  (exists e sctx e' ectx,
     findExpToEvaluate s = Some (e, sctx) /\
     findExpContext e = Some (e', ectx) /\
     reduceExp (List.concat (envs ++ [globals])) e' = Return None).
Proof.
(unfold stepExpInStm).
(intros).
(repeat (break_match; try discriminate); subst; inj; subst).
-
right.
right.
(solve [ eauto  10 ]).
-
right.
left.
(solve [ eauto ]).
-
left.
reflexivity.
Qed.
Lemma IsLit_dec : forall e, IsLit e \/ ~ IsLit e.
Proof.
(destruct e; try (solve [ eauto ]);
  (right; intro Z; destruct Z; discriminate)).
Qed.
Lemma literals_do_not_reduce :
  forall env e e', ExpReduce env e e' -> ~ IsLit e.
Proof.
(intros).
intro Z.
(inv Z).
solve_by_inversion.
Qed.
Lemma ExpCtx_unique :
  forall ectxA ectxB,
  ExpCtx ectxA ->
  ExpCtx ectxB ->
  forall a b,
  ExpCanBeReduced a ->
  ExpCanBeReduced b -> ectxA a = ectxB b -> ectxA = ectxB /\ a = b.
Proof.
(intros).
(eapply findExpContext_finds in H1; try exact H).
(eapply findExpContext_finds in H2; try exact H0).
(rewrite H3 in H1).
(rewrite H1 in H2).
(split; congruence).
Qed.
Lemma stepExpInStm_none' :
  forall s envs globals,
  stepExpInStm s envs globals = Return None -> noExpressionCanBeReducedIn s.
Proof.
(unfold noExpressionCanBeReducedIn).
(intros).
(apply stepExpInStm_none in H).
intro Z.
(repeat break_or; subst).
-
(eapply findExpToEvaluate_none; (solve [ eauto ])).
-
(repeat break_exists).
(repeat break_and).
(eapply findExpContext_none in H2).
break_exists.
subst.
(rewrite findExpToEvaluate_finds in H by assumption).
inj.
(inv H1; try discriminate).
subst.
solve_by_inversion.
-
(repeat break_exists).
(repeat break_and).
(apply reduceExp_some in Z).
(rewrite findExpToEvaluate_finds in H by assumption).
inj.
subst.
(eapply findExpContext_finds in H1).
+
exfalso.
(assert (e = x1)).
{
(rewrite H2 in H1).
congruence.
}
subst.
(eapply reduceExp_swap_env; eassumption).
+
left.
(do 2 eexists).
(eapply reduceExp_some).
eassumption.
Qed.
Lemma reduceStmOrStepExp_correct :
  forall s envs globals st',
  reduceStmOrStepExp s envs globals = Return (Some st') ->
  StmStep (MakeStmState s envs globals) st'.
Proof.
(intros).
(unfold reduceStmOrStepExp in *).
break_match.
-
inj.
subst.
(apply StmStep_reduce).
(apply reduceStm_correct).
assumption.
-
(solve [ auto using stepExpInStm_correct ]).
Qed.
Lemma reduceStm_none :
  forall s, reduceStm s = None -> forall s', ~ StmReduce s s'.
Proof.
(destruct s; intros; simpl in *; intro Q; inv Q; discriminate).
Qed.
Lemma reduceStm_complete :
  forall s s', StmReduce s s' -> reduceStm s = Some s'.
Proof.
(intros).
(inversion_then reflexivity).
Qed.
Lemma reduceStmOrStepExp_none :
  forall s envs globals,
  reduceStmOrStepExp s envs globals = Return None ->
  noExpressionCanBeReducedIn s /\ (forall s', ~ StmReduce s s').
Proof.
(intros).
(intros).
(unfold reduceStmOrStepExp in *).
(break_match; try discriminate).
eauto using stepExpInStm_none', reduceStm_none.
Qed.
Lemma stepStm'_noseq_some :
  forall s s' envs globals,
  ~ IsSeq s ->
  reduceStm s = Some s' <->
  stepStm' s envs globals = Some (MakeStmState s' envs globals).
Proof.
(split; intros; destruct s; try contradict_sseq_is_not_sseq; try discriminate;
  simpl in *; repeat (break_match; try discriminate); 
  try congruence).
Qed.
Lemma stepStm'_noseq_none :
  forall s envs globals,
  ~ IsSeq s -> reduceStm s = None <-> stepStm' s envs globals = None.
Proof.
(split; intros; destruct s; try contradict_sseq_is_not_sseq; try discriminate;
  simpl in *; repeat (break_match; try discriminate); congruence).
Qed.
Lemma noExpressionCanBeReducedIn_seq :
  forall s1 s2,
  noExpressionCanBeReducedIn s1 <-> noExpressionCanBeReducedIn (SSeq s1 s2).
Proof.
(unfold noExpressionCanBeReducedIn).
(split; intros).
-
(inv H0; try discriminate).
inj.
subst.
(solve [ eauto ]).
-
(eapply H).
+
(eapply StmExpCtx_SSeq).
eassumption.
+
eassumption.
+
(simpl).
(repeat f_equal).
assumption.
Qed.
Lemma stepStm'_none :
  forall s envs globals,
  stepStm' s envs globals = None ->
  noExpressionCanBeReducedIn s ->
  forall st', ~ StmStep (MakeStmState s envs globals) st'.
Proof.
(induction s using left_induction; intros).
-
intro Z.
(inv Z).
+
(eapply_hyp_then eauto).
+
contradict_sseq_is_not_sseq.
+
(eapply reduceStm_none; try eassumption).
(eapply stepStm'_noseq_none; (solve [ eauto ])).
-
intro Z.
(inv Z).
+
(eapply_hyp_then eauto).
+
(cbn-[reduceStm] in H).
(repeat (break_match; try discriminate)).
(eapply IHs1; try eassumption).
(eapply noExpressionCanBeReducedIn_seq).
eassumption.
+
(inversion_then discriminate).
Qed.
Lemma stepStm'_correct :
  forall s envs globals st',
  stepStm' s envs globals = Some st' ->
  StmStep (MakeStmState s envs globals) st'.
Proof.
(induction s using left_induction; intros).
-
(destruct s; try contradict_sseq_is_not_sseq; cbn-[reduceStm] in *;
  repeat (break_match; try discriminate); inj; subst; 
  apply StmStep_reduce; apply reduceStm_correct; auto).
-
(cbn-[reduceStm] in *).
(repeat (break_match; try discriminate); inj; subst).
+
(apply StmStep_reduce).
(apply reduceStm_correct).
assumption.
+
(solve [ auto using StmStep_seq1 ]).
Qed.
Lemma stepStm_correct :
  forall st st', stepStm st = Return (Some st') -> StmStep st st'.
Proof.
(intros).
(unfold stepStm in *).
(repeat (break_match; subst; try discriminate)).
-
(repeat (inj; subst)).
(solve [ auto using stepExpInStm_correct ]).
-
(repeat (inj; subst)).
(solve [ auto using stepStm'_correct ]).
Qed.
Lemma reduceStmOrStepExp_none_noseq :
  forall s envs globals,
  reduceStmOrStepExp s envs globals = Return None ->
  ~ IsSeq s -> forall st st', ss_stm st = s -> ~ StmStep st st'.
Proof.
(intros).
(apply reduceStmOrStepExp_none in H).
break_and.
intro Z.
(inv Z; try contradict_sseq_is_not_sseq).
-
(eapply H; eauto).
reflexivity.
-
(eapply H2).
eassumption.
Qed.
Lemma stepStm_none :
  forall st, stepStm st = Return None -> forall st', ~ StmStep st st'.
Proof.
(intros).
(unfold stepStm in *).
(destruct st).
(repeat (break_match; try discriminate)).
(apply stepStm'_none).
-
congruence.
-
(solve [ eauto using stepExpInStm_none' ]).
Qed.
Theorem init_correct : forall p, Initial p (makeInitialState p).
Proof.
constructor.
Qed.
Lemma values_correct : forall es vs, values es = Some vs <-> AllValues es vs.
Proof.
(split; intros).
-
generalize dependent vs.
(induction es; intros; simpl in *).
+
inj.
subst.
constructor.
+
(repeat (break_match; try discriminate)).
inj.
subst.
constructor.
auto.
-
(induction H).
+
reflexivity.
+
(simpl).
(rewrite IHAllValues).
reflexivity.
Qed.
Lemma values_complete : forall es vs, AllValues es vs -> values es = Some vs.
Proof.
(apply values_correct).
Qed.
Lemma findFunc_correct :
  forall f prog args body,
  findFunc f prog = Some (args, body) -> LookupFunction prog f args body.
Proof.
(induction prog; intros; simpl in *).
-
discriminate.
-
(repeat (break_match; try discriminate); subst; inj; subst).
+
(solve [ auto using LookupFunctionElsewhere ]).
+
(solve [ eauto using LookupFunctionHere, zip_map ]).
+
(solve [ auto using LookupFunctionElsewhere ]).
Qed.
Lemma findFunc_complete :
  forall f prog args body,
  LookupFunction prog f args body -> findFunc f prog = Some (args, body).
Proof.
(induction prog; intros; simpl in *).
-
solve_by_inversion.
-
(inv H).
+
break_match.
*
(erewrite zip_fst; (solve [ eauto ])).
*
congruence.
+
(break_match; subst).
*
(solve [ eauto ]).
*
(break_match; simpl in *).
{
congruence.
}
{
eauto.
}
Qed.
Lemma zip_correct :
  forall A B (l1 : list A) (l2 : list B) res,
  zip l1 l2 = Some res <-> Zip l1 l2 res.
Proof.
(split; intros).
-
generalize dependent l2.
generalize dependent res.
(induction l1; intros; simpl in *; repeat (break_match; try discriminate);
  subst; inj; subst; constructor; auto).
-
(induction H).
+
reflexivity.
+
(simpl).
(rewrite IHZip).
reflexivity.
Qed.
Lemma zip_complete :
  forall A B (l1 : list A) (l2 : list B) res,
  Zip l1 l2 res -> zip l1 l2 = Some res.
Proof.
(apply zip_correct).
Qed.
Lemma callStep_correct : forall s s', callStep s = Return s' -> Step s s'.
Proof.
(intros).
(unfold callStep in *).
(repeat (break_match; try discriminate)).
subst.
inj.
subst.
replace ss_stm with s0 (e1 (ECall i l)).
-
(eapply Step_call).
+
(apply values_correct).
eassumption.
+
(apply findFunc_correct).
eassumption.
+
(apply zip_correct).
assumption.
+
(eapply findExpContext_is_legal_ctx).
eassumption.
+
(eapply findExpToEvaluate_is_legal_ctx).
eassumption.
-
(apply findExpContext_real in Heqo0).
(apply findExpToEvaluate_real in Heqo).
congruence.
Qed.
Lemma returnValue_correct :
  forall s val, returnValue s = Some val -> s = SReturn (ELit val).
Proof.
(intros).
(unfold returnValue in *).
(repeat (break_match; try discriminate)).
congruence.
Qed.
Lemma returnValue_none :
  forall s, returnValue s = None -> forall v, s <> SReturn (ELit v).
Proof.
(intros).
(destruct s; try discriminate).
(destruct e; discriminate).
Qed.
Lemma wt_sctx :
  forall sctx e tenv rettype,
  StmExpCtx sctx ->
  StmWt tenv (sctx e) rettype -> exists tenv' exptype, ExpWt tenv' e exptype.
Proof.
(intros).
generalize dependent e.
generalize dependent tenv.
generalize dependent rettype.
(induction H; intros; inv_wt; (solve [ eauto ])).
Qed.
Ltac inv_zip := match goal with
                | H:Zip (_ :: _) _ _ |- _ => inv H
                end.
Require Import Proofs.ListAll.
Lemma wt_ectx :
  forall e ectx tenv t,
  ExpCtx ectx -> ExpWt tenv (ectx e) t -> exists tenv' t', ExpWt tenv' e t'.
Proof.
(intros).
generalize dependent e.
generalize dependent tenv.
generalize dependent t.
(induction H using good_ExpCtx_ind with
   (P0 := 
     fun (lctx : Exp -> list Exp) (pf : ExpCtxSeq lctx) =>
     forall e,
     All (lctx e) (fun e' => exists tenv' t', ExpWt tenv' e' t') ->
     exists tenv' t', ExpWt tenv' e t'); intros;
  try (solve [ try inv_wt; eauto ])).
-
(eapply IHExpCtx).
inv_wt.
clear H2.
generalize dependent argTypes.
generalize dependent argsZipped.
clear t.
(induction (lctx e0); intros).
+
constructor.
+
inv_zip.
split.
*
(do 2 eexists).
(eapply H6).
left.
reflexivity.
*
(eapply IHl; intros).
{
(eapply H6).
right.
eassumption.
}
{
eassumption.
}
-
(simpl in *).
break_and.
(repeat break_exists).
(eapply IHExpCtx).
eassumption.
-
(eapply IHExpCtx).
eapply_hyp.
Qed.
Lemma StmExpCtx_unique :
  forall sctx1 sctx2 e1 e2,
  StmExpCtx sctx1 ->
  StmExpCtx sctx2 -> sctx1 e1 = sctx2 e2 -> sctx1 = sctx2 /\ e1 = e2.
Proof.
(intros).
generalize dependent e1.
generalize dependent e2.
generalize dependent sctx2.
(induction H; intros; match goal with
                      | H:StmExpCtx _ |- _ => inv H
                      end; try discriminate; inj; subst;
  try (solve [ intuition ])).
(exploit IHStmExpCtx; try eassumption).
break_and.
subst.
intuition.
Qed.
Lemma nonreducible_Exp_means_no_StmStep :
  forall sctx ectx e env tenv t,
  ~ IsLit e ->
  ~ ExpCanBeReducedInEnv e env ->
  StmExpCtx sctx ->
  findExpContext (ectx e) = Some (e, ectx) ->
  ExpWt tenv (ectx e) t ->
  forall st st',
  env = List.concat (ss_envs st ++ [ss_globals st]) ->
  ss_stm st = sctx (ectx e) -> ~ StmStep st st'.
Proof.
(intros).
intro Z.
(remember (ss_stm st) as S).
generalize dependent S.
generalize dependent sctx.
generalize dependent ectx.
generalize dependent e.
generalize dependent env.
(induction Z; intros; subst; simpl in *).
-
(assert (e = e0)).
{
(eapply_in_hyp StmExpCtx_unique; eauto).
break_and.
subst.
(eapply ExpCtx_unique; try exact H8; eauto).
+
(solve [ eauto using findExpContext_is_legal_ctx ]).
+
left.
(solve [ eauto ]).
+
(solve [ eauto using findExpContext_can_be_reduced ]).
}
subst.
contradiction  H3.
left.
(solve [ eauto ]).
-
(match goal with
 | H:StmExpCtx _ |- _ => inv H
 end; try discriminate).
(inj; subst).
(solve [ eauto ]).
-
(match goal with
 | H:StmExpCtx _ |- _ => inv H
 end; try discriminate; try solve_by_inversion).
+
(inv H).
*
(inversion_then discriminate).
*
(match goal with
 | H:StmExpCtx _ |- _ => inv H
 end; try discriminate).
(eapply_in_hyp findExpContext_is_legal_ctx).
(match goal with
 | H:ExpCtx _ |- _ => inv H
 end; try discriminate).
inj.
subst.
(solve [ intuition eauto ]).
+
(inv H).
(eapply_in_hyp findExpContext_is_legal_ctx).
(match goal with
 | H:ExpCtx _ |- _ => inv H
 end; try discriminate).
subst.
contradiction  H0.
econstructor.
reflexivity.
+
(eapply_in_hyp findExpContext_is_legal_ctx).
(match goal with
 | H:StmReduce _ _ |- _ => inv H
 end; match goal with
      | H:ExpCtx _ |- _ => inv H
      end; try discriminate; subst; contradiction  H0; econstructor;
  reflexivity).
Qed.
Lemma stepStm_impossible :
  forall st err tenv t,
  StmWt tenv (ss_stm (evaluating st)) t ->
  stepStm (evaluating st) = Error err -> forall st', ~ Step st st'.
Proof.
(intros).
(unfold stepStm in *).
(unfold stepExpInStm in *).
(repeat break_match; try discriminate).
(repeat (inj; subst)).
(destruct st).
(simpl in *).
(inj; subst).
intro Z.
(inv Z).
-
(assert (exists tenv t, ExpWt tenv e t)).
{
(eapply wt_sctx).
-
(solve [ eauto using findExpToEvaluate_is_legal_ctx ]).
-
(erewrite <- findExpToEvaluate_real; eassumption).
}
(repeat break_exists).
(eapply nonreducible_Exp_means_no_StmStep; eauto).
+
(eapply reduceExp_err; eassumption).
+
(eapply reduceExp_err; eassumption).
+
(eapply findExpToEvaluate_is_legal_ctx; eassumption).
+
(erewrite <- findExpContext_real; eassumption).
+
(erewrite <- findExpContext_real; eassumption).
+
(eapply findExpToEvaluate_real).
(erewrite <- findExpContext_real; eassumption).
-
(assert (e0 = ECall f args)).
{
(eapply ExpCtx_unique).
-
(eapply findExpContext_is_legal_ctx).
eassumption.
-
eassumption.
-
(erewrite findExpToEvaluate_finds in Heqo; try eassumption).
inj.
subst.
(erewrite findExpContext_finds in Heqo0; try eassumption).
+
inj.
subst.
right.
(solve [ eauto ]).
+
right.
(solve [ eauto ]).
-
right.
(solve [ eauto ]).
-
(eapply eq_sym).
(eapply findExpContext_real).
(erewrite findExpToEvaluate_finds in Heqo by assumption).
inj.
subst.
eassumption.
}
subst.
(eapply reduceExp_err).
+
eassumption.
+
right.
(solve [ eauto ]).
-
(simpl in *).
(inj; subst).
discriminate.
Qed.
Theorem step_some : forall s s', step s = Return (Some s') -> Step s s'.
Proof.
(intros).
(unfold step in *).
(destruct s).
(repeat (break_match; try discriminate); subst; inj; subst;
  try (solve [ auto using callStep_correct ])).
-
(solve [ auto using Step_stm, stepStm_correct ]).
-
subst.
inj.
subst.
replace s with fst (c v) by (rewrite Heqp; reflexivity).
replace l0 with snd (c v) by (rewrite Heqp; reflexivity).
replace ss_stm with SReturn (ELit v)
 by auto using eq_sym, returnValue_correct.
constructor.
Qed.
Theorem step_none : forall s, step s = Return None -> Done s.
Proof.
(intros).
(unfold step in *).
(repeat (break_match; try discriminate); subst; inj; subst).
(apply returnValue_correct in Heqo1).
subst.
econstructor.
Qed.
Theorem step_impossible :
  forall s err tenv t,
  StmWt tenv (ss_stm (evaluating s)) t ->
  step s = Error err -> forall s', ~ Step s s'.
Proof.
(intros).
(unfold step in *).
(repeat (break_match; try discriminate); subst; inj; subst).
-
intro St.
(inv St).
+
(solve [ eapply stepStm_none; eauto ]).
+
clear Heqo1.
clear Heqi.
(unfold callStep in Heqi0).
(rewrite findExpToEvaluate_finds in Heqi0 by assumption).
(erewrite findExpContext_finds_call in Heqi0; eauto).
(erewrite findFunc_complete in Heqi0; eauto).
(erewrite values_complete in Heqi0; eauto).
(erewrite zip_complete in Heqi0; eauto).
discriminate.
+
discriminate.
-
(solve [ eauto using stepStm_impossible ]).
Qed.

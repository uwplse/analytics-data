Require Import Impl.Programs.
Require Import Proofs.ListAll.
Require Import Proofs.Tactics.
Require Import Definitions.Trusted.Semantics.
Section expression_induction.
Variable (P : Exp -> Prop).
Hypothesis (rec_EVar : forall var, P (EVar var)).
Hypothesis (rec_ELit : forall val, P (ELit val)).
Hypothesis (rec_EBin : forall e1 e2, P e1 -> P e2 -> P (EPlus e1 e2)).
Hypothesis (rec_ECall : forall f args, All args P -> P (ECall f args)).
Fixpoint good_Exp_ind (e : Exp) : P e :=
  match e with
  | EVar var => rec_EVar var
  | ELit val => rec_ELit val
  | EPlus e1 e2 => rec_EBin _ _ (good_Exp_ind e1) (good_Exp_ind e2)
  | ECall f es =>
      rec_ECall f es
        ((fix G es : All es P :=
            match es with
            | nil => I
            | cons e es' => conj (good_Exp_ind e) (G es')
            end) es)
  end.
End expression_induction.
Section left_statement_induction.
Inductive IsSeq : Stm -> Prop :=
    SeqIsSeq : forall a b, IsSeq (SSeq a b).
Definition IsSeq_dec (s : Stm) : {IsSeq s} + {~ IsSeq s}.
(refine match s with
        | SSeq _ _ => left (SeqIsSeq _ _)
        | _ => right _
        end; intro; solve_by_inversion).
Defined.
Inductive SeqChainL : Stm -> Prop :=
  | SeqChainLEnd : forall s, ~ IsSeq s -> SeqChainL s
  | SeqChainLCont : forall l r, SeqChainL l -> SeqChainL (SSeq l r).
Fixpoint left_chain (s : Stm) : SeqChainL s.
(refine
  match s as S return (SeqChainL S) with
  | SSeq a b => SeqChainLCont _ _ (left_chain a)
  | x =>
      match IsSeq_dec x with
      | right pf => SeqChainLEnd x pf
      | left pf => _
      end
  end; solve_by_inversion).
Defined.
Lemma left_induction :
  forall P : Stm -> Prop,
  (forall s, ~ IsSeq s -> P s) ->
  (forall l r, P l -> P (SSeq l r)) -> forall s, P s.
Proof.
(intros).
(induction (left_chain s); auto).
Qed.
End left_statement_induction.
Section exp_ctx_induction.
Scheme good_ExpCtx_ind := Induction for ExpCtx Sort Prop
  with good_ExpCtxSeq_ind := Induction for ExpCtxSeq 
  Sort Prop.
End exp_ctx_induction.

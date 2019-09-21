Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250b.BaseDefs.
Require Import BetaJulia.Sub0250b.BaseProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Close Scope btj_scope.
Open Scope btjnf_scope.
Open Scope btjr_scope.
Lemma atom_sub_r_union__inv : forall t t1' t2' : ty, |- t << TUnion t1' t2' -> atom_type t -> |- t << t1' \/ |- t << t2'.
Proof.
(intros t t1' t2' Hsub).
(remember (TUnion t1' t2') as t' eqn:Heq ).
(induction Hsub; intros Hat; try (solve [ inversion Heq | inversion Hat ]); inversion Heq; subst).
-
(left; assumption).
-
(right; assumption).
-
(assert (Hnf : InNF( t)) by (constructor; assumption)).
(rewrite (mk_nf_nf__equal t Hnf) in IHHsub).
tauto.
Qed.
Set Printing Width 148.
Set Silent.
Lemma sub_r_cname__inv : forall c1 c2 : cname, |- TCName c1 << TCName c2 -> c1 = c2.
Proof.
(intros c1 c2 Hsub).
(remember (TCName c1) as t1 eqn:Heq1 ).
(remember (TCName c2) as t2 eqn:Heq2 ).
(induction Hsub; try inversion Heq1; inversion Heq2; subst).
reflexivity.
Set Printing Width 148.
Set Printing Width 148.
Lemma sub_r_nf_ref__inv : forall t t' : ty, InNF( t) -> InNF( t') -> |- TRef t << TRef t' -> |- t << t' /\ |- t' << t.
Set Silent.
Proof.
(intros t t' Hnf Hnf' Hsub).
(remember (TRef t) as t1 eqn:Heq1 ).
(remember (TRef t') as t2 eqn:Heq2 ).
(induction Hsub; try inversion Heq1; inversion Heq2; subst).
Unset Silent.
tauto.
(apply IHHsub; try tauto).
(apply mk_nf_nf__equal).
Set Printing Width 148.
(do 2 constructor; assumption).
Qed.
Set Silent.
Lemma sub_r_ref__inv : forall t t' : ty, |- TRef t << TRef t' -> |- t << t' /\ |- t' << t.
Unset Silent.
Proof.
Show.
(intros t t' Hsub).
Search -sub_r.

Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
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
Lemma unite_pairs_of_nf__preserves_sub_r :
  forall t1 t1' t2 t2' : ty,
  InNF( t1) -> InNF( t1') -> InNF( t2) -> InNF( t2') -> |- t1 << t1' -> |- t2 << t2' -> |- unite_pairs t1 t2 << unite_pairs t1' t2'.
Proof.
(intros t1 t1' t2 t2' Hnf1).
(induction Hnf1).
-
(intros Hnf1'; induction Hnf1').
+
(intros Hnf2; induction Hnf2).
*
(intros Hnf2'; induction Hnf2'; intros Hsub1 Hsub2).
{
(rewrite (unite_pairs_of_atomtys _ _ H H1)).
(rewrite (unite_pairs_of_atomtys _ _ H0 H2)).
(constructor; assumption).
}
{
(rewrite unite_pairs_atom_union; try assumption).
(destruct (atom_sub_r_union__inv _ _ _ Hsub2 H1) as [Hsub21| Hsub22]; [ apply SR_UnionR1 | apply SR_UnionR2 ]; tauto).
(* Auto-generated comment: Failed. *)

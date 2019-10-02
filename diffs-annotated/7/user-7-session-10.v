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
}
*
(intros Hnf2'; intros Hsub1 Hsub2).
(rewrite unite_pairs_atom_union; try assumption).
(apply sub_r_union_l__inv in Hsub2; try assumption).
(inversion Hsub2).
(constructor; [ apply IHHnf2_1 | apply IHHnf2_2 ]; assumption).
+
(intros Hnf2; intros Hnf2'; intros Hsub1 Hsub2).
(rewrite (unite_pairs_union_t t1 t0 t2')).
(destruct (atom_sub_r_union__inv _ _ _ Hsub1 H) as [Hsub11| Hsub12]; [ apply SR_UnionR1 | apply SR_UnionR2 ]; tauto).
-
(intros Hnf1' Hnf2 Hn2' Hsub1 Hsub2).
(rewrite (unite_pairs_union_t t1 t0 t2)).
Check sub_r_union_l__inv.
(destruct (sub_r_union_l__inv _ _ _ Hsub1) as [Hsub11 Hsub12]).
(constructor; tauto).
Qed.
Lemma unite_pairs_of_nf__preserves_sub_r1 :
  forall t1 t2 t1' t2' : ty, InNF( t1) -> |- t1 << t1' -> InNF( t2) -> |- t2 << t2' -> |- unite_pairs t1 t2 << TPair t1' t2'.
Proof.
(intros ta; induction ta; intros tb; induction tb; intros ta' tb' Hnf1 Hsub1 Hnf2 Hsub2; try (solve [ simpl; constructor; assumption ])).
(intros t1; induction t1; intros t2; induction t2; intros t1' t2' Hsub; intros Hnf1 Hnf2;
  try (solve
   [ match goal with
     | Hsub:|- ?t1 << ?t2
       |- _ =>
           remember t1 as tx eqn:Heqx ; remember t2 as ty eqn:Heqy ;
            assert (Hnf : InNF( t1)) by (subst; apply unite_pairs__preserves_nf; assumption); induction Hsub; inversion Heqx; 
            inversion Heqy; subst; tauto || (rewrite (mk_nf_nf__equal _ Hnf) in IHHsub; tauto)
     end ])).
-
(rewrite unite_pairs_t_union in Hsub; try resolve_not_union; destruct (union_in_nf__components_in_nf _ _ Hnf2) as [Hnf21 Hnf22];
  apply sub_r_nf_union_l__inv in Hsub).
(* Failed. *)

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
Close Scope btjd_scope.
Open Scope btjd_scope.
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

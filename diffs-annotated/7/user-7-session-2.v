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
(apply sub_r_nf_union_l__inv in Hsub2; try assumption).
Check unite_pairs_union_t.
Check sub_r_nf_union_l__inv.
(intros Hsub12).
(remember (TPair t1' t2') as tx eqn:Heqx ).
(remember (TPair t1 t2) as ty eqn:Heqy ).
(induction Hsub12; inversion Heqx; inversion Heqy; subst).
+
(intros t3 Hsub21).
(remember (TPair t1' t2') as tx eqn:Heqx ).

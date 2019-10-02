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
(induction Hsub12; inversion Heqx; inversion Heqy; subst; try clear Heqx Heqy).
(inversion Hsub22; subst).
specialize (IHHsub11_1 Hsub12_1 t1'0 Hsub21_1 H2).
specialize (IHHsub11_2 Hsub12_2 t2'0 Hsub21_2 H4).
(split; constructor; tauto).
}
{
(* Failed. *)

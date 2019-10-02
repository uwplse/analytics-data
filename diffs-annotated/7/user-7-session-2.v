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
(rewrite (unite_pairs_union_t t1 t0 t2')).
(apply sub_r_nf_union_l__inv in Hsub1; try assumption).
(* Failed. *)

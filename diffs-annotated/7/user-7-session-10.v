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
Lemma sub_r_nf__trans :
  forall tm1 tm2 : ty,
  |- tm1 << tm2 -> InNF( tm1) -> InNF( tm2) -> (forall tl : ty, |- tl << tm1 -> |- tl << tm2) /\ (forall tr : ty, |- tm2 << tr -> |- tm1 << tr).
Proof.
(intros tm1 tm2 Hsub).
(induction Hsub; intros Hnfm1 Hnfm2).
-
tauto.
-
(destruct (in_nf_pair__inv _ _ Hnfm1) as [Hnfmx Hnfmy]).
(* Failed. *)

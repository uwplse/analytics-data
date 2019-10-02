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
(destruct (in_nf_pair__inv _ _ Hnfm1) as [Hnfm11 Hnfm12]).
(destruct (in_nf_pair__inv _ _ Hnfm2) as [Hnfm21 Hnfm22]).
(destruct IHHsub1 as [IHHsub11 IHHsub12]).
(* Failed. *)

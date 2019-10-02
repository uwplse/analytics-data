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
(destruct IHHsub1 as [IHHsub11 IHHsub12]; try assumption).
(split; intros tx Hsub'; [ remember (TPair t1 t2) as ty eqn:Heqy  | remember (TPair t1' t2') as ty eqn:Heqy  ]; induction Hsub'; inversion Heqy;
  subst; try (solve [ constructor; auto ])).
(* Failed. *)

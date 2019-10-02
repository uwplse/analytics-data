Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.AltMatchDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjmi_scope.
(induction k; intros v t; generalize dependent v; induction t; intros v Hm k' Hle;
  try
   match goal with
   | |- |-[ ?k'] ?v <$ TCName _ => apply match_ty_i_cname__inv in Hm; subst; reflexivity
   | |- |-[ ?k'] ?v <$ TPair _ _ => apply match_ty_i_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst; apply match_ty_i_pair; tauto
   | |- |-[ ?k'] ?v <$ TUnion _ _ =>
         apply match_ty_i_union__inv in Hm; destruct Hm as [Hm1| Hm2]; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; tauto
   end).
-
(destruct v; contradiction).
(* Failed. *)

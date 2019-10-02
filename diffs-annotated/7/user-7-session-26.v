Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Theorem value_type__dcdbl : forall t : ty, Decidable.decidable (value_type t).
Proof.
(induction t; try (solve [ left; constructor | right; intros Hcontra; inversion Hcontra ])).
-
(destruct IHt1 as [IHt1| IHt1]; destruct IHt2 as [IHt2| IHt2]; try (solve [ right; intros Hcontra; inversion Hcontra; subst; contradiction ])).
(left; constructor; assumption).
Qed.
(* Auto-generated comment: Failed. *)

Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0281a.BaseDefs.
Require Import BetaJulia.Sub0281a.BaseProps.
Require Import BetaJulia.Sub0281a.BaseMatchProps.
Require Import BetaJulia.Sub0281a.BaseSemSubProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Set Printing Width 148.
Set Printing Width 148.
Lemma fresh_in_ty_var__neq : forall X Y : id, fresh_in_ty X (TVar Y) -> X <> Y.
Proof.
Set Silent.
(intros X Y H).
Unset Silent.
(unfold fresh_in_ty, fresh in H).
(simpl in H).
(destruct (beq_idP X Y)).
-
Show.
Set Printing Width 148.
Check IdSetFacts.singleton_2.
Set Printing Width 148.
Set Printing Width 148.
symmetry in e.
(pose proof (IdSetFacts.singleton_2 e)).
contradiction.
-
assumption.
Qed.
Set Silent.
Lemma match_ty_subst_fresh : forall (X : id) (s : ty) (w : nat) (t v : ty), fresh_in_ty X t -> |-[ w] v <$ t -> |-[ w] v <$ [X := s] t.
Set Printing Width 148.
(intros X s; induction w; induction t; intros v HX Hm;
  try (solve
   [ rewrite subst_cname in *; assumption
   | rewrite subst_pair; destruct (fresh_in_ty_pair__inv _ _ _ HX) as [HX1 HX2]; apply match_ty_pair__inv in Hm;
      destruct Hm as [v1 [v2 [heq [Hm1 Hm2]]]]; subst; apply match_ty_pair; auto
   | rewrite subst_union; destruct (fresh_in_ty_union__inv _ _ _ HX) as [HX1 HX2]; apply match_ty_union__inv in Hm; destruct Hm as [Hm| Hm];
      [ apply match_ty_union_1 | apply match_ty_union_2 ]; auto
   | pose proof (fresh_in_ty_var__neq _ _ HX) as HXi; rewrite subst_var_neq; assumption
   | rewrite subst_ev in *; assumption ])).
Show.
Set Silent.
-
(apply match_ty_exist__0_inv in Hm; contradiction).
Unset Silent.
-
(rewrite subst_equation).
Set Printing Width 148.
(destruct (beq_idP X i) as [HXi| HXi]; try assumption).
(destruct (IdSet.mem i (FV s)) as [Hmem| Hmem]).
Show.
(destruct (IdSet.mem i (FV s))).

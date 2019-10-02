Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.AltMatchDef.
Require Import BetaJulia.BasicTactics.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Close Scope btjm.
Open Scope btjmi.
(apply sem_eq_k_i__trans with t; assumption).
Qed.
Lemma sem_sub_k_i__trans : forall (k : nat) (t1 t2 t3 : ty), ||-[ k][t1]<= [t2] -> ||-[ k][t2]<= [t3] -> ||-[ k][t1]<= [t3].
Proof.
auto with DBBetaJulia.
Qed.
Lemma value_sem_sub_k_i_union__inv :
  forall v : ty, value_type v -> forall (k : nat) (ta tb : ty), ||-[ k][v]<= [TUnion ta tb] -> ||-[ k][v]<= [ta] \/ ||-[ k][v]<= [tb].
Proof.
(intros v Hv k ta tb Hsem; unfold sem_sub_k_i in Hsem).
(assert (Hm : |-[ k] v <$ v) by (apply match_ty_i__reflexive; assumption)).
specialize (Hsem _ Hm).
(apply match_ty_i_union__inv in Hsem).
(destruct Hsem; [ left | right ]; unfold sem_sub_k_i; intros v' Hm'; apply match_ty_i__transitive_on_value_type with v; assumption).
Qed.
Lemma cname_sem_sub_k_i__sub_d : forall (k : nat) (c : cname) (t2 : ty), ||-[ k][TCName c]<= [t2] -> |- TCName c << t2.
Proof.
(intros k c t2).
(assert (Hva : value_type (TCName c)) by constructor).
(assert (Hma : |-[ k] TCName c <$ TCName c) by (apply match_ty_i__reflexive; assumption)).
(induction t2; intros Hsem; try (solve [ specialize (Hsem _ Hma); destruct k; simpl in Hsem; subst; constructor || contradiction ])).
-
(apply value_sem_sub_k_i_union__inv in Hsem; try assumption).
(destruct Hsem as [Hsem| Hsem]; [ apply union_right_1 | apply union_right_2 ]; auto).
Qed.
Lemma pair_sem_sub_k_i__sub_d :
  forall (k : nat) (ta1 ta2 : ty),
  atom_type (TPair ta1 ta2) ->
  (forall tb1 : ty, ||-[ k][ta1]<= [tb1] -> |- ta1 << tb1) ->
  (forall tb2 : ty, ||-[ k][ta2]<= [tb2] -> |- ta2 << tb2) -> forall t2 : ty, ||-[ k][TPair ta1 ta2]<= [t2] -> |- TPair ta1 ta2 << t2.
Proof.
(intros k ta1 ta2 Hat IH1 IH2).
(pose proof (atom_type__value_type _ Hat) as Hva).

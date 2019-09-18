Time From iris.algebra Require Export cmra.
Time From stdpp Require Export list gmap.
Time From iris.algebra Require Import updates local_updates.
Time From iris.base_logic Require Import base_logic.
Time From iris.algebra Require Import proofmode_classes.
Time Set Default Proof Using "Type".
Time Section cofe.
Time Context `{Countable K} {A : ofeT}.
Time Implicit Type m : gmap K A.
Time Implicit Type i : K.
Time
Instance gmap_dist : (Dist (gmap K A)) :=
 (\206\187 n m1 m2, \226\136\128 i, m1 !! i \226\137\161{n}\226\137\161 m2 !! i).
Time Definition gmap_ofe_mixin : OfeMixin (gmap K A).
Time Proof.
Time split.
Time -
Time (intros m1 m2; split).
Time +
Time by intros Hm n k; apply equiv_dist.
Time +
Time (intros Hm k; apply equiv_dist; intros n; apply Hm).
Time -
Time (intros n; split).
Time +
Time by intros m k.
Time +
Time by intros m1 m2 ? k.
Time +
Time by intros m1 m2 m3 ? ? k; trans m2 !! k.
Time -
Time by intros n m1 m2 ? k; apply dist_S.
Time Qed.
Time Canonical Structure gmapC : ofeT := OfeT (gmap K A) gmap_ofe_mixin.
Time #[program]
Definition gmap_chain (c : chain gmapC) (k : K) : 
  chain (optionC A) := {| chain_car := fun n => c n !! k |}.
Time Next Obligation.
Time by intros c k n i ?; apply (chain_cauchy c).
Time Qed.
Time
Definition gmap_compl `{Cofe A} : Compl gmapC :=
  \206\187 c, map_imap (\206\187 i _, compl (gmap_chain c i)) (c 0).
Time #[global, program]
Instance gmap_cofe  `{Cofe A}: (Cofe gmapC) := {| compl := gmap_compl |}.
Time Next Obligation.
Time (intros ? n c k).
Time rewrite /compl /gmap_compl lookup_imap.

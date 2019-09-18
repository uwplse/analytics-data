Time From iris.algebra Require Export cmra.
Time From iris.algebra Require Import updates.
Time From stdpp Require Import finite.
Time Set Default Proof Using "Type".
Time
Definition discrete_fun_insert `{EqDecision A} {B : A \226\134\146 ofeT} 
  (x : A) (y : B x) (f : discrete_fun B) : discrete_fun B :=
  \206\187 x',
    match decide (x = x') with
    | left H => eq_rect _ B y _ H
    | right _ => f x'
    end.
Time Instance: (Params (@discrete_fun_insert) 5) := { }.
Time
Definition discrete_fun_singleton `{EqDecision A} 
  {B : A \226\134\146 ucmraT} (x : A) (y : B x) : discrete_fun B :=
  discrete_fun_insert x y \206\181.
Time Instance: (Params (@discrete_fun_singleton) 5) := { }.
Time Section ofe.
Time Context `{Heqdec : EqDecision A} {B : A \226\134\146 ofeT}.
Time Implicit Type x : A.
Time Implicit Types f g : discrete_fun B.
Time #[global]
Instance discrete_funO_ofe_discrete :
 ((\226\136\128 i, OfeDiscrete (B i)) \226\134\146 OfeDiscrete (discrete_funO B)).
Time Proof.
Time (intros HB f f' Heq i).
Time (apply HB, Heq).
Time Qed.
Time #[global]
Instance discrete_fun_insert_ne  x:
 (NonExpansive2 (discrete_fun_insert (B:=B) x)).
Time Proof.
Time (intros n y1 y2 ? f1 f2 ? x'; rewrite /discrete_fun_insert).
Time by destruct (decide _) as [[]| ].
Time Qed.
Time #[global]
Instance discrete_fun_insert_proper  x:
 (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) (discrete_fun_insert (B:=B) x)) :=
 (ne_proper_2 _).
Time
Lemma discrete_fun_lookup_insert f x y : (discrete_fun_insert x y f) x = y.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0>
 rewrite /discrete_fun_insert; destruct (decide _) as [Hx| ] ; last  done).
Time by rewrite (proof_irrel Hx eq_refl).
Time Qed.
Time
Lemma discrete_fun_lookup_insert_ne f x x' y :
  x \226\137\160 x' \226\134\146 (discrete_fun_insert x y f) x' = f x'.
Time Proof.
Time by rewrite /discrete_fun_insert; destruct (decide _).
Time Qed.
Time #[global]
Instance discrete_fun_insert_discrete  f x y:
 (Discrete f \226\134\146 Discrete y \226\134\146 Discrete (discrete_fun_insert x y f)).
Time Proof.
Time (intros ? ? g Heq x'; destruct (decide (x = x')) as [->| ]).
Time -
Time rewrite discrete_fun_lookup_insert.
Time apply : {}discrete {}.
Time by rewrite -(Heq x') discrete_fun_lookup_insert.
Time -
Time rewrite discrete_fun_lookup_insert_ne //.
Time apply : {}discrete {}.
Time by rewrite -(Heq x') discrete_fun_lookup_insert_ne.
Time Qed.
Time End ofe.
Time Section cmra.
Time Context `{EqDecision A} {B : A \226\134\146 ucmraT}.
Time Implicit Type x : A.
Time Implicit Types f g : discrete_fun B.
Time #[global]
Instance discrete_funR_cmra_discrete :
 ((\226\136\128 i, CmraDiscrete (B i)) \226\134\146 CmraDiscrete (discrete_funR B)).
Time Proof.
Time (intros HB).
Time (split; [ apply _ |  ]).
Time (intros x Hv i).
Time (apply HB, Hv).
Time Qed.
Time #[global]
Instance discrete_fun_singleton_ne  x:
 (NonExpansive (discrete_fun_singleton x : B x \226\134\146 _)).
Time Proof.
Time (intros n y1 y2 ?; apply discrete_fun_insert_ne).
Time done.
Time by apply equiv_dist.
Time Qed.
Time #[global]
Instance discrete_fun_singleton_proper  x:
 (Proper ((\226\137\161) ==> (\226\137\161)) (discrete_fun_singleton x)) := 
 (ne_proper _).
Time
Lemma discrete_fun_lookup_singleton x (y : B x) :
  (discrete_fun_singleton x y) x = y.
Time Proof.
Time by rewrite /discrete_fun_singleton discrete_fun_lookup_insert.
Time Qed.
Time
Lemma discrete_fun_lookup_singleton_ne x x' (y : B x) :
  x \226\137\160 x' \226\134\146 (discrete_fun_singleton x y) x' = \206\181.
Time Proof.
Time
(intros; by rewrite /discrete_fun_singleton discrete_fun_lookup_insert_ne).
Time Qed.
Time #[global]
Instance discrete_fun_singleton_discrete  x (y : B x):
 ((\226\136\128 i, Discrete (\206\181 : B i))
  \226\134\146 Discrete y \226\134\146 Discrete (discrete_fun_singleton x y)).
Time Proof.
Time (apply _).
Time Qed.
Time
Lemma discrete_fun_singleton_validN n x (y : B x) :
  \226\156\147{n} discrete_fun_singleton x y \226\134\148 \226\156\147{n} y.
Time Proof.
Time
(split; [ by move  {}=>/(_ x); rewrite discrete_fun_lookup_singleton |  ]).
Time
(move  {}=>Hx x'; destruct (decide (x = x')) as [->| ]; rewrite
  ?discrete_fun_lookup_singleton ?discrete_fun_lookup_singleton_ne //).
Time by apply ucmra_unit_validN.
Time Qed.
Time
Lemma discrete_fun_core_singleton x (y : B x) :
  core (discrete_fun_singleton x y) \226\137\161 discrete_fun_singleton x (core y).
Time Proof.
Time
(move  {}=>x'; destruct (decide (x = x')) as [->| ]; by rewrite
  discrete_fun_lookup_core ?discrete_fun_lookup_singleton
  ?discrete_fun_lookup_singleton_ne // (core_id_core \226\136\133)).
Time Qed.
Time #[global]
Instance discrete_fun_singleton_core_id  x (y : B x):
 (CoreId y \226\134\146 CoreId (discrete_fun_singleton x y)).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite !core_id_total
 discrete_fun_core_singleton =>{+}->.
Time Qed.
Time
Lemma discrete_fun_op_singleton (x : A) (y1 y2 : B x) :
  discrete_fun_singleton x y1 \226\139\133 discrete_fun_singleton x y2
  \226\137\161 discrete_fun_singleton x (y1 \226\139\133 y2).
Time Proof.
Time (intros x'; destruct (decide (x' = x)) as [->| ]).
Time -
Time by rewrite discrete_fun_lookup_op !discrete_fun_lookup_singleton.
Time -
Time
by rewrite discrete_fun_lookup_op !discrete_fun_lookup_singleton_ne //
 left_id.
Time Qed.
Time
Lemma discrete_fun_insert_updateP x (P : B x \226\134\146 Prop)
  (Q : discrete_fun B \226\134\146 Prop) g y1 :
  y1 ~~>: P
  \226\134\146 (\226\136\128 y2, P y2 \226\134\146 Q (discrete_fun_insert x y2 g))
    \226\134\146 discrete_fun_insert x y1 g ~~>: Q.
Time Proof.
Time (intros Hy1 HP; apply cmra_total_updateP).
Time (intros n gf Hg).
Time (destruct (Hy1 n (Some (gf x))) as (y2, (?, ?))).
Time {
Time move : {}(Hg x) {}.
Time by rewrite discrete_fun_lookup_op discrete_fun_lookup_insert.
Time }
Time (exists (discrete_fun_insert x y2 g); split; [ auto |  ]).
Time
(intros x'; destruct (decide (x' = x)) as [->| ]; rewrite
  discrete_fun_lookup_op ?discrete_fun_lookup_insert //; 
  [  ]).
Time move : {}(Hg x') {}.
Time by rewrite discrete_fun_lookup_op !discrete_fun_lookup_insert_ne.
Time Qed.
Time
Lemma discrete_fun_insert_updateP' x (P : B x \226\134\146 Prop) 
  g y1 :
  y1 ~~>: P
  \226\134\146 discrete_fun_insert x y1 g ~~>:
    (\206\187 g', \226\136\131 y2, g' = discrete_fun_insert x y2 g \226\136\167 P y2).
Time Proof.
Time eauto using discrete_fun_insert_updateP.
Time Qed.
Time
Lemma discrete_fun_insert_update g x y1 y2 :
  y1 ~~> y2 \226\134\146 discrete_fun_insert x y1 g ~~> discrete_fun_insert x y2 g.
Time Proof.
Time
(rewrite !cmra_update_updateP; eauto using discrete_fun_insert_updateP
  with subst).
Time Qed.
Time
Lemma discrete_fun_singleton_updateP x (P : B x \226\134\146 Prop)
  (Q : discrete_fun B \226\134\146 Prop) y1 :
  y1 ~~>: P
  \226\134\146 (\226\136\128 y2, P y2 \226\134\146 Q (discrete_fun_singleton x y2))
    \226\134\146 discrete_fun_singleton x y1 ~~>: Q.
Time Proof.
Time
(rewrite /discrete_fun_singleton; eauto using discrete_fun_insert_updateP).
Time Qed.
Time
Lemma discrete_fun_singleton_updateP' x (P : B x \226\134\146 Prop) 
  y1 :
  y1 ~~>: P
  \226\134\146 discrete_fun_singleton x y1 ~~>:
    (\206\187 g, \226\136\131 y2, g = discrete_fun_singleton x y2 \226\136\167 P y2).
Time Proof.
Time eauto using discrete_fun_singleton_updateP.
Time Qed.
Time
Lemma discrete_fun_singleton_update x (y1 y2 : B x) :
  y1 ~~> y2 \226\134\146 discrete_fun_singleton x y1 ~~> discrete_fun_singleton x y2.
Time Proof.
Time eauto using discrete_fun_insert_update.
Time Qed.
Time
Lemma discrete_fun_singleton_updateP_empty x (P : B x \226\134\146 Prop)
  (Q : discrete_fun B \226\134\146 Prop) :
  \206\181 ~~>: P \226\134\146 (\226\136\128 y2, P y2 \226\134\146 Q (discrete_fun_singleton x y2)) \226\134\146 \206\181 ~~>: Q.
Time Proof.
Time (intros Hx HQ; apply cmra_total_updateP).
Time (intros n gf Hg).
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (Hx n (Some (gf x))) as (y2, (?, ?)) ; first  
 apply Hg).
Time (exists (discrete_fun_singleton x y2); split; [ by apply HQ |  ]).
Time (intros x'; destruct (decide (x' = x)) as [->| ]).
Time -
Time by rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton.
Time -
Time rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton_ne //.
Time (apply Hg).
Time Qed.
Time
Lemma discrete_fun_singleton_updateP_empty' x (P : B x \226\134\146 Prop) :
  \206\181 ~~>: P \226\134\146 \206\181 ~~>: (\206\187 g, \226\136\131 y2, g = discrete_fun_singleton x y2 \226\136\167 P y2).
Time Proof.
Time eauto using discrete_fun_singleton_updateP_empty.
Time Qed.
Time
Lemma discrete_fun_singleton_update_empty x (y : B x) :
  \206\181 ~~> y \226\134\146 \206\181 ~~> discrete_fun_singleton x y.
Time Proof.
Time
(rewrite !cmra_update_updateP; eauto
  using discrete_fun_singleton_updateP_empty with subst).
Time Qed.
Time End cmra.

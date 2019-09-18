Time From iris.algebra Require Export cmra.
Time From iris.algebra Require Export cmra.
Time From iris.algebra Require Export cmra.
Time From iris.algebra Require Import proofmode_classes.
Time From iris.base_logic Require Import base_logic.
Time From stdpp Require Export list.
Time From iris.base_logic Require Import base_logic.
Time From stdpp Require Export list gmap.
Time From iris.algebra Require Import updates local_updates.
Time From iris.base_logic Require Import base_logic.
Time From iris.base_logic Require Import base_logic.
Time Set Default Proof Using "Type".
Time Inductive counting :=
       | Count : forall z : Z, _
       | CountBot : _.
Time #[local]Open Scope Z.
Time
Instance counting_valid : (Valid counting) :=
 (\206\187 x, match x with
       | Count _ => True
       | CountBot => False
       end).
Time
Instance counting_validN : (ValidN counting) :=
 (\206\187 n x, match x with
         | Count _ => True
         | CountBot => False
         end).
Time Instance counting_pcore : (PCore counting) := (\206\187 x, None).
Time
Instance counting_op : (Op counting) :=
 (\206\187 x y,
    match x, y with
    | Count z1, Count z2 =>
        if decide (z1 >= 0 \226\136\167 z2 >= 0) then CountBot
        else if decide ((z1 >= 0 \226\136\168 z2 >= 0) \226\136\167 z1 + z2 < 0) then CountBot
             else Count (z1 + z2)
    | _, _ => CountBot
    end).
Time Canonical Structure countingC := leibnizC counting.
Time #[local]
Ltac
 by_cases :=
  repeat <ssreflect_plugin::ssrtclintros@0>
   match goal with
   | H:counting |- _ => destruct H
   end =>//=; repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=;
   try lia.
Time Lemma counting_ra_mixin : RAMixin counting.
Time Proof.
Time (split; try apply _; try done).
Time From iris.algebra Require Import local_updates.
Time Set Default Proof Using "Type".
Time #[local]Arguments pcore _ _ !_ /.
Time #[local]Arguments cmra_pcore _ !_ /.
Time #[local]Arguments validN _ _ _ !_ /.
Time #[local]Arguments valid _ _ !_ /.
Time #[local]Arguments cmra_validN _ _ !_ /.
Time #[local]Arguments cmra_valid _ !_ /.
Time
Inductive csum (A B : Type) :=
  | Cinl : A \226\134\146 csum A B
  | Cinr : B \226\134\146 csum A B
  | CsumBot : csum A B.
Time Arguments Cinl {_} {_} _.
Time Arguments Cinr {_} {_} _.
Time Arguments CsumBot {_} {_}.
Time Instance: (Params (@Cinl) 2) := { }.
Time Instance: (Params (@Cinr) 2) := { }.
Time Instance: (Params (@CsumBot) 2) := { }.
Time From iris.algebra Require Import updates local_updates.
Time Set Default Proof Using "Type".
Time Section cofe.
Time
Instance maybe_Cinl  {A} {B}: (Maybe (@Cinl A B)) :=
 (\206\187 x, match x with
       | Cinl a => Some a
       | _ => None
       end).
Time
Instance maybe_Cinr  {A} {B}: (Maybe (@Cinr A B)) :=
 (\206\187 x, match x with
       | Cinr b => Some b
       | _ => None
       end).
Time Section cofe.
Time Context {A B : ofeT}.
Time Implicit Type a : A.
Time Implicit Type b : B.
Time
Inductive csum_equiv : Equiv (csum A B) :=
  | Cinl_equiv : forall a a', a \226\137\161 a' \226\134\146 Cinl a \226\137\161 Cinl a'
  | Cinr_equiv : forall b b', b \226\137\161 b' \226\134\146 Cinr b \226\137\161 Cinr b'
  | CsumBot_equiv : CsumBot \226\137\161 CsumBot.
Time Context {A : ofeT}.
Time Implicit Type l : list A.
Time Instance list_dist : (Dist (list A)) := (\206\187 n, Forall2 (dist n)).
Time
Lemma list_dist_lookup n l1 l2 : l1 \226\137\161{n}\226\137\161 l2 \226\134\148 (\226\136\128 i, l1 !! i \226\137\161{n}\226\137\161 l2 !! i).
Time Proof.
Time setoid_rewrite dist_option_Forall2.
Time Existing Instance csum_equiv.
Time
Inductive csum_dist : Dist (csum A B) :=
  | Cinl_dist : forall n a a', a \226\137\161{n}\226\137\161 a' \226\134\146 Cinl a \226\137\161{n}\226\137\161 Cinl a'
  | Cinr_dist : forall n b b', b \226\137\161{n}\226\137\161 b' \226\134\146 Cinr b \226\137\161{n}\226\137\161 Cinr b'
  | CsumBot_dist : forall n, CsumBot \226\137\161{n}\226\137\161 CsumBot.
Time Existing Instance csum_dist.
Time #[global]Instance Cinl_ne : (NonExpansive (@Cinl A B)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance Cinl_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (@Cinl A B)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance Cinl_inj : (Inj (\226\137\161) (\226\137\161) (@Cinl A B)).
Time Proof.
Time by inversion_clear 1.
Time (apply Forall2_lookup).
Time Qed.
Time #[global]Instance cons_ne : (NonExpansive2 (@cons A)) := _.
Time From iris.algebra Require Import proofmode_classes.
Time Set Default Proof Using "Type".
Time Section cofe.
Time Context `{Countable K} {A : ofeT}.
Time Implicit Type m : gmap K A.
Time Implicit Type i : K.
Time
Instance gmap_dist : (Dist (gmap K A)) :=
 (\206\187 n m1 m2, \226\136\128 i, m1 !! i \226\137\161{n}\226\137\161 m2 !! i).
Time Qed.
Time #[global]Instance Cinl_inj_dist  n: (Inj (dist n) (dist n) (@Cinl A B)).
Time Proof.
Time by inversion_clear 1.
Time Definition gmap_ofe_mixin : OfeMixin (gmap K A).
Time Proof.
Time split.
Time -
Time (intros m1 m2; split).
Time +
Time by intros Hm n k; apply equiv_dist.
Time -
Time (intros x y z).
Time rewrite /op /counting_op.
Time Qed.
Time #[global]Instance Cinr_ne : (NonExpansive (@Cinr A B)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance app_ne : (NonExpansive2 (@app A)) := _.
Time +
Time (intros Hm k; apply equiv_dist; intros n; apply Hm).
Time by_cases.
Time #[global]Instance Cinr_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (@Cinr A B)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance Cinr_inj : (Inj (\226\137\161) (\226\137\161) (@Cinr A B)).
Time Proof.
Time by inversion_clear 1.
Time Qed.
Time -
Time (intros n; split).
Time +
Time by intros m k.
Time +
Time by intros m1 m2 ? k.
Time #[global]Instance Cinr_inj_dist  n: (Inj (dist n) (dist n) (@Cinr A B)).
Time Proof.
Time by inversion_clear 1.
Time +
Time by intros m1 m2 m3 ? ? k; trans m2 !! k.
Time Qed.
Time Definition csum_ofe_mixin : OfeMixin (csum A B).
Time Proof.
Time split.
Time -
Time (intros mx my; split).
Time +
Time by destruct 1; constructor; try apply equiv_dist.
Time #[global]
Instance length_ne  n: (Proper (dist n ==> (=)) (@length A)) := _.
Time #[global]Instance tail_ne : (NonExpansive (@tail A)) := _.
Time -
Time by intros n m1 m2 ? k; apply dist_S.
Time +
Time
(intros Hxy; feed inversion Hxy 0; subst; constructor; try done;
  <ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n; by feed inversion
  Hxy n).
Time Qed.
Time Canonical Structure gmapC : ofeT := OfeT (gmap K A) gmap_ofe_mixin.
Time #[program]
Definition gmap_chain (c : chain gmapC) (k : K) : 
  chain (optionC A) := {| chain_car := fun n => c n !! k |}.
Time Next Obligation.
Time by intros c k n i ?; apply (chain_cauchy c).
Time Qed.
Time #[global]Instance take_ne : (NonExpansive (@take A n)) := _.
Time
Definition gmap_compl `{Cofe A} : Compl gmapC :=
  \206\187 c, map_imap (\206\187 i _, compl (gmap_chain c i)) (c 0).
Time #[global, program]
Instance gmap_cofe  `{Cofe A}: (Cofe gmapC) := {| compl := gmap_compl |}.
Time Next Obligation.
Time (intros ? n c k).
Time rewrite /compl /gmap_compl lookup_imap.
Time
(feed inversion \206\187 H, chain_cauchy c 0 n H k; simplify_option_eq; auto
  with lia).
Time #[global]Instance drop_ne : (NonExpansive (@drop A n)) := _.
Time -
Time (intros n; split).
Time +
Time by intros [| a| ]; constructor.
Time +
Time by destruct 1; constructor.
Time +
Time (destruct 1; inversion_clear 1; constructor; etrans; eauto).
Time #[global]Instance head_ne : (NonExpansive (head (A:=A))).
Time Proof.
Time (destruct 1; by constructor).
Time Qed.
Time #[global]
Instance list_lookup_ne  i: (NonExpansive (lookup (M:=list A) i)).
Time Proof.
Time (intros ? ? ? ?).
Time by apply dist_option_Forall2, Forall2_lookup.
Time Qed.
Time #[global]
Instance list_alter_ne  n f i:
 (Proper (dist n ==> dist n) f
  \226\134\146 Proper (dist n ==> dist n) (alter (M:=list A) f i)) := _.
Time #[global]
Instance list_insert_ne  i: (NonExpansive2 (insert (M:=list A) i)) := _.
Time by rewrite conv_compl /=; apply reflexive_eq.
Time -
Time by inversion_clear 1; constructor; apply dist_S.
Time Qed.
Time #[global]
Instance list_inserts_ne  i: (NonExpansive2 (@list_inserts A i)) := _.
Time #[global]
Instance gmap_ofe_discrete : (OfeDiscrete A \226\134\146 OfeDiscrete gmapC).
Time Proof.
Time (intros ? m m' ? i).
Time by apply (discrete _).
Time Qed.
Time Qed.
Time #[global]Instance gmapC_leibniz : (LeibnizEquiv A \226\134\146 LeibnizEquiv gmapC).
Time Proof.
Time (intros; change_no_check (LeibnizEquiv (gmap K A)); apply _).
Time #[global]
Instance list_delete_ne  i: (NonExpansive (delete (M:=list A) i)) := _.
Time Qed.
Time Canonical Structure csumC : ofeT := OfeT (csum A B) csum_ofe_mixin.
Time #[program]
Definition csum_chain_l (c : chain csumC) (a : A) : 
  chain A :=
  {| chain_car := fun n => match c n with
                           | Cinl a' => a'
                           | _ => a
                           end |}.
Time Next Obligation.
Time (intros c a n i ?; simpl).
Time by destruct (chain_cauchy c n i).
Time #[global]
Instance lookup_ne  k: (NonExpansive (lookup k : gmap K A \226\134\146 option A)).
Time Proof.
Time by intros m1 m2.
Time Qed.
Time #[program]
Definition csum_chain_r (c : chain csumC) (b : B) : 
  chain B :=
  {| chain_car := fun n => match c n with
                           | Cinr b' => b'
                           | _ => b
                           end |}.
Time Next Obligation.
Time Qed.
Time #[global]
Instance lookup_proper  k:
 (Proper ((\226\137\161) ==> (\226\137\161)) (lookup k : gmap K A \226\134\146 option A)) := _.
Time (intros c b n i ?; simpl).
Time by destruct (chain_cauchy c n i).
Time #[global]Instance option_list_ne : (NonExpansive (@option_list A)).
Time Proof.
Time (intros ? ? ? ?; by apply Forall2_option_list, dist_option_Forall2).
Time #[global]
Instance alter_ne  f k n:
 (Proper (dist n ==> dist n) f \226\134\146 Proper (dist n ==> dist n) (alter f k)).
Time Qed.
Time
Definition csum_compl `{Cofe A} `{Cofe B} : Compl csumC :=
  \206\187 c,
    match c 0 with
    | Cinl a => Cinl (compl (csum_chain_l c a))
    | Cinr b => Cinr (compl (csum_chain_r c b))
    | CsumBot => CsumBot
    end.
Time Qed.
Time #[global]
Instance list_filter_ne  n P `{\226\136\128 x, Decision (P x)}:
 (Proper (dist n ==> iff) P
  \226\134\146 Proper (dist n ==> dist n) (filter (B:=list A) P)) := _.
Time Proof.
Time (intros ? m m' Hm k').
Time by destruct (decide (k = k')); simplify_map_eq; rewrite (Hm k').
Time #[global, program]
Instance csum_cofe  `{Cofe A} `{Cofe B}: (Cofe csumC) :=
 {| compl := csum_compl |}.
Time Next Obligation.
Time (intros ? ? n c; rewrite /compl /csum_compl).
Time
(<ssreflect_plugin::ssrtclseq@0> feed inversion chain_cauchy c 0 n ; first 
  auto with lia; constructor).
Time #[global]Instance replicate_ne : (NonExpansive (@replicate A n)) := _.
Time +
Time #[global]Instance reverse_ne : (NonExpansive (@reverse A)) := _.
Time rewrite (conv_compl n (csum_chain_l c a')) /=.
Time #[global]Instance last_ne : (NonExpansive (@last A)).
Time Proof.
Time (intros ? ? ? ?; by apply dist_option_Forall2, Forall2_last).
Time (destruct (c n); naive_solver).
Time Qed.
Time #[global]Instance resize_ne  n: (NonExpansive2 (@resize A n)) := _.
Time +
Time rewrite (conv_compl n (csum_chain_r c b')) /=.
Time
Lemma list_dist_cons_inv_l n x l k :
  x :: l \226\137\161{n}\226\137\161 k \226\134\146 \226\136\131 y k', x \226\137\161{n}\226\137\161 y \226\136\167 l \226\137\161{n}\226\137\161 k' \226\136\167 k = y :: k'.
Time Proof.
Time (apply Forall2_cons_inv_l).
Time (destruct (c n); naive_solver).
Time Qed.
Time
Lemma list_dist_cons_inv_r n l k y :
  l \226\137\161{n}\226\137\161 y :: k \226\134\146 \226\136\131 x l', x \226\137\161{n}\226\137\161 y \226\136\167 l' \226\137\161{n}\226\137\161 k \226\136\167 l = x :: l'.
Time Proof.
Time (apply Forall2_cons_inv_r).
Time Qed.
Time Definition list_ofe_mixin : OfeMixin (list A).
Time Proof.
Time split.
Time -
Time (intros l k).
Time rewrite equiv_Forall2 -Forall2_forall.
Time (split; induction 1; constructor; intros; try apply equiv_dist; auto).
Time -
Time (apply _).
Time Qed.
Time -
Time rewrite /dist /list_dist.
Time eauto using Forall2_impl, dist_S.
Time #[global]
Instance csum_ofe_discrete :
 (OfeDiscrete A \226\134\146 OfeDiscrete B \226\134\146 OfeDiscrete csumC).
Time Proof.
Time by inversion_clear 3; constructor; apply (discrete _).
Time Qed.
Time Canonical Structure listC := OfeT (list A) list_ofe_mixin.
Time
Fixpoint list_compl_go `{!Cofe A} (c0 : list A) (c : chain listC) : listC :=
  match c0 with
  | [] => []
  | x :: c0 =>
      compl (chain_map (default x \226\136\152 head) c)
      :: list_compl_go c0 (chain_map tail c)
  end.
Time Qed.
Time #[global]
Instance csum_leibniz :
 (LeibnizEquiv A \226\134\146 LeibnizEquiv B \226\134\146 LeibnizEquiv csumC).
Time Proof.
Time by destruct 3; f_equal; apply leibniz_equiv.
Time Qed.
Time #[global]Instance Cinl_discrete  a: (Discrete a \226\134\146 Discrete (Cinl a)).
Time Proof.
Time by inversion_clear 2; constructor; apply (discrete _).
Time Qed.
Time #[global]Instance Cinr_discrete  b: (Discrete b \226\134\146 Discrete (Cinr b)).
Time Proof.
Time by inversion_clear 2; constructor; apply (discrete _).
Time Qed.
Time End cofe.
Time Qed.
Time Arguments csumC : clear implicits.
Time
Definition csum_map {A} {A'} {B} {B'} (fA : A \226\134\146 A') 
  (fB : B \226\134\146 B') (x : csum A B) : csum A' B' :=
  match x with
  | Cinl a => Cinl (fA a)
  | Cinr b => Cinr (fB b)
  | CsumBot => CsumBot
  end.
Time Instance: (Params (@csum_map) 4) := { }.
Time Lemma csum_map_id {A} {B} (x : csum A B) : csum_map id id x = x.
Time #[global]
Instance insert_ne  i: (NonExpansive2 (insert (M:=gmap K A) i)).
Time Proof.
Time Proof.
Time by destruct x.
Time Qed.
Time
Lemma csum_map_compose {A} {A'} {A''} {B} {B'} {B''} 
  (f : A \226\134\146 A') (f' : A' \226\134\146 A'') (g : B \226\134\146 B') (g' : B' \226\134\146 B'') 
  (x : csum A B) :
  csum_map (f' \226\136\152 f) (g' \226\136\152 g) x = csum_map f' g' (csum_map f g x).
Time
(intros n x y ? m m' ? j; destruct (decide (i = j)); simplify_map_eq;
  [ by constructor | by apply lookup_ne ]).
Time Proof.
Time by destruct x.
Time Qed.
Time
Lemma csum_map_ext {A A' B B' : ofeT} (f f' : A \226\134\146 A') 
  (g g' : B \226\134\146 B') x :
  (\226\136\128 x, f x \226\137\161 f' x) \226\134\146 (\226\136\128 x, g x \226\137\161 g' x) \226\134\146 csum_map f g x \226\137\161 csum_map f' g' x.
Time Proof.
Time by destruct x; constructor.
Time Qed.
Time
Instance csum_map_cmra_ne  {A A' B B' : ofeT} n:
 (Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==> dist n ==> dist n)
    (@csum_map A A' B B')).
Time Proof.
Time
(intros f f' Hf g g' Hg []; destruct 1; constructor; by apply Hf || apply Hg).
Time Qed.
Time
Definition csumC_map {A} {A'} {B} {B'} (f : A -n> A') 
  (g : B -n> B') : csumC A B -n> csumC A' B' := CofeMor (csum_map f g).
Time Qed.
Time #[global]
Instance singleton_ne  i: (NonExpansive (singletonM i : A \226\134\146 gmap K A)).
Time Proof.
Time by intros ? ? ? ?; apply insert_ne.
Time Qed.
Time #[global]Instance delete_ne  i: (NonExpansive (delete (M:=gmap K A) i)).
Time Proof.
Time
(intros n m m' ? j; destruct (decide (i = j)); simplify_map_eq;
  [ by constructor | by apply lookup_ne ]).
Time Qed.
Time #[global]Instance gmap_empty_discrete : (Discrete (\226\136\133 : gmap K A)).
Time Proof.
Time (intros m Hm i; specialize (Hm i); rewrite lookup_empty in  {} Hm |- *).
Time (inversion_clear Hm; constructor).
Time Qed.
Time #[global]
Instance gmap_lookup_discrete  m i: (Discrete m \226\134\146 Discrete (m !! i)).
Time Proof.
Time (intros ? [x| ] Hx; [  | by symmetry; apply : {}discrete {} ]).
Time
Instance csumC_map_ne  A A' B B': (NonExpansive2 (@csumC_map A A' B B')).
Time
(assert (m \226\137\161{0}\226\137\161 <[i:=x]> m) by by
  symmetry in Hx; inversion Hx; ofe_subst; rewrite insert_id).
Time Proof.
Time by intros n f f' Hf g g' Hg []; constructor.
Time Qed.
Time Section cmra.
Time Context {A B : cmraT}.
Time Implicit Type a : A.
Time Implicit Type b : B.
Time
Instance csum_valid : (Valid (csum A B)) :=
 (\206\187 x, match x with
       | Cinl a => \226\156\147 a
       | Cinr b => \226\156\147 b
       | CsumBot => False
       end).
Time
Instance csum_validN : (ValidN (csum A B)) :=
 (\206\187 n x,
    match x with
    | Cinl a => \226\156\147{n} a
    | Cinr b => \226\156\147{n} b
    | CsumBot => False
    end).
Time
Instance csum_pcore : (PCore (csum A B)) :=
 (\206\187 x,
    match x with
    | Cinl a => Cinl <$> pcore a
    | Cinr b => Cinr <$> pcore b
    | CsumBot => Some CsumBot
    end).
Time
Instance csum_op : (Op (csum A B)) :=
 (\206\187 x y,
    match x, y with
    | Cinl a, Cinl a' => Cinl (a \226\139\133 a')
    | Cinr b, Cinr b' => Cinr (b \226\139\133 b')
    | _, _ => CsumBot
    end).
Time Lemma Cinl_op a a' : Cinl a \226\139\133 Cinl a' = Cinl (a \226\139\133 a').
Time Proof.
Time done.
Time Qed.
Time Lemma Cinr_op b b' : Cinr b \226\139\133 Cinr b' = Cinr (b \226\139\133 b').
Time Proof.
Time done.
Time Qed.
Time
Lemma csum_included x y :
  x \226\137\188 y
  \226\134\148 y = CsumBot
    \226\136\168 (\226\136\131 a a', x = Cinl a \226\136\167 y = Cinl a' \226\136\167 a \226\137\188 a')
      \226\136\168 (\226\136\131 b b', x = Cinr b \226\136\167 y = Cinr b' \226\136\167 b \226\137\188 b').
Time Proof.
Time split.
Time -
Time (unfold included).
Time
(intros [[a'| b'| ] Hy]; destruct x as [a| b| ]; inversion_clear Hy; eauto 
  10).
Time by rewrite (discrete m (<[i:=x]> m)) // lookup_insert.
Time Qed.
Time #[global]
Instance gmap_insert_discrete  m i x:
 (Discrete x \226\134\146 Discrete m \226\134\146 Discrete (<[i:=x]> m)).
Time Proof.
Time (intros ? ? m' Hm j; destruct (decide (i = j)); simplify_map_eq).
Time {
Time by apply : {}discrete {}; rewrite -Hm lookup_insert.
Time }
Time by apply : {}discrete {}; rewrite -Hm lookup_insert_ne.
Time #[global, program]
Instance list_cofe  `{!Cofe A}: (Cofe listC) :=
 {| compl := fun c => list_compl_go (c 0) c |}.
Time Next Obligation.
Time (intros ? n c; rewrite /compl).
Time (assert (Hc0 : c 0 \226\137\161{0}\226\137\161 c n) by (symmetry; apply chain_cauchy; lia)).
Time revert Hc0.
Time (<ssreflect_plugin::ssrtclintros@0> generalize (c 0) =>c0).
Time Qed.
Time revert c.
Time
(<ssreflect_plugin::ssrtclintros@0> induction c0 as [| x c0 IH] =>c Hc0 /=).
Time {
Time by inversion Hc0.
Time #[global]
Instance gmap_singleton_discrete  i x:
 (Discrete x \226\134\146 Discrete ({[i := x]} : gmap K A)) := _.
Time Lemma insert_idN n m i x : m !! i \226\137\161{n}\226\137\161 Some x \226\134\146 <[i:=x]> m \226\137\161{n}\226\137\161 m.
Time -
Time
(intros [->| [(a, (a', (->, (->, (c, ?)))))| (b, (b', (->, (->, (c, ?)))))]]).
Time }
Time (apply list_dist_cons_inv_l in Hc0 as (x', (xs', (Hx, (Hc0, Hcn))))).
Time Proof.
Time (intros (y', (?, ->))%dist_Some_inv_r').
Time +
Time (destruct x; exists CsumBot; constructor).
Time +
Time (exists (Cinl c); by constructor).
Time +
Time (exists (Cinr c); by constructor).
Time rewrite Hcn.
Time f_equiv.
Time Qed.
Time by rewrite insert_id.
Time
Lemma csum_includedN n x y :
  x \226\137\188{n} y
  \226\134\148 y = CsumBot
    \226\136\168 (\226\136\131 a a', x = Cinl a \226\136\167 y = Cinl a' \226\136\167 a \226\137\188{n} a')
      \226\136\168 (\226\136\131 b b', x = Cinr b \226\136\167 y = Cinr b' \226\136\167 b \226\137\188{n} b').
Time f_equal.
Time -
Time by rewrite conv_compl /= Hcn /=.
Time Qed.
Time End cofe.
Time -
Time rewrite IH /= ?Hcn //.
Time Arguments gmapC _ {_} {_} _.
Time Section cmra.
Time Context `{Countable K} {A : cmraT}.
Time Implicit Type m : gmap K A.
Time lia.
Time Instance gmap_unit : (Unit (gmap K A)) := (\226\136\133 : gmap K A).
Time Instance gmap_op : (Op (gmap K A)) := (merge op).
Time Instance gmap_pcore : (PCore (gmap K A)) := (\206\187 m, Some (omap pcore m)).
Time Instance gmap_valid : (Valid (gmap K A)) := (\206\187 m, \226\136\128 i, \226\156\147 (m !! i)).
Time
Instance gmap_validN : (ValidN (gmap K A)) := (\206\187 n m, \226\136\128 i, \226\156\147{n} (m !! i)).
Time -
Time (intros x y).
Time rewrite /op /counting_op.
Time by_cases.
Time Lemma lookup_op m1 m2 i : (m1 \226\139\133 m2) !! i = m1 !! i \226\139\133 m2 !! i.
Time Proof.
Time by apply lookup_merge.
Time Qed.
Time Lemma lookup_core m i : core m !! i = core (m !! i).
Time Proof.
Time by apply lookup_omap.
Time Qed.
Time Qed.
Time
Lemma lookup_included (m1 m2 : gmap K A) : m1 \226\137\188 m2 \226\134\148 (\226\136\128 i, m1 !! i \226\137\188 m2 !! i).
Time Proof.
Time
(split; [ by intros [m Hm] i; exists (m !! i); rewrite -lookup_op Hm |  ]).
Time #[global]
Instance list_ofe_discrete : (OfeDiscrete A \226\134\146 OfeDiscrete listC).
Time Proof.
Time (induction 2; constructor; try apply (discrete _); auto).
Time Qed.
Time #[global]Instance nil_discrete : (Discrete (@nil A)).
Time Proof.
Time (inversion_clear 1; constructor).
Time Qed.
Time #[global]
Instance cons_discrete  x l: (Discrete x \226\134\146 Discrete l \226\134\146 Discrete (x :: l)).
Time Proof.
Time (intros ? ?; inversion_clear 1; constructor; by apply discrete).
Time revert m2.
Time
(<ssreflect_plugin::ssrtclintros@0>
 induction m1 as [| i x m Hi IH] using map_ind =>m2 Hm).
Time {
Time Qed.
Time End cofe.
Time exists m2.
Time by rewrite left_id.
Time }
Time (destruct (IH (delete i m2)) as [m2' Hm2']).
Time {
Time (intros j).
Time (move : {}(Hm j) {}; destruct (decide (i = j)) as [->| ]).
Time Arguments listC : clear implicits.
Time
Lemma list_fmap_ext_ne {A} {B : ofeT} (f g : A \226\134\146 B) 
  (l : list A) n : (\226\136\128 x, f x \226\137\161{n}\226\137\161 g x) \226\134\146 f <$> l \226\137\161{n}\226\137\161 g <$> l.
Time Proof.
Time (intros Hf).
Time by apply Forall2_fmap, Forall_Forall2, Forall_true.
Time Qed.
Time Proof.
Time split.
Time -
Time (unfold includedN).
Time
(intros [[a'| b'| ] Hy]; destruct x as [a| b| ]; inversion_clear Hy; eauto 
  10).
Time
Instance list_fmap_ne  {A B : ofeT} (f : A \226\134\146 B) n:
 (Proper (dist n ==> dist n) f
  \226\134\146 Proper (dist n ==> dist n) (fmap (M:=list) f)).
Time Proof.
Time (intros Hf l k ?; by eapply Forall2_fmap, Forall2_impl; eauto).
Time -
Time (intros _).
Time rewrite Hi.
Time apply : {}ucmra_unit_least {}.
Time -
Time rewrite lookup_insert_ne // lookup_delete_ne //.
Time Qed.
Time
Definition listC_map {A} {B} (f : A -n> B) : listC A -n> listC B :=
  CofeMor (fmap f : listC A \226\134\146 listC B).
Time }
Time (destruct (Hm i) as [my Hi']; simplify_map_eq).
Time
(<ssreflect_plugin::ssrtclintros@0> exists (partial_alter (\206\187 _, my) i m2')
  =>j; destruct (decide (i = j)) as [->| ]).
Time -
Time by rewrite Hi' lookup_op lookup_insert lookup_partial_alter.
Time Instance listC_map_ne  A B: (NonExpansive (@listC_map A B)).
Time Proof.
Time (intros n f g ? l).
Time by apply list_fmap_ext_ne.
Time Qed.
Time #[program]
Definition listCF (F : cFunctor) : cFunctor :=
  {|
  cFunctor_car := fun A _ B _ => listC (cFunctor_car F A B);
  cFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg => listC_map (cFunctor_map F fg) |}.
Time -
Time move : {}(Hm2' j) {}.
Time
by rewrite !lookup_op lookup_delete_ne // lookup_insert_ne //
 lookup_partial_alter_ne.
Time f_equal.
Time lia.
Time -
Time (intros x y).
Time rewrite /op /counting_op /valid.
Time by_cases.
Time Qed.
Time Qed.
Time -
Time
(intros [->| [(a, (a', (->, (->, (c, ?)))))| (b, (b', (->, (->, (c, ?)))))]]).
Time +
Time (destruct x; exists CsumBot; constructor).
Time +
Time (exists (Cinl c); by constructor).
Time +
Time (exists (Cinr c); by constructor).
Time Qed.
Time Lemma gmap_cmra_mixin : CmraMixin (gmap K A).
Time Proof.
Time (apply cmra_total_mixin).
Time -
Time eauto.
Time -
Time (intros n m1 m2 m3 Hm i; by rewrite !lookup_op (Hm i)).
Time -
Time Canonical Structure countingR := discreteR counting counting_ra_mixin.
Time #[global]Instance counting_cmra_discrete : (CmraDiscrete countingR).
Time Proof.
Time (apply discrete_cmra_discrete).
Time Qed.
Time Lemma counting_op' (x y : countingR) : x \226\139\133 y = counting_op x y.
Time Proof.
Time done.
Time Qed.
Time Lemma counting_valid' (x : countingR) : \226\156\147 x \226\134\148 counting_valid x.
Time Proof.
Time done.
Time Qed.
Time Next Obligation.
Time
by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply listC_map_ne, cFunctor_ne.
Time (intros n m1 m2 Hm i; by rewrite !lookup_core (Hm i)).
Time Lemma counting_validN' n (x : countingR) : \226\156\147{n} x \226\134\148 counting_validN n x.
Time Proof.
Time done.
Time Qed.
Time #[global]
Instance is_op_counting  z:
 (z >= 0 \226\134\146 IsOp' (Count z) (Count (z + 1)) (Count (- 1))).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IsOp' /IsOp counting_op' =>?).
Time rewrite //=.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x).
Time rewrite /= -{+2}(list_fmap_id x).
Time (<ssreflect_plugin::ssrtclintros@0> apply list_fmap_equiv_ext =>y).
Time (apply cFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -list_fmap_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply list_fmap_equiv_ext =>y;
  apply cFunctor_compose).
Time Qed.
Time by_cases.
Time
Instance listCF_contractive  F:
 (cFunctorContractive F \226\134\146 cFunctorContractive (listCF F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply listC_map_ne, cFunctor_contractive.
Time Qed.
Time -
Time (intros n m1 m2 Hm ? i; by rewrite -(Hm i)).
Time Lemma csum_cmra_mixin : CmraMixin (csum A B).
Time Proof.
Time Section cmra.
Time Context {A : ucmraT}.
Time Implicit Type l : list A.
Time #[local]Arguments op _ _ !_ !_ / : simpl nomatch.
Time
Instance list_op : (Op (list A)) :=
 (fix go l1 l2 :=
    let _ : Op _ := @go in
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | x :: l1, y :: l2 => x \226\139\133 y :: l1 \226\139\133 l2
    end).
Time Instance list_pcore : (PCore (list A)) := (\206\187 l, Some (core <$> l)).
Time Instance list_valid : (Valid (list A)) := (Forall (\206\187 x, \226\156\147 x)).
Time Instance list_validN : (ValidN (list A)) := (\206\187 n, Forall (\206\187 x, \226\156\147{n} x)).
Time split.
Time -
Time (intros [] n; destruct 1; constructor; by ofe_subst).
Time Lemma cons_valid l x : \226\156\147 (x :: l) \226\134\148 \226\156\147 x \226\136\167 \226\156\147 l.
Time Proof.
Time (apply Forall_cons).
Time Qed.
Time Lemma cons_validN n l x : \226\156\147{n} (x :: l) \226\134\148 \226\156\147{n} x \226\136\167 \226\156\147{n} l.
Time Proof.
Time (apply Forall_cons).
Time Qed.
Time Lemma app_valid l1 l2 : \226\156\147 (l1 ++ l2) \226\134\148 \226\156\147 l1 \226\136\167 \226\156\147 l2.
Time Proof.
Time (apply Forall_app).
Time Qed.
Time Lemma app_validN n l1 l2 : \226\156\147{n} (l1 ++ l2) \226\134\148 \226\156\147{n} l1 \226\136\167 \226\156\147{n} l2.
Time Proof.
Time (apply Forall_app).
Time Qed.
Time Lemma list_lookup_valid l : \226\156\147 l \226\134\148 (\226\136\128 i, \226\156\147 (l !! i)).
Time Proof.
Time (rewrite {+1}/valid /list_valid Forall_lookup; split).
Time -
Time (intros m; split).
Time -
Time (intros Hl i).
Time by destruct (l !! i) as [x| ] eqn:?; [ apply (Hl i) |  ].
Time +
Time by intros ? n i; apply cmra_valid_validN.
Time +
Time
(intros Hm i; <ssreflect_plugin::ssrtclintros@0> apply cmra_valid_validN =>n;
  apply Hm).
Time -
Time (intros n m Hm i; apply cmra_validN_S, Hm).
Time -
Time (intros Hl i x Hi).
Time (move : {}(Hl i) {}; by rewrite Hi).
Time Qed.
Time Lemma list_lookup_validN n l : \226\156\147{n} l \226\134\148 (\226\136\128 i, \226\156\147{n} (l !! i)).
Time Proof.
Time (rewrite {+1}/validN /list_validN Forall_lookup; split).
Time -
Time by intros m1 m2 m3 i; rewrite !lookup_op assoc.
Time -
Time (intros Hl i).
Time by destruct (l !! i) as [x| ] eqn:?; [ apply (Hl i) |  ].
Time -
Time (intros Hl i x Hi).
Time (move : {}(Hl i) {}; by rewrite Hi).
Time Qed.
Time Lemma list_lookup_op l1 l2 i : (l1 \226\139\133 l2) !! i = l1 !! i \226\139\133 l2 !! i.
Time Proof.
Time revert i l2.
Time
(induction l1 as [| x l1]; intros [| i] [| y l2]; by rewrite /= ?left_id_L
  ?right_id_L).
Time f_equal.
Time lia.
Time Qed.
Time -
Time by intros m1 m2 i; rewrite !lookup_op comm.
Time #[global]
Instance is_op_counting'  (n : nat):
 (IsOp' (Count n) (Count (S n)) (Count (- 1))).
Time Proof.
Time rewrite /IsOp' /IsOp counting_op' //=.
Time -
Time (intros ? ? ? ? [n a a' Ha| n b b' Hb| n] [=]; subst; eauto).
Time by_cases.
Time +
Time (destruct (pcore a) as [ca| ] eqn:?; simplify_option_eq).
Time -
Time (intros m i).
Time by rewrite lookup_op lookup_core cmra_core_l.
Time f_equal.
Time -
Time (intros m i).
Time by rewrite !lookup_core cmra_core_idemp.
Time lia.
Time Qed.
Time #[global]Instance counting_id_free  (z : counting): (IdFree z).
Time Proof.
Time (intros y).
Time rewrite counting_op' counting_validN'.
Time -
Time by_cases.
Time
(intros m1 m2; <ssreflect_plugin::ssrtclintros@0> rewrite !lookup_included
  =>Hm i).
Time (destruct y; by_cases; intros _; inversion 1).
Time rewrite !lookup_core.
Time by apply cmra_core_mono.
Time lia.
Time Qed.
Time (destruct (cmra_pcore_ne n a a' ca) as (ca', (->, ?)); auto).
Time -
Time (intros n m1 m2 Hm i; apply cmra_validN_op_l with (m2 !! i)).
Time (exists (Cinl ca'); by repeat constructor).
Time +
Time (destruct (pcore b) as [cb| ] eqn:?; simplify_option_eq).
Time by rewrite -lookup_op.
Time -
Time (intros n m y1 y2 Hm Heq).
Time
(<ssreflect_plugin::ssrtclseq@0> refine
 ((\206\187 FUN, _) (\206\187 i, cmra_extend n (m !! i) (y1 !! i) (y2 !! i) (Hm i) _)) ;
 last  by rewrite -lookup_op).
Time #[global]Instance counting_full_exclusive : (Exclusive (Count 0)).
Time Proof.
Time (intros y).
Time rewrite counting_validN' counting_op'.
Time exists (map_imap (\206\187 i _, projT1 (FUN i)) y1).
Time (<ssreflect_plugin::ssrtclintros@0> destruct y =>//=; by_cases).
Time exists (map_imap (\206\187 i _, proj1_sig (projT2 (FUN i))) y2).
Time
(<ssreflect_plugin::ssrtclintros@0> split; [  | split ] =>i; rewrite
  ?lookup_op !lookup_imap; <ssreflect_plugin::ssrtclintros@0>
  destruct (FUN i) as (z1i, (z2i, (Hmi, (Hz1i, Hz2i)))) =>/=).
Time Qed.
Time Qed.
Time Lemma list_lookup_core l i : core l !! i = core (l !! i).
Time Proof.
Time rewrite /core /= list_lookup_fmap.
Time (destruct (l !! i); by rewrite /= ?Some_core).
Time Qed.
Time Lemma list_lookup_included l1 l2 : l1 \226\137\188 l2 \226\134\148 (\226\136\128 i, l1 !! i \226\137\188 l2 !! i).
Time Proof.
Time split.
Time {
Time (intros [l Hl] i).
Time exists (l !! i).
Time by rewrite Hl list_lookup_op.
Time (destruct (cmra_pcore_ne n b b' cb) as (cb', (->, ?)); auto).
Time (exists (Cinr cb'); by repeat constructor).
Time -
Time (intros ? [a| b| ] [a'| b'| ] H; inversion_clear H; ofe_subst; done).
Time }
Time revert l1.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l2 as [| y l2 IH] =>- 
 [|x l1] Hl).
Time -
Time by exists [].
Time -
Time (destruct (Hl 0) as [[z| ] Hz]; inversion Hz).
Time -
Time by exists (y :: l2).
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (IH l1) as [l3 ?] ; first 
 intros i; apply (Hl (S i))).
Time (destruct (Hl 0) as [[z| ] Hz]; inversion_clear Hz; simplify_eq /=).
Time +
Time (exists (z :: l3); by constructor).
Time +
Time (exists (core x :: l3); constructor; by rewrite ?cmra_core_r).
Time Qed.
Time +
Time -
Time
(intros [a| b| ]; rewrite /= ?cmra_valid_validN; naive_solver eauto using O).
Time
(destruct (y1 !! i), (y2 !! i); inversion Hz1i; inversion Hz2i;
  <ssreflect_plugin::ssrtclintros@0> subst =>//).
Time Definition list_cmra_mixin : CmraMixin (list A).
Time Proof.
Time (apply cmra_total_mixin).
Time -
Time eauto.
Time -
Time
(intros n l l1 l2; <ssreflect_plugin::ssrtclintros@0> rewrite
  !list_dist_lookup =>Hl i).
Time -
Time (intros n [a| b| ]; simpl; auto using cmra_validN_S).
Time -
Time
(intros [a1| b1| ] [a2| b2| ] [a3| b3| ]; constructor; by rewrite ?assoc).
Time by rewrite !list_lookup_op Hl.
Time -
Time (intros n l1 l2 Hl; by rewrite /core /= Hl).
Time +
Time revert Hz1i.
Time case : {}(y1 !! i) {} =>[?|] //.
Time +
Time revert Hz2i.
Time case : {}(y2 !! i) {} =>[?|] //.
Time Qed.
Time -
Time (intros [a1| b1| ] [a2| b2| ]; constructor; by rewrite 1?comm).
Time -
Time
(intros n l1 l2; <ssreflect_plugin::ssrtclintros@0> rewrite !list_dist_lookup
  !list_lookup_validN =>Hl ? i).
Time -
Time (intros [a| b| ] ? [=]; subst; auto).
Time +
Time (destruct (pcore a) as [ca| ] eqn:?; simplify_option_eq).
Time by rewrite -Hl.
Time (constructor; eauto using cmra_pcore_l).
Time +
Time (destruct (pcore b) as [cb| ] eqn:?; simplify_option_eq).
Time Canonical Structure gmapR := CmraT (gmap K A) gmap_cmra_mixin.
Time #[global]
Instance gmap_cmra_discrete : (CmraDiscrete A \226\134\146 CmraDiscrete gmapR).
Time Proof.
Time (split; [ apply _ |  ]).
Time (intros m ? i).
Time (constructor; eauto using cmra_pcore_l).
Time -
Time (intros l).
Time rewrite list_lookup_valid.
Time by apply : {}cmra_discrete_valid {}.
Time Qed.
Time Lemma gmap_ucmra_mixin : UcmraMixin (gmap K A).
Time Proof.
Time split.
Time -
Time by intros i; rewrite lookup_empty.
Time -
Time by intros m i; rewrite /= lookup_op lookup_empty (left_id_L None _).
Time -
Time (intros [a| b| ] ? [=]; subst; auto).
Time setoid_rewrite list_lookup_validN.
Time setoid_rewrite cmra_valid_validN.
Time -
Time (<ssreflect_plugin::ssrtclintros@0> constructor =>i).
Time by rewrite lookup_omap lookup_empty.
Time +
Time (destruct (pcore a) as [ca| ] eqn:?; simplify_option_eq).
Time Qed.
Time naive_solver.
Time Canonical Structure gmapUR := UcmraT (gmap K A) gmap_ucmra_mixin.
Time
Lemma gmap_equivI {M} m1 m2 : m1 \226\137\161 m2 \226\138\163\226\138\162@{ uPredI M} (\226\136\128 i, m1 !! i \226\137\161 m2 !! i).
Time Proof.
Time by uPred.unseal.
Time -
Time (intros n x).
Time rewrite !list_lookup_validN.
Time (feed inversion cmra_pcore_idemp a ca; repeat constructor; auto).
Time +
Time (destruct (pcore b) as [cb| ] eqn:?; simplify_option_eq).
Time Qed.
Time Lemma gmap_validI {M} m : \226\156\147 m \226\138\163\226\138\162@{ uPredI M} (\226\136\128 i, \226\156\147 (m !! i)).
Time Proof.
Time by uPred.unseal.
Time auto using cmra_validN_S.
Time -
Time
(intros l1 l2 l3; <ssreflect_plugin::ssrtclintros@0> rewrite
  list_equiv_lookup =>i).
Time by rewrite !list_lookup_op assoc.
Time Qed.
Time End cmra.
Time (feed inversion cmra_pcore_idemp b cb; repeat constructor; auto).
Time -
Time
(intros x y ?
  [->| [(a, (a', (->, (->, ?))))| (b, (b', (->, (->, ?))))]]%csum_included
  [=]).
Time -
Time
(intros l1 l2; <ssreflect_plugin::ssrtclintros@0> rewrite list_equiv_lookup
  =>i).
Time by rewrite !list_lookup_op comm.
Time +
Time exists CsumBot.
Time (rewrite csum_included; eauto).
Time +
Time (destruct (pcore a) as [ca| ] eqn:?; simplify_option_eq).
Time -
Time
(intros l; <ssreflect_plugin::ssrtclintros@0> rewrite list_equiv_lookup =>i).
Time Arguments gmapR _ {_} {_} _.
Time Arguments gmapUR _ {_} {_} _.
Time Section properties.
Time Context `{Countable K} {A : cmraT}.
Time Implicit Type m : gmap K A.
Time Implicit Type i : K.
Time Implicit Types x y : A.
Time by rewrite list_lookup_op list_lookup_core cmra_core_l.
Time #[global]
Instance lookup_op_homomorphism :
 (MonoidHomomorphism op op (\226\137\161) (lookup i : gmap K A \226\134\146 option A)).
Time Proof.
Time (split; [ split |  ]; try apply _).
Time -
Time
(intros l; <ssreflect_plugin::ssrtclintros@0> rewrite list_equiv_lookup =>i).
Time by rewrite !list_lookup_core cmra_core_idemp.
Time (intros m1 m2; by rewrite lookup_op).
Time (destruct (cmra_pcore_mono a a' ca) as (ca', (->, ?)); auto).
Time exists (Cinl ca').
Time (rewrite csum_included; eauto  10).
Time done.
Time Qed.
Time Lemma lookup_opM m1 mm2 i : (m1 \226\139\133? mm2) !! i = m1 !! i \226\139\133 (mm2 \226\137\171= (!!i)).
Time Proof.
Time (destruct mm2; by rewrite /= ?lookup_op ?right_id_L).
Time -
Time
(intros l1 l2; <ssreflect_plugin::ssrtclintros@0> rewrite
  !list_lookup_included =>Hl i).
Time +
Time (destruct (pcore b) as [cb| ] eqn:?; simplify_option_eq).
Time rewrite !list_lookup_core.
Time by apply cmra_core_mono.
Time -
Time (intros n l1 l2).
Time rewrite !list_lookup_validN.
Time (destruct (cmra_pcore_mono b b' cb) as (cb', (->, ?)); auto).
Time exists (Cinr cb').
Time (rewrite csum_included; eauto  10).
Time Qed.
Time
Lemma lookup_validN_Some n m i x : \226\156\147{n} m \226\134\146 m !! i \226\137\161{n}\226\137\161 Some x \226\134\146 \226\156\147{n} x.
Time Proof.
Time by move  {}=>/(_ i) Hm Hi; move : {}Hm {}; rewrite Hi.
Time setoid_rewrite list_lookup_op.
Time Qed.
Time Lemma lookup_valid_Some m i x : \226\156\147 m \226\134\146 m !! i \226\137\161 Some x \226\134\146 \226\156\147 x.
Time Proof.
Time move  {}=>Hm Hi.
Time move : {}(Hm i) {}.
Time by rewrite Hi.
Time Qed.
Time Lemma insert_validN n m i x : \226\156\147{n} x \226\134\146 \226\156\147{n} m \226\134\146 \226\156\147{n} <[i:=x]> m.
Time Proof.
Time by intros ? ? j; destruct (decide (i = j)); simplify_map_eq.
Time -
Time
(intros n [a1| b1| ] [a2| b2| ]; simpl; eauto using cmra_validN_op_l; done).
Time -
Time (intros n [a| b| ] y1 y2 Hx Hx').
Time +
Time
(destruct y1 as [a1| b1| ], y2 as [a2| b2| ]; try by exfalso; inversion Hx').
Time Qed.
Time Lemma insert_valid m i x : \226\156\147 x \226\134\146 \226\156\147 m \226\134\146 \226\156\147 <[i:=x]> m.
Time Proof.
Time by intros ? ? j; destruct (decide (i = j)); simplify_map_eq.
Time eauto using cmra_validN_op_l.
Time -
Time (intros n l).
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>- 
  [|y1 l1] [|y2 l2] Hl Heq; try by exfalso; inversion Heq).
Time
(destruct (cmra_extend n a a1 a2) as (z1, (z2, (?, (?, ?))));
  [ done | apply (inj Cinl), Hx' |  ]).
Time Qed.
Time exists (Cinl z1),(Cinl z2).
Time by repeat constructor.
Time +
Time
(destruct y1 as [a1| b1| ], y2 as [a2| b2| ]; try by exfalso; inversion Hx').
Time Lemma singleton_validN n i x : \226\156\147{n} ({[i := x]} : gmap K A) \226\134\148 \226\156\147{n} x.
Time Proof.
Time split.
Time -
Time (move  {}=>/(_ i); by simplify_map_eq).
Time -
Time (intros).
Time (apply insert_validN).
Time done.
Time apply : {}ucmra_unit_validN {}.
Time Qed.
Time Lemma singleton_valid i x : \226\156\147 ({[i := x]} : gmap K A) \226\134\148 \226\156\147 x.
Time +
Time by exists [],[].
Time Proof.
Time rewrite !cmra_valid_validN.
Time +
Time (exists [],(x :: l); inversion Heq; by repeat constructor).
Time by setoid_rewrite singleton_validN.
Time Qed.
Time Lemma delete_validN n m i : \226\156\147{n} m \226\134\146 \226\156\147{n} delete i m.
Time Proof.
Time (intros Hm j; destruct (decide (i = j)); by simplify_map_eq).
Time +
Time (exists (x :: l),[]; inversion Heq; by repeat constructor).
Time
(destruct (cmra_extend n b b1 b2) as (z1, (z2, (?, (?, ?))));
  [ done | apply (inj Cinr), Hx' |  ]).
Time exists (Cinr z1),(Cinr z2).
Time by repeat constructor.
Time +
Time by exists CsumBot,CsumBot; destruct y1, y2; inversion_clear Hx'.
Time +
Time
(destruct (IH l1 l2) as (l1', (l2', (?, (?, ?)))), 
  (cmra_extend n x y1 y2) as (y1', (y2', (?, (?, ?))));
  [ by inversion_clear Heq; inversion_clear Hl.. | idtac ]).
Time Qed.
Time Lemma delete_valid m i : \226\156\147 m \226\134\146 \226\156\147 delete i m.
Time Proof.
Time (intros Hm j; destruct (decide (i = j)); by simplify_map_eq).
Time Qed.
Time
Lemma insert_singleton_op m i x : m !! i = None \226\134\146 <[i:=x]> m = {[i := x]} \226\139\133 m.
Time Proof.
Time
(intros Hi; <ssreflect_plugin::ssrtclintros@0> apply map_eq =>j;
  destruct (decide (i = j)) as [->| ]).
Time -
Time by rewrite lookup_op lookup_insert lookup_singleton Hi right_id_L.
Time -
Time
by rewrite lookup_op lookup_insert_ne // lookup_singleton_ne // left_id_L.
Time (exists (y1' :: l1'),(y2' :: l2'); repeat constructor; auto).
Time Qed.
Time Qed.
Time Qed.
Time
Lemma core_singleton (i : K) (x : A) cx :
  pcore x = Some cx \226\134\146 core ({[i := x]} : gmap K A) = {[i := cx]}.
Time Proof.
Time (apply omap_singleton).
Time Qed.
Time
Lemma core_singleton' (i : K) (x : A) cx :
  pcore x \226\137\161 Some cx \226\134\146 core ({[i := x]} : gmap K A) \226\137\161 {[i := cx]}.
Time Proof.
Time (intros (cx', (?, ->))%equiv_Some_inv_r').
Time Canonical Structure listR := CmraT (list A) list_cmra_mixin.
Time #[global]Instance list_unit : (Unit (list A)) := [].
Time Definition list_ucmra_mixin : UcmraMixin (list A).
Time Proof.
Time split.
Time -
Time constructor.
Time -
Time by intros l.
Time -
Time by constructor.
Time Qed.
Time Canonical Structure listUR := UcmraT (list A) list_ucmra_mixin.
Time #[global]
Instance list_cmra_discrete : (CmraDiscrete A \226\134\146 CmraDiscrete listR).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> split; [ apply _ |  ] =>l;
  <ssreflect_plugin::ssrtclintros@0> rewrite list_lookup_valid
  list_lookup_validN =>Hl i).
Time Canonical Structure csumR := CmraT (csum A B) csum_cmra_mixin.
Time #[global]
Instance csum_cmra_discrete :
 (CmraDiscrete A \226\134\146 CmraDiscrete B \226\134\146 CmraDiscrete csumR).
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  apply _).
Time by move  {}=>[a|b|] HH /=; try apply cmra_discrete_valid.
Time by apply cmra_discrete_valid.
Time Qed.
Time #[global]Instance Cinl_core_id  a: (CoreId a \226\134\146 CoreId (Cinl a)).
Time Proof.
Time rewrite /CoreId /=.
Time (inversion_clear 1; by repeat constructor).
Time Qed.
Time #[global]Instance list_core_id  l: ((\226\136\128 x : A, CoreId x) \226\134\146 CoreId l).
Time Proof.
Time
(intros ?; constructor; <ssreflect_plugin::ssrtclintros@0>
  apply list_equiv_lookup =>i).
Time by rewrite list_lookup_core (core_id_core (l !! i)).
Time by rewrite (core_singleton _ _ cx').
Time Qed.
Time #[global]Instance Cinr_core_id  b: (CoreId b \226\134\146 CoreId (Cinr b)).
Time Proof.
Time rewrite /CoreId /=.
Time (inversion_clear 1; by repeat constructor).
Time Qed.
Time
Lemma op_singleton (i : K) (x y : A) :
  {[i := x]} \226\139\133 {[i := y]} = ({[i := x \226\139\133 y]} : gmap K A).
Time Qed.
Time #[global]Instance Cinl_exclusive  a: (Exclusive a \226\134\146 Exclusive (Cinl a)).
Time Proof.
Time by <ssreflect_plugin::ssrtclintros@0> move  {}=>H [] ? =>[/H||].
Time Qed.
Time Proof.
Time by apply (merge_singleton _ _ _ x y).
Time Qed.
Time #[global]
Instance is_op_singleton  i a a1 a2:
 (IsOp a a1 a2 \226\134\146 IsOp' ({[i := a]} : gmap K A) {[i := a1]} {[i := a2]}).
Time #[global]Instance Cinr_exclusive  b: (Exclusive b \226\134\146 Exclusive (Cinr b)).
Time Proof.
Time by <ssreflect_plugin::ssrtclintros@0> move  {}=>H [] ? =>[|/H|].
Time Qed.
Time #[global]
Instance Cinl_cancelable  a: (Cancelable a \226\134\146 Cancelable (Cinl a)).
Time Proof.
Time (move  {}=>? ? [y|y|] [z|z|] ? EQ //; inversion_clear EQ).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsOp' /IsOp =>{+}->).
Time Qed.
Time
Lemma list_equivI {M} l1 l2 : l1 \226\137\161 l2 \226\138\163\226\138\162@{ uPredI M} (\226\136\128 i, l1 !! i \226\137\161 l2 !! i).
Time Proof.
Time (uPred.unseal; <ssreflect_plugin::ssrtclintros@0> constructor =>n x ?).
Time (apply list_dist_lookup).
Time Qed.
Time Lemma list_validI {M} l : \226\156\147 l \226\138\163\226\138\162@{ uPredI M} (\226\136\128 i, \226\156\147 (l !! i)).
Time Proof.
Time (uPred.unseal; <ssreflect_plugin::ssrtclintros@0> constructor =>n x ?).
Time (apply list_lookup_validN).
Time Qed.
Time End cmra.
Time Arguments listR : clear implicits.
Time Arguments listUR : clear implicits.
Time
Instance list_singletonM  {A : ucmraT}: (SingletonM nat A (list A)) :=
 (\206\187 n x, replicate n \206\181 ++ [x]).
Time Section properties.
Time Context {A : ucmraT}.
Time Implicit Type l : list A.
Time Implicit Types x y z : A.
Time #[local]Arguments op _ _ !_ !_ / : simpl nomatch.
Time #[local]Arguments cmra_op _ !_ !_ / : simpl nomatch.
Time #[local]Arguments ucmra_op _ !_ !_ / : simpl nomatch.
Time Lemma list_lookup_opM l mk i : (l \226\139\133? mk) !! i = l !! i \226\139\133 (mk \226\137\171= (!!i)).
Time Proof.
Time (destruct mk; by rewrite /= ?list_lookup_op ?right_id_L).
Time by rewrite -op_singleton.
Time constructor.
Time by eapply (cancelableN a).
Time Qed.
Time Qed.
Time #[global]Instance gmap_core_id  m: ((\226\136\128 x : A, CoreId x) \226\134\146 CoreId m).
Time Proof.
Time (intros; <ssreflect_plugin::ssrtclintros@0> apply core_id_total =>i).
Time rewrite lookup_core.
Time Qed.
Time #[global]Instance list_op_nil_l : (LeftId (=) (@nil A) op).
Time Proof.
Time done.
Time Qed.
Time #[global]Instance list_op_nil_r : (RightId (=) (@nil A) op).
Time Proof.
Time by intros [].
Time (apply (core_id_core _)).
Time Qed.
Time #[global]
Instance gmap_singleton_core_id  i (x : A): (CoreId x \226\134\146 CoreId {[i := x]}).
Time Proof.
Time (intros).
Time #[global]
Instance Cinr_cancelable  b: (Cancelable b \226\134\146 Cancelable (Cinr b)).
Time Proof.
Time (move  {}=>? ? [y|y|] [z|z|] ? EQ //; inversion_clear EQ).
Time Qed.
Time
Lemma list_op_app l1 l2 l3 :
  (l1 ++ l3) \226\139\133 l2 = l1 \226\139\133 take (length l1) l2 ++ l3 \226\139\133 drop (length l1) l2.
Time Proof.
Time revert l2 l3.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l1 as [| x1 l1] =>- 
  [|x2 l2] [|x3 l3]; f_equal /=; auto).
Time by apply core_id_total, core_singleton'.
Time Qed.
Time
Lemma singleton_includedN n m i x :
  {[i := x]} \226\137\188{n} m \226\134\148 (\226\136\131 y, m !! i \226\137\161{n}\226\137\161 Some y \226\136\167 Some x \226\137\188{n} Some y).
Time Proof.
Time split.
Time -
Time
(move  {}=>[m' /(_ i)]; <ssreflect_plugin::ssrtclintros@0> rewrite lookup_op
  lookup_singleton =>Hi).
Time exists (x \226\139\133? m' !! i).
Time rewrite -Some_op_opM.
Time split.
Time done.
Time (apply cmra_includedN_l).
Time -
Time (intros (y, (Hi, [mz Hy]))).
Time exists (partial_alter (\206\187 _, mz) i m).
Time (intros j; destruct (decide (i = j)) as [->| ]).
Time +
Time by rewrite lookup_op lookup_singleton lookup_partial_alter Hi.
Time Qed.
Time
Lemma list_op_app_le l1 l2 l3 :
  length l2 \226\137\164 length l1 \226\134\146 (l1 ++ l3) \226\139\133 l2 = l1 \226\139\133 l2 ++ l3.
Time Proof.
Time (intros ?).
Time by rewrite list_op_app take_ge // drop_ge // right_id_L.
Time Qed.
Time +
Time
by rewrite lookup_op lookup_singleton_ne // lookup_partial_alter_ne //
 left_id.
Time
Lemma list_lookup_validN_Some n l i x : \226\156\147{n} l \226\134\146 l !! i \226\137\161{n}\226\137\161 Some x \226\134\146 \226\156\147{n} x.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> move  {}=>/list_lookup_validN/
  (_ i) =>Hl Hi; move : {}Hl {}).
Time by rewrite Hi.
Time Qed.
Time Lemma list_lookup_valid_Some l i x : \226\156\147 l \226\134\146 l !! i \226\137\161 Some x \226\134\146 \226\156\147 x.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> move  {}=>/list_lookup_valid/
  (_ i) =>Hl Hi; move : {}Hl {}).
Time by rewrite Hi.
Time Qed.
Time
Lemma list_op_length l1 l2 : length (l1 \226\139\133 l2) = max (length l1) (length l2).
Time Proof.
Time revert l2.
Time (induction l1; intros [| ? ?]; f_equal /=; auto).
Time Qed.
Time Lemma replicate_valid n (x : A) : \226\156\147 x \226\134\146 \226\156\147 replicate n x.
Time Proof.
Time (apply Forall_replicate).
Time Qed.
Time #[global]
Instance list_singletonM_ne  i: (NonExpansive (@list_singletonM A i)).
Time Proof.
Time (intros n l1 l2 ?).
Time (apply Forall2_app; by repeat constructor).
Time Qed.
Time #[global]
Instance list_singletonM_proper  i:
 (Proper ((\226\137\161) ==> (\226\137\161)) (list_singletonM i)) := (ne_proper _).
Time
Lemma elem_of_list_singletonM i z x :
  z \226\136\136 ({[i := x]} : list A) \226\134\146 z = \206\181 \226\136\168 z = x.
Time Proof.
Time rewrite elem_of_app elem_of_list_singleton elem_of_replicate.
Time constructor.
Time Qed.
Time by eapply (cancelableN b).
Time Qed.
Time
Lemma singleton_included m i x :
  {[i := x]} \226\137\188 m \226\134\148 (\226\136\131 y, m !! i \226\137\161 Some y \226\136\167 Some x \226\137\188 Some y).
Time #[global]Instance Cinl_id_free  a: (IdFree a \226\134\146 IdFree (Cinl a)).
Time Proof.
Time (intros ? [] ? EQ; inversion_clear EQ).
Time naive_solver.
Time Proof.
Time split.
Time -
Time (move  {}=>[m' /(_ i)]; rewrite lookup_op lookup_singleton).
Time exists (x \226\139\133? m' !! i).
Time rewrite -Some_op_opM.
Time split.
Time done.
Time (apply cmra_included_l).
Time -
Time (intros (y, (Hi, [mz Hy]))).
Time Qed.
Time Lemma list_lookup_singletonM i x : ({[i := x]} : list A) !! i = Some x.
Time Proof.
Time (induction i; by f_equal /=).
Time exists (partial_alter (\206\187 _, mz) i m).
Time (intros j; destruct (decide (i = j)) as [->| ]).
Time by eapply id_free0_r.
Time Qed.
Time #[global]Instance Cinr_id_free  b: (IdFree b \226\134\146 IdFree (Cinr b)).
Time Proof.
Time (intros ? [] ? EQ; inversion_clear EQ).
Time Qed.
Time
Lemma list_lookup_singletonM_ne i j x :
  i \226\137\160 j
  \226\134\146 ({[i := x]} : list A) !! j = None \226\136\168 ({[i := x]} : list A) !! j = Some \206\181.
Time +
Time by rewrite lookup_op lookup_singleton lookup_partial_alter Hi.
Time Proof.
Time (revert j; induction i; intros [| j]; naive_solver auto with lia).
Time +
Time
by rewrite lookup_op lookup_singleton_ne // lookup_partial_alter_ne //
 left_id.
Time by eapply id_free0_r.
Time Qed.
Time
Lemma csum_equivI {M} (x y : csum A B) :
  x \226\137\161 y
  \226\138\163\226\138\162@{ uPredI M} match x, y with
                 | Cinl a, Cinl a' => a \226\137\161 a'
                 | Cinr b, Cinr b' => b \226\137\161 b'
                 | CsumBot, CsumBot => True
                 | _, _ => False
                 end.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> uPred.unseal; do 2 split ; first  by
 destruct 1).
Time by destruct x, y; try destruct 1; try constructor.
Time Qed.
Time
Lemma csum_validI {M} (x : csum A B) :
  \226\156\147 x
  \226\138\163\226\138\162@{ uPredI M} match x with
                 | Cinl a => \226\156\147 a
                 | Cinr b => \226\156\147 b
                 | CsumBot => False
                 end.
Time Proof.
Time uPred.unseal.
Time by destruct x.
Time Qed.
Time Qed.
Time Lemma csum_update_l (a1 a2 : A) : a1 ~~> a2 \226\134\146 Cinl a1 ~~> Cinl a2.
Time Proof.
Time Qed.
Time
Lemma list_singletonM_validN n i x : \226\156\147{n} ({[i := x]} : list A) \226\134\148 \226\156\147{n} x.
Time (intros Ha n [[a| b| ]| ] ?; simpl in *; auto).
Time -
Time by apply (Ha n (Some a)).
Time -
Time by apply (Ha n None).
Time Qed.
Time Lemma csum_update_r (b1 b2 : B) : b1 ~~> b2 \226\134\146 Cinr b1 ~~> Cinr b2.
Time Proof.
Time (intros Hb n [[a| b| ]| ] ?; simpl in *; auto).
Time -
Time by apply (Hb n (Some b)).
Time -
Time by apply (Hb n None).
Time Proof.
Time rewrite list_lookup_validN.
Time split.
Time
Lemma singleton_included_exclusive m i x :
  Exclusive x \226\134\146 \226\156\147 m \226\134\146 {[i := x]} \226\137\188 m \226\134\148 m !! i \226\137\161 Some x.
Time Proof.
Time (intros ? Hm).
Time rewrite singleton_included.
Time Qed.
Time
Lemma csum_updateP_l (P : A \226\134\146 Prop) (Q : csum A B \226\134\146 Prop) 
  a : a ~~>: P \226\134\146 (\226\136\128 a', P a' \226\134\146 Q (Cinl a')) \226\134\146 Cinl a ~~>: Q.
Time Proof.
Time (intros Hx HP n mf Hm).
Time (destruct mf as [[a'| b'| ]| ]; try by destruct Hm).
Time -
Time (destruct (Hx n (Some a')) as (c, (?, ?)); naive_solver).
Time {
Time move  {}=>/(_ i).
Time by rewrite list_lookup_singletonM.
Time }
Time (intros Hx j; destruct (decide (i = j)); subst).
Time -
Time by rewrite list_lookup_singletonM.
Time -
Time
(<ssreflect_plugin::ssrtclseq@0>
  destruct (list_lookup_singletonM_ne i j x) as [Hi| Hi] ; first  done;
  rewrite Hi; by try apply (ucmra_unit_validN (A:=A))).
Time (<ssreflect_plugin::ssrtclseq@0> split ; last  by eauto).
Time Qed.
Time Lemma list_singleton_valid i x : \226\156\147 ({[i := x]} : list A) \226\134\148 \226\156\147 x.
Time Proof.
Time rewrite !cmra_valid_validN.
Time
(intros (y, (?, ->%(Some_included_exclusive _))); eauto
  using lookup_valid_Some).
Time by setoid_rewrite list_singletonM_validN.
Time -
Time
(destruct (Hx n None) as (c, (?, ?)); naive_solver eauto
  using cmra_validN_op_l).
Time Qed.
Time Lemma list_singletonM_length i x : length {[i := x]} = S i.
Time Proof.
Time
(rewrite /singletonM /list_singletonM app_length replicate_length /=; lia).
Time Qed.
Time #[global]
Instance singleton_cancelable  i x:
 (Cancelable (Some x) \226\134\146 Cancelable {[i := x]}).
Time Proof.
Time Qed.
Time
Lemma list_core_singletonM i (x : A) : core {[i := x]} \226\137\161 {[i := core x]}.
Time Proof.
Time (intros ? n m1 m2 Hv EQ j).
Time move : {}(Hv j) {}(EQ j) {}.
Time rewrite !lookup_op.
Time Qed.
Time
Lemma csum_updateP_r (P : B \226\134\146 Prop) (Q : csum A B \226\134\146 Prop) 
  b : b ~~>: P \226\134\146 (\226\136\128 b', P b' \226\134\146 Q (Cinr b')) \226\134\146 Cinr b ~~>: Q.
Time Proof.
Time (intros Hx HP n mf Hm).
Time (destruct mf as [[a'| b'| ]| ]; try by destruct Hm).
Time rewrite /singletonM /list_singletonM.
Time by rewrite {+1}/core /= fmap_app fmap_replicate (core_id_core \226\136\133).
Time (destruct (decide (i = j)) as [->| ]).
Time -
Time (destruct (Hx n (Some b')) as (c, (?, ?)); naive_solver).
Time -
Time rewrite lookup_singleton.
Time by apply cancelableN.
Time -
Time by rewrite lookup_singleton_ne // !(left_id None _).
Time -
Time
(destruct (Hx n None) as (c, (?, ?)); naive_solver eauto
  using cmra_validN_op_l).
Time Qed.
Time
Lemma list_op_singletonM i (x y : A) :
  {[i := x]} \226\139\133 {[i := y]} \226\137\161 {[i := x \226\139\133 y]}.
Time Proof.
Time rewrite /singletonM /list_singletonM /=.
Time (induction i; constructor; rewrite ?left_id; auto).
Time Qed.
Time
Lemma csum_updateP'_l (P : A \226\134\146 Prop) a :
  a ~~>: P \226\134\146 Cinl a ~~>: (\206\187 m', \226\136\131 a', m' = Cinl a' \226\136\167 P a').
Time Proof.
Time eauto using csum_updateP_l.
Time Qed.
Time
Lemma csum_updateP'_r (P : B \226\134\146 Prop) b :
  b ~~>: P \226\134\146 Cinr b ~~>: (\206\187 m', \226\136\131 b', m' = Cinr b' \226\136\167 P b').
Time Proof.
Time eauto using csum_updateP_r.
Time Qed.
Time
Lemma csum_local_update_l (a1 a2 a1' a2' : A) :
  (a1, a2) ~l~> (a1', a2') \226\134\146 (Cinl a1, Cinl a2) ~l~> (Cinl a1', Cinl a2').
Time Proof.
Time (intros Hup n mf ? Ha1; simpl in *).
Time (destruct (Hup n (mf \226\137\171= maybe Cinl)); auto).
Time {
Time by destruct mf as [[]| ]; inversion_clear Ha1.
Time Qed.
Time
Lemma list_alter_singletonM f i x :
  alter f i ({[i := x]} : list A) = {[i := f x]}.
Time Proof.
Time rewrite /singletonM /list_singletonM /=.
Time (induction i; f_equal /=; auto).
Time Qed.
Time Qed.
Time #[global]
Instance list_singleton_core_id  i (x : A): (CoreId x \226\134\146 CoreId {[i := x]}).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite !core_id_total
 list_core_singletonM =>{+}->.
Time }
Time split.
Time done.
Time by destruct mf as [[]| ]; inversion_clear Ha1; constructor.
Time #[global]
Instance gmap_cancelable  (m : gmap K A):
 ((\226\136\128 x : A, IdFree x) \226\134\146 (\226\136\128 x : A, Cancelable x) \226\134\146 Cancelable m).
Time Proof.
Time (intros ? ? n m1 m2 ? ? i).
Time (apply (cancelableN (m !! i)); by rewrite -!lookup_op).
Time Qed.
Time
Lemma insert_op m1 m2 i x y :
  <[i:=x \226\139\133 y]> (m1 \226\139\133 m2) = <[i:=x]> m1 \226\139\133 <[i:=y]> m2.
Time Proof.
Time by rewrite (insert_merge (\226\139\133) m1 m2 i (x \226\139\133 y) x y).
Time Qed.
Time Qed.
Time
Lemma insert_updateP (P : A \226\134\146 Prop) (Q : gmap K A \226\134\146 Prop) 
  m i x : x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q (<[i:=y]> m)) \226\134\146 <[i:=x]> m ~~>: Q.
Time Proof.
Time
(intros Hx%option_updateP' HP; <ssreflect_plugin::ssrtclintros@0>
  apply cmra_total_updateP =>n mf Hm).
Time (destruct (Hx n (Some (mf !! i))) as ([y| ], (?, ?)); try done).
Time {
Time by generalize (Hm i); rewrite lookup_op; simplify_map_eq.
Time
Lemma csum_local_update_r (b1 b2 b1' b2' : B) :
  (b1, b2) ~l~> (b1', b2') \226\134\146 (Cinr b1, Cinr b2) ~l~> (Cinr b1', Cinr b2').
Time Proof.
Time (intros Hup n mf ? Ha1; simpl in *).
Time (destruct (Hup n (mf \226\137\171= maybe Cinr)); auto).
Time Qed.
Time
Lemma list_singleton_updateP (P : A \226\134\146 Prop) (Q : list A \226\134\146 Prop) 
  x : x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q [y]) \226\134\146 [x] ~~>: Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite !cmra_total_updateP =>Hup HQ n lf
 /list_lookup_validN Hv).
Time {
Time by destruct mf as [[]| ]; inversion_clear Ha1.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> exists (<[i:=y]> m); split ; first  by auto).
Time
(intros j; move : {}(Hm j) {} =>{Hm}; <ssreflect_plugin::ssrtclintros@0>
  rewrite !lookup_op =>Hm).
Time (destruct (Hup n (default \206\181 (lf !! 0))) as (y, (?, Hv'))).
Time {
Time move : {}(Hv 0) {}.
Time by destruct lf; rewrite /= ?right_id.
Time (destruct (decide (i = j)); simplify_map_eq /=; auto).
Time }
Time split.
Time done.
Time by destruct mf as [[]| ]; inversion_clear Ha1; constructor.
Time }
Time (<ssreflect_plugin::ssrtclseq@0> exists [y]; split ; first  by auto).
Time (<ssreflect_plugin::ssrtclintros@0> apply list_lookup_validN =>i).
Time move : {}(Hv i) {}Hv' {}.
Time by destruct i, lf; rewrite /= ?right_id.
Time Qed.
Time End cmra.
Time Qed.
Time Qed.
Time
Lemma insert_updateP' (P : A \226\134\146 Prop) m i x :
  x ~~>: P \226\134\146 <[i:=x]> m ~~>: (\206\187 m', \226\136\131 y, m' = <[i:=y]> m \226\136\167 P y).
Time Proof.
Time eauto using insert_updateP.
Time Qed.
Time Lemma insert_update m i x y : x ~~> y \226\134\146 <[i:=x]> m ~~> <[i:=y]> m.
Time Proof.
Time (rewrite !cmra_update_updateP; eauto using insert_updateP with subst).
Time
Lemma list_singleton_updateP' (P : A \226\134\146 Prop) x :
  x ~~>: P \226\134\146 [x] ~~>: (\206\187 k, \226\136\131 y, k = [y] \226\136\167 P y).
Time Proof.
Time eauto using list_singleton_updateP.
Time Qed.
Time Lemma list_singleton_update x y : x ~~> y \226\134\146 [x] ~~> [y].
Time Proof.
Time
(rewrite !cmra_update_updateP; eauto using list_singleton_updateP with subst).
Time Qed.
Time
Lemma app_updateP (P1 P2 Q : list A \226\134\146 Prop) l1 l2 :
  l1 ~~>: P1
  \226\134\146 l2 ~~>: P2
    \226\134\146 (\226\136\128 k1 k2, P1 k1 \226\134\146 P2 k2 \226\134\146 length l1 = length k1 \226\136\167 Q (k1 ++ k2))
      \226\134\146 l1 ++ l2 ~~>: Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite !cmra_total_updateP =>Hup1 Hup2
 HQ n lf).
Time Qed.
Time
Lemma singleton_updateP (P : A \226\134\146 Prop) (Q : gmap K A \226\134\146 Prop) 
  i x : x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q {[i := y]}) \226\134\146 {[i := x]} ~~>: Q.
Time Proof.
Time (apply insert_updateP).
Time Qed.
Time
Lemma singleton_updateP' (P : A \226\134\146 Prop) i x :
  x ~~>: P \226\134\146 {[i := x]} ~~>: (\206\187 m, \226\136\131 y, m = {[i := y]} \226\136\167 P y).
Time Proof.
Time (apply insert_updateP').
Time Qed.
Time
Lemma singleton_update i (x y : A) : x ~~> y \226\134\146 {[i := x]} ~~> {[i := y]}.
Time Proof.
Time (apply insert_update).
Time Qed.
Time Lemma delete_update m i : m ~~> delete i m.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> apply cmra_total_update =>n mf Hm j;
  destruct (decide (i = j)); subst).
Time -
Time move : {}(Hm j) {}.
Time rewrite !lookup_op lookup_delete left_id.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite list_op_app app_validN =>- [? ?]).
Time Arguments csumR : clear implicits.
Time
Instance csum_map_cmra_morphism  {A A' B B' : cmraT} 
 (f : A \226\134\146 A') (g : B \226\134\146 B'):
 (CmraMorphism f \226\134\146 CmraMorphism g \226\134\146 CmraMorphism (csum_map f g)).
Time Proof.
Time (split; try apply _).
Time (destruct (Hup1 n (take (length l1) lf)) as (k1, (?, ?)); auto).
Time (apply cmra_validN_op_r).
Time -
Time move : {}(Hm j) {}.
Time (destruct (Hup2 n (drop (length l1) lf)) as (k2, (?, ?)); auto).
Time exists (k1 ++ k2).
Time rewrite list_op_app app_validN.
Time by rewrite !lookup_op lookup_delete_ne.
Time Qed.
Time by destruct (HQ k1 k2) as [<- ?].
Time Lemma dom_op m1 m2 : dom (gset K) (m1 \226\139\133 m2) = dom _ m1 \226\136\170 dom _ m2.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> apply elem_of_equiv_L =>i; rewrite
  elem_of_union !elem_of_dom).
Time Qed.
Time
Lemma app_update l1 l2 k1 k2 :
  length l1 = length k1 \226\134\146 l1 ~~> k1 \226\134\146 l2 ~~> k2 \226\134\146 l1 ++ l2 ~~> k1 ++ k2.
Time Proof.
Time (rewrite !cmra_update_updateP; eauto using app_updateP with subst).
Time (unfold is_Some; setoid_rewrite lookup_op).
Time Qed.
Time
Lemma cons_updateP (P1 : A \226\134\146 Prop) (P2 Q : list A \226\134\146 Prop) 
  x l :
  x ~~>: P1 \226\134\146 l ~~>: P2 \226\134\146 (\226\136\128 y k, P1 y \226\134\146 P2 k \226\134\146 Q (y :: k)) \226\134\146 x :: l ~~>: Q.
Time Proof.
Time (intros).
Time
(eapply (app_updateP _ _ _ [x]); naive_solver eauto
  using list_singleton_updateP').
Time -
Time (intros n [a| b| ]; simpl; auto using cmra_morphism_validN).
Time Qed.
Time (destruct (m1 !! i), (m2 !! i); naive_solver).
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> move  {}=>[a|b|] =>//=; rewrite
  cmra_morphism_pcore; by destruct pcore).
Time
Lemma cons_updateP' (P1 : A \226\134\146 Prop) (P2 : list A \226\134\146 Prop) 
  x l :
  x ~~>: P1
  \226\134\146 l ~~>: P2 \226\134\146 x :: l ~~>: (\206\187 k, \226\136\131 y k', k = y :: k' \226\136\167 P1 y \226\136\167 P2 k').
Time Proof.
Time eauto  10 using cons_updateP.
Time Qed.
Time Lemma cons_update x y l k : x ~~> y \226\134\146 l ~~> k \226\134\146 x :: l ~~> y :: k.
Time Proof.
Time (rewrite !cmra_update_updateP; eauto using cons_updateP with subst).
Time Qed.
Time
Lemma list_middle_updateP (P : A \226\134\146 Prop) (Q : list A \226\134\146 Prop) 
  l1 x l2 : x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q (l1 ++ y :: l2)) \226\134\146 l1 ++ x :: l2 ~~>: Q.
Time Proof.
Time (intros).
Time (eapply app_updateP).
Time -
Time by apply cmra_update_updateP.
Time -
Time by eapply cons_updateP', cmra_update_updateP.
Time Qed.
Time -
Time naive_solver.
Time Lemma dom_included m1 m2 : m1 \226\137\188 m2 \226\134\146 dom (gset K) m1 \226\138\134 dom _ m2.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite lookup_included =>? i; rewrite
  !elem_of_dom).
Time Qed.
Time
Lemma list_middle_update l1 l2 x y :
  x ~~> y \226\134\146 l1 ++ x :: l2 ~~> l1 ++ y :: l2.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite !cmra_update_updateP =>?; eauto
  using list_middle_updateP with subst).
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> intros [xa| ya| ] [xb| yb| ] =>//=; by
  rewrite -cmra_morphism_op).
Time Qed.
Time End properties.
Time by apply is_Some_included.
Time Qed.
Time Section freshness.
Time #[local]Set Default Proof Using "Type*".
Time Context `{!Infinite K}.
Time
Lemma alloc_updateP_strong (Q : gmap K A \226\134\146 Prop) (I : K \226\134\146 Prop) 
  m x :
  pred_infinite I
  \226\134\146 \226\156\147 x \226\134\146 (\226\136\128 i, m !! i = None \226\134\146 I i \226\134\146 Q (<[i:=x]> m)) \226\134\146 m ~~>: Q.
Time Proof.
Time move  {}=>/(pred_infinite_set I (C:=gset K)) HP ? HQ.
Time (apply cmra_total_updateP).
Time (intros n mf Hm).
Time (destruct (HP (dom (gset K) (m \226\139\133 mf))) as [i [Hi1 Hi2]]).
Time
Instance list_fmap_cmra_morphism  {A B : ucmraT} (f : A \226\134\146 B)
 `{!CmraMorphism f}: (CmraMorphism (fmap f : list A \226\134\146 list B)).
Time Proof.
Time (split; try apply _).
Time (assert (m !! i = None)).
Time {
Time (eapply (not_elem_of_dom (D:=gset K))).
Time revert Hi2.
Time rewrite dom_op not_elem_of_union.
Time naive_solver.
Time }
Time (exists (<[i:=x]> m); split).
Time -
Time by apply HQ.
Time -
Time rewrite insert_singleton_op //.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite -assoc -insert_singleton_op ; last 
 by eapply (not_elem_of_dom (D:=gset K))).
Time Qed.
Time #[program]
Definition csumRF (Fa Fb : rFunctor) : rFunctor :=
  {|
  rFunctor_car := fun A _ B _ =>
                  csumR (rFunctor_car Fa A B) (rFunctor_car Fb A B);
  rFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  csumC_map (rFunctor_map Fa fg) (rFunctor_map Fb fg) |}.
Time by apply insert_validN; [ apply cmra_valid_validN |  ].
Time Qed.
Time -
Time (intros n l).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite !list_lookup_validN =>Hl i).
Time
Lemma alloc_updateP (Q : gmap K A \226\134\146 Prop) m x :
  \226\156\147 x \226\134\146 (\226\136\128 i, m !! i = None \226\134\146 Q (<[i:=x]> m)) \226\134\146 m ~~>: Q.
Time Proof.
Time move  {}=>? ?.
Time
(eapply alloc_updateP_strong with (I := \206\187 _, True); eauto
  using pred_infinite_True).
Time Qed.
Time
Lemma alloc_updateP_strong' m x (I : K \226\134\146 Prop) :
  pred_infinite I
  \226\134\146 \226\156\147 x \226\134\146 m ~~>: (\206\187 m', \226\136\131 i, I i \226\136\167 m' = <[i:=x]> m \226\136\167 m !! i = None).
Time Proof.
Time eauto using alloc_updateP_strong.
Time rewrite list_lookup_fmap.
Time by apply (cmra_morphism_validN (fmap f : option A \226\134\146 option B)).
Time -
Time (intros l).
Time (apply Some_proper).
Time rewrite -!list_fmap_compose.
Time Qed.
Time
Lemma alloc_updateP' m x :
  \226\156\147 x \226\134\146 m ~~>: (\206\187 m', \226\136\131 i, m' = <[i:=x]> m \226\136\167 m !! i = None).
Time Proof.
Time eauto using alloc_updateP.
Time (apply list_fmap_equiv_ext, cmra_morphism_core, _).
Time -
Time (intros l1 l2).
Time (<ssreflect_plugin::ssrtclintros@0> apply list_equiv_lookup =>i).
Time
by rewrite list_lookup_op !list_lookup_fmap list_lookup_op cmra_morphism_op.
Time Qed.
Time
Lemma alloc_updateP_cofinite (Q : gmap K A \226\134\146 Prop) 
  (J : gset K) m x :
  \226\156\147 x \226\134\146 (\226\136\128 i, m !! i = None \226\134\146 i \226\136\137 J \226\134\146 Q (<[i:=x]> m)) \226\134\146 m ~~>: Q.
Time Proof.
Time (eapply alloc_updateP_strong).
Time (apply (pred_infinite_set (C:=gset K))).
Time (intros E).
Time exists (fresh (J \226\136\170 E)).
Time (apply not_elem_of_union, is_fresh).
Time Qed.
Time
Lemma alloc_updateP_cofinite' m x (J : gset K) :
  \226\156\147 x \226\134\146 m ~~>: (\206\187 m', \226\136\131 i, (i \226\136\137 J) \226\136\167 m' = <[i:=x]> m \226\136\167 m !! i = None).
Time Proof.
Time eauto using alloc_updateP_cofinite.
Time Qed.
Time Qed.
Time End freshness.
Time
Lemma alloc_unit_singleton_updateP (P : A \226\134\146 Prop) 
  (Q : gmap K A \226\134\146 Prop) u i :
  \226\156\147 u \226\134\146 LeftId (\226\137\161) u (\226\139\133) \226\134\146 u ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q {[i := y]}) \226\134\146 \226\136\133 ~~>: Q.
Time #[program]
Definition listURF (F : urFunctor) : urFunctor :=
  {|
  urFunctor_car := fun A _ B _ => listUR (urFunctor_car F A B);
  urFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                   listC_map (urFunctor_map F fg) |}.
Time Proof.
Time (intros ? ? Hx HQ).
Time (<ssreflect_plugin::ssrtclintros@0> apply cmra_total_updateP =>n gf Hg).
Time (destruct (Hx n (gf !! i)) as (y, (?, Hy))).
Time {
Time move : {}(Hg i) {}.
Time rewrite !left_id.
Time (case : {}(gf !! i) {} =>[x|]; rewrite /= ?left_id //).
Time (intros; by apply cmra_valid_validN).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> exists {[i := y]}; split ; first  by auto).
Time (intros i'; destruct (decide (i' = i)) as [->| ]).
Time -
Time rewrite lookup_op lookup_singleton.
Time (move : {}Hy {}; case : {}(gf !! i) {} =>[x|]; rewrite /= ?right_id //).
Time -
Time move : {}(Hg i') {}.
Time by rewrite !lookup_op lookup_singleton_ne // !left_id.
Time Qed.
Time
Lemma alloc_unit_singleton_updateP' (P : A \226\134\146 Prop) 
  u i :
  \226\156\147 u \226\134\146 LeftId (\226\137\161) u (\226\139\133) \226\134\146 u ~~>: P \226\134\146 \226\136\133 ~~>: (\206\187 m, \226\136\131 y, m = {[i := y]} \226\136\167 P y).
Time Proof.
Time eauto using alloc_unit_singleton_updateP.
Time Next Obligation.
Time
by
 intros Fa Fb A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply csumC_map_ne;
  try apply rFunctor_ne.
Time Qed.
Time Qed.
Time Next Obligation.
Time (intros Fa Fb A ? B ? x).
Time rewrite /= -{+2}(csum_map_id x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply csum_map_ext =>y; apply rFunctor_id).
Time
Lemma alloc_unit_singleton_update (u : A) i (y : A) :
  \226\156\147 u \226\134\146 LeftId (\226\137\161) u (\226\139\133) \226\134\146 u ~~> y \226\134\146 (\226\136\133 : gmap K A) ~~> {[i := y]}.
Time Proof.
Time
(rewrite !cmra_update_updateP; eauto using alloc_unit_singleton_updateP
  with subst).
Time Qed.
Time Next Obligation.
Time (intros Fa Fb A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -csum_map_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply csum_map_ext =>y;
  apply rFunctor_compose).
Time Qed.
Time
Instance csumRF_contractive  Fa Fb:
 (rFunctorContractive Fa
  \226\134\146 rFunctorContractive Fb \226\134\146 rFunctorContractive (csumRF Fa Fb)).
Time Proof.
Time (intros ? ? A1 ? A2 ? B1 ? B2 ? n f g Hfg).
Time by apply csumC_map_ne; try apply rFunctor_contractive.
Time Qed.
Time Next Obligation.
Time
by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply listC_map_ne, urFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x).
Time rewrite /= -{+2}(list_fmap_id x).
Time (<ssreflect_plugin::ssrtclintros@0> apply list_fmap_equiv_ext =>y).
Time (apply urFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -list_fmap_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply list_fmap_equiv_ext =>y;
  apply urFunctor_compose).
Time Qed.
Time
Instance listURF_contractive  F:
 (urFunctorContractive F \226\134\146 urFunctorContractive (listURF F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply listC_map_ne, urFunctor_contractive.
Time Qed.
Time Qed.
Time
Lemma alloc_local_update m1 m2 i x :
  m1 !! i = None \226\134\146 \226\156\147 x \226\134\146 (m1, m2) ~l~> (<[i:=x]> m1, <[i:=x]> m2).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite cmra_valid_validN =>Hi ?).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mf Hmv Hm;
  simpl in *).
Time (split; auto using insert_validN).
Time (intros j; destruct (decide (i = j)) as [->| ]).
Time -
Time
(move : {}(Hm j) {}; <ssreflect_plugin::ssrtclintros@0> rewrite Hi
  symmetry_iff dist_None lookup_op op_None =>- [_ Hj]).
Time by rewrite lookup_op !lookup_insert Hj.
Time -
Time rewrite Hm lookup_insert_ne // !lookup_op lookup_insert_ne //.
Time Qed.
Time
Lemma alloc_singleton_local_update m i x :
  m !! i = None \226\134\146 \226\156\147 x \226\134\146 (m, \226\136\133) ~l~> (<[i:=x]> m, {[i := x]}).
Time Proof.
Time (apply alloc_local_update).
Time Qed.
Time
Lemma insert_local_update m1 m2 i x y x' y' :
  m1 !! i = Some x
  \226\134\146 m2 !! i = Some y
    \226\134\146 (x, y) ~l~> (x', y') \226\134\146 (m1, m2) ~l~> (<[i:=x']> m1, <[i:=y']> m2).
Time Proof.
Time
(intros Hi1 Hi2 Hup; <ssreflect_plugin::ssrtclintros@0>
  apply local_update_unital =>n mf Hmv Hm; simpl in *).
Time (destruct (Hup n (mf !! i)) as [? Hx']; simpl in *).
Time {
Time move : {}(Hmv i) {}.
Time by rewrite Hi1.
Time }
Time {
Time move : {}(Hm i) {}.
Time by rewrite lookup_op Hi1 Hi2 Some_op_opM (inj_iff Some).
Time }
Time (split; auto using insert_validN).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite Hm Hx' =>j;
  destruct (decide (i = j)) as [->| ]).
Time -
Time by rewrite lookup_insert lookup_op lookup_insert Some_op_opM.
Time -
Time by rewrite lookup_insert_ne // !lookup_op lookup_insert_ne.
Time Qed.
Time
Lemma singleton_local_update m i x y x' y' :
  m !! i = Some x
  \226\134\146 (x, y) ~l~> (x', y') \226\134\146 (m, {[i := y]}) ~l~> (<[i:=x']> m, {[i := y']}).
Time Proof.
Time (intros).
Time rewrite /singletonM /map_singleton -(insert_insert \226\136\133 i y' y).
Time by eapply insert_local_update; [  | eapply lookup_insert |  ].
Time Qed.
Time
Lemma delete_local_update m1 m2 i x `{!Exclusive x} :
  m2 !! i = Some x \226\134\146 (m1, m2) ~l~> (delete i m1, delete i m2).
Time Proof.
Time (intros Hi).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mf Hmv Hm;
  simpl in *).
Time (split; auto using delete_validN).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite Hm =>j;
  destruct (decide (i = j)) as [<-| ]).
Time -
Time rewrite lookup_op !lookup_delete left_id symmetry_iff dist_None.
Time (<ssreflect_plugin::ssrtclintros@0> apply eq_None_not_Some =>- [y Hi']).
Time move : {}(Hmv i) {}.
Time rewrite Hm lookup_op Hi Hi' -Some_op.
Time by apply exclusiveN_l.
Time -
Time by rewrite lookup_op !lookup_delete_ne // lookup_op.
Time Qed.
Time
Lemma delete_singleton_local_update m i x `{!Exclusive x} :
  (m, {[i := x]}) ~l~> (delete i m, \226\136\133).
Time Proof.
Time rewrite -(delete_singleton i x).
Time by eapply delete_local_update, lookup_singleton.
Time Qed.
Time
Lemma delete_local_update_cancelable m1 m2 i mx `{!Cancelable mx} :
  m1 !! i \226\137\161 mx \226\134\146 m2 !! i \226\137\161 mx \226\134\146 (m1, m2) ~l~> (delete i m1, delete i m2).
Time Proof.
Time (intros Hm1i Hm2i).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mf Hmv Hm;
  simpl in *).
Time (split; [ eauto using delete_validN |  ]).
Time (intros j).
Time (destruct (decide (i = j)) as [->| ]).
Time -
Time move : {}(Hm j) {}.
Time rewrite !lookup_op Hm1i Hm2i !lookup_delete.
Time (intros Hmx).
Time rewrite (cancelableN mx n (mf !! j) None) ?right_id // -Hmx -Hm1i.
Time (apply Hmv).
Time -
Time by rewrite lookup_op !lookup_delete_ne // Hm lookup_op.
Time Qed.
Time
Lemma delete_singleton_local_update_cancelable m i 
  x `{!Cancelable (Some x)} :
  m !! i \226\137\161 Some x \226\134\146 (m, {[i := x]}) ~l~> (delete i m, \226\136\133).
Time Proof.
Time (intros).
Time rewrite -(delete_singleton i x).
Time
(apply (delete_local_update_cancelable m _ i (Some x));
  [ done | by rewrite lookup_singleton ]).
Time Qed.
Time
Lemma gmap_fmap_mono {B : cmraT} (f : A \226\134\146 B) m1 m2 :
  Proper ((\226\137\161) ==> (\226\137\161)) f
  \226\134\146 (\226\136\128 x y, x \226\137\188 y \226\134\146 f x \226\137\188 f y) \226\134\146 m1 \226\137\188 m2 \226\134\146 fmap f m1 \226\137\188 fmap f m2.
Time Proof.
Time (intros ? ?).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite !lookup_included =>Hm i).
Time rewrite !lookup_fmap.
Time by apply option_fmap_mono.
Time Qed.
Time End properties.
Time Section unital_properties.
Time Context `{Countable K} {A : ucmraT}.
Time Implicit Type m : gmap K A.
Time Implicit Type i : K.
Time Implicit Types x y : A.
Time
Lemma insert_alloc_local_update m1 m2 i x x' y' :
  m1 !! i = Some x
  \226\134\146 m2 !! i = None
    \226\134\146 (x, \206\181) ~l~> (x', y') \226\134\146 (m1, m2) ~l~> (<[i:=x']> m1, <[i:=y']> m2).
Time Proof.
Time (intros Hi1 Hi2 Hup).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mf Hm1v Hm).
Time (assert (Hif : mf !! i \226\137\161{n}\226\137\161 Some x)).
Time {
Time move : {}(Hm i) {}.
Time by rewrite lookup_op Hi1 Hi2 left_id.
Time }
Time (destruct (Hup n (mf !! i)) as [Hx'v Hx'eq]).
Time {
Time move : {}(Hm1v i) {}.
Time by rewrite Hi1.
Time }
Time {
Time by rewrite Hif -(inj_iff Some) -Some_op_opM -Some_op left_id.
Time }
Time split.
Time -
Time by apply insert_validN.
Time -
Time (simpl in Hx'eq).
Time by rewrite -(insert_idN n mf i x) // -insert_op -Hm Hx'eq Hif.
Time Qed.
Time End unital_properties.
Time
Instance gmap_fmap_ne  `{Countable K} {A B : ofeT} 
 (f : A \226\134\146 B) n:
 (Proper (dist n ==> dist n) f
  \226\134\146 Proper (dist n ==> dist n) (fmap (M:=gmap K) f)).
Time Proof.
Time by intros ? m m' Hm k; rewrite !lookup_fmap; apply option_fmap_ne.
Time Qed.
Time
Instance gmap_fmap_cmra_morphism  `{Countable K} {A B : cmraT} 
 (f : A \226\134\146 B) `{!CmraMorphism f}:
 (CmraMorphism (fmap f : gmap K A \226\134\146 gmap K B)).
Time Proof.
Time (split; try apply _).
Time -
Time by intros n m ? i; rewrite lookup_fmap; apply (cmra_morphism_validN _).
Time -
Time (intros m).
Time (<ssreflect_plugin::ssrtclintros@0> apply Some_proper =>i).
Time rewrite lookup_fmap !lookup_omap lookup_fmap.
Time case : {}(m !! i) {} =>//= ?.
Time (apply cmra_morphism_pcore, _).
Time -
Time (intros m1 m2 i).
Time by rewrite lookup_op !lookup_fmap lookup_op cmra_morphism_op.
Time Qed.
Time
Definition gmapC_map `{Countable K} {A} {B} (f : A -n> B) :
  gmapC K A -n> gmapC K B := CofeMor (fmap f : gmapC K A \226\134\146 gmapC K B).
Time
Instance gmapC_map_ne  `{Countable K} {A} {B}:
 (NonExpansive (@gmapC_map K _ _ A B)).
Time Proof.
Time (intros n f g Hf m k; rewrite /= !lookup_fmap).
Time (destruct (_ !! k) eqn:?; simpl; constructor; apply Hf).
Time Qed.
Time #[program]
Definition gmapCF K `{Countable K} (F : cFunctor) : cFunctor :=
  {|
  cFunctor_car := fun A _ B _ => gmapC K (cFunctor_car F A B);
  cFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg => gmapC_map (cFunctor_map F fg) |}.
Time Next Obligation.
Time
by
 intros K ? ? F A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply gmapC_map_ne, cFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros K ? ? F A ? B ? x).
Time rewrite /= -{+2}(map_fmap_id x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply map_fmap_equiv_ext =>y ? ?;
  apply cFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros K ? ? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -map_fmap_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply map_fmap_equiv_ext =>y ? ?;
  apply cFunctor_compose).
Time Qed.
Time
Instance gmapCF_contractive  K `{Countable K} F:
 (cFunctorContractive F \226\134\146 cFunctorContractive (gmapCF K F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply gmapC_map_ne, cFunctor_contractive.
Time Qed.
Time #[program]
Definition gmapURF K `{Countable K} (F : rFunctor) : urFunctor :=
  {|
  urFunctor_car := fun A _ B _ => gmapUR K (rFunctor_car F A B);
  urFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                   gmapC_map (rFunctor_map F fg) |}.
Time Next Obligation.
Time
by
 intros K ? ? F A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply gmapC_map_ne, rFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros K ? ? F A ? B ? x).
Time rewrite /= -{+2}(map_fmap_id x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply map_fmap_equiv_ext =>y ? ?;
  apply rFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros K ? ? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -map_fmap_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply map_fmap_equiv_ext =>y ? ?;
  apply rFunctor_compose).
Time Qed.
Time
Instance gmapRF_contractive  K `{Countable K} F:
 (rFunctorContractive F \226\134\146 urFunctorContractive (gmapURF K F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply gmapC_map_ne, rFunctor_contractive.
Time Qed.

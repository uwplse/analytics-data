Time From iris.algebra Require Import proofmode_classes.
Time From iris.algebra Require Export cmra.
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
Time Canonical Structure countingC := leibnizO counting.
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
Time -
Time (intros x y z).
Time rewrite /op /counting_op.
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
Time by_cases.
Time Section cofe.
Time Context {A B : ofeT}.
Time Implicit Type a : A.
Time Implicit Type b : B.
Time
Inductive csum_equiv : Equiv (csum A B) :=
  | Cinl_equiv : forall a a', a \226\137\161 a' \226\134\146 Cinl a \226\137\161 Cinl a'
  | Cinr_equiv : forall b b', b \226\137\161 b' \226\134\146 Cinr b \226\137\161 Cinr b'
  | CsumBot_equiv : CsumBot \226\137\161 CsumBot.
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
Time Qed.
Time #[global]Instance Cinl_inj_dist  n: (Inj (dist n) (dist n) (@Cinl A B)).
Time Proof.
Time by inversion_clear 1.
Time Qed.
Time #[global]Instance Cinr_ne : (NonExpansive (@Cinr A B)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance Cinr_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (@Cinr A B)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance Cinr_inj : (Inj (\226\137\161) (\226\137\161) (@Cinr A B)).
Time Proof.
Time by inversion_clear 1.
Time Qed.
Time #[global]Instance Cinr_inj_dist  n: (Inj (dist n) (dist n) (@Cinr A B)).
Time Proof.
Time by inversion_clear 1.
Time Qed.
Time Definition csum_ofe_mixin : OfeMixin (csum A B).
Time Proof.
Time split.
Time -
Time (intros mx my; split).
Time +
Time by destruct 1; constructor; try apply equiv_dist.
Time +
Time
(intros Hxy; feed inversion Hxy 0; subst; constructor; try done;
  <ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n; by feed inversion
  Hxy n).
Time -
Time (intros n; split).
Time +
Time by intros [| a| ]; constructor.
Time +
Time by destruct 1; constructor.
Time +
Time (destruct 1; inversion_clear 1; constructor; etrans; eauto).
Time -
Time by inversion_clear 1; constructor; apply dist_S.
Time Qed.
Time Canonical Structure csumO : ofeT := OfeT (csum A B) csum_ofe_mixin.
Time #[program]
Definition csum_chain_l (c : chain csumO) (a : A) : 
  chain A :=
  {| chain_car := fun n => match c n with
                           | Cinl a' => a'
                           | _ => a
                           end |}.
Time Next Obligation.
Time (intros c a n i ?; simpl).
Time by destruct (chain_cauchy c n i).
Time Qed.
Time #[program]
Definition csum_chain_r (c : chain csumO) (b : B) : 
  chain B :=
  {| chain_car := fun n => match c n with
                           | Cinr b' => b'
                           | _ => b
                           end |}.
Time Next Obligation.
Time (intros c b n i ?; simpl).
Time by destruct (chain_cauchy c n i).
Time Qed.
Time
Definition csum_compl `{Cofe A} `{Cofe B} : Compl csumO :=
  \206\187 c,
    match c 0 with
    | Cinl a => Cinl (compl (csum_chain_l c a))
    | Cinr b => Cinr (compl (csum_chain_r c b))
    | CsumBot => CsumBot
    end.
Time #[global, program]
Instance csum_cofe  `{Cofe A} `{Cofe B}: (Cofe csumO) :=
 {| compl := csum_compl |}.
Time Next Obligation.
Time (intros ? ? n c; rewrite /compl /csum_compl).
Time
(<ssreflect_plugin::ssrtclseq@0> feed inversion chain_cauchy c 0 n ; first 
  auto with lia; constructor).
Time +
Time rewrite (conv_compl n (csum_chain_l c a')) /=.
Time (destruct (c n); naive_solver).
Time +
Time rewrite (conv_compl n (csum_chain_r c b')) /=.
Time (destruct (c n); naive_solver).
Time Qed.
Time #[global]
Instance csum_ofe_discrete :
 (OfeDiscrete A \226\134\146 OfeDiscrete B \226\134\146 OfeDiscrete csumO).
Time Proof.
Time by inversion_clear 3; constructor; apply (discrete _).
Time Qed.
Time #[global]
Instance csum_leibniz :
 (LeibnizEquiv A \226\134\146 LeibnizEquiv B \226\134\146 LeibnizEquiv csumO).
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
Time Arguments csumO : clear implicits.
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
Time Proof.
Time by destruct x.
Time Qed.
Time
Lemma csum_map_compose {A} {A'} {A''} {B} {B'} {B''} 
  (f : A \226\134\146 A') (f' : A' \226\134\146 A'') (g : B \226\134\146 B') (g' : B' \226\134\146 B'') 
  (x : csum A B) :
  csum_map (f' \226\136\152 f) (g' \226\136\152 g) x = csum_map f' g' (csum_map f g x).
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
Definition csumO_map {A} {A'} {B} {B'} (f : A -n> A') 
  (g : B -n> B') : csumO A B -n> csumO A' B' := OfeMor (csum_map f g).
Time
Instance csumO_map_ne  A A' B B': (NonExpansive2 (@csumO_map A A' B B')).
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
Time Lemma Cinl_op a a' : Cinl (a \226\139\133 a') = Cinl a \226\139\133 Cinl a'.
Time Proof.
Time done.
Time Qed.
Time Lemma Cinr_op b b' : Cinr (b \226\139\133 b') = Cinr b \226\139\133 Cinr b'.
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
Time Lemma Cinl_included a a' : Cinl a \226\137\188 Cinl a' \226\134\148 a \226\137\188 a'.
Time Proof.
Time rewrite csum_included.
Time naive_solver.
Time f_equal.
Time lia.
Time -
Time (intros x y).
Time rewrite /op /counting_op.
Time by_cases.
Time Qed.
Time Lemma Cinr_included b b' : Cinr b \226\137\188 Cinr b' \226\134\148 b \226\137\188 b'.
Time Proof.
Time rewrite csum_included.
Time naive_solver.
Time f_equal.
Time lia.
Time -
Time (intros x y).
Time rewrite /op /counting_op /valid.
Time by_cases.
Time Qed.
Time Qed.
Time
Lemma csum_includedN n x y :
  x \226\137\188{n} y
  \226\134\148 y = CsumBot
    \226\136\168 (\226\136\131 a a', x = Cinl a \226\136\167 y = Cinl a' \226\136\167 a \226\137\188{n} a')
      \226\136\168 (\226\136\131 b b', x = Cinr b \226\136\167 y = Cinr b' \226\136\167 b \226\137\188{n} b').
Time Proof.
Time split.
Time -
Time (unfold includedN).
Time
(intros [[a'| b'| ] Hy]; destruct x as [a| b| ]; inversion_clear Hy; eauto 
  10).
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
Time by_cases.
Time f_equal.
Time lia.
Time Qed.
Time #[global]
Instance is_op_counting'  (n : nat):
 (IsOp' (Count n) (Count (S n)) (Count (- 1))).
Time Proof.
Time rewrite /IsOp' /IsOp counting_op' //=.
Time by_cases.
Time f_equal.
Time lia.
Time Qed.
Time #[global]Instance counting_id_free  (z : counting): (IdFree z).
Time Proof.
Time (intros y).
Time rewrite counting_op' counting_validN'.
Time by_cases.
Time (destruct y; by_cases; intros _; inversion 1).
Time lia.
Time Qed.
Time #[global]Instance counting_full_exclusive : (Exclusive (Count 0)).
Time Proof.
Time (intros y).
Time rewrite counting_validN' counting_op'.
Time (<ssreflect_plugin::ssrtclintros@0> destruct y =>//=; by_cases).
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
Time Qed.
Time Lemma csum_cmra_mixin : CmraMixin (csum A B).
Time Proof.
Time split.
Time -
Time (intros [] n; destruct 1; constructor; by ofe_subst).
Time -
Time (intros ? ? ? ? [n a a' Ha| n b b' Hb| n] [=]; subst; eauto).
Time +
Time (destruct (pcore a) as [ca| ] eqn:?; simplify_option_eq).
Time (destruct (cmra_pcore_ne n a a' ca) as (ca', (->, ?)); auto).
Time (exists (Cinl ca'); by repeat constructor).
Time +
Time (destruct (pcore b) as [cb| ] eqn:?; simplify_option_eq).
Time (destruct (cmra_pcore_ne n b b' cb) as (cb', (->, ?)); auto).
Time (exists (Cinr cb'); by repeat constructor).
Time -
Time (intros ? [a| b| ] [a'| b'| ] H; inversion_clear H; ofe_subst; done).
Time -
Time
(intros [a| b| ]; rewrite /= ?cmra_valid_validN; naive_solver eauto using O).
Time -
Time (intros n [a| b| ]; simpl; auto using cmra_validN_S).
Time -
Time
(intros [a1| b1| ] [a2| b2| ] [a3| b3| ]; constructor; by rewrite ?assoc).
Time -
Time (intros [a1| b1| ] [a2| b2| ]; constructor; by rewrite 1?comm).
Time -
Time (intros [a| b| ] ? [=]; subst; auto).
Time +
Time (destruct (pcore a) as [ca| ] eqn:?; simplify_option_eq).
Time (constructor; eauto using cmra_pcore_l).
Time +
Time (destruct (pcore b) as [cb| ] eqn:?; simplify_option_eq).
Time (constructor; eauto using cmra_pcore_l).
Time -
Time (intros [a| b| ] ? [=]; subst; auto).
Time +
Time (destruct (pcore a) as [ca| ] eqn:?; simplify_option_eq).
Time (feed inversion cmra_pcore_idemp a ca; repeat constructor; auto).
Time +
Time (destruct (pcore b) as [cb| ] eqn:?; simplify_option_eq).
Time (feed inversion cmra_pcore_idemp b cb; repeat constructor; auto).
Time -
Time
(intros x y ?
  [->| [(a, (a', (->, (->, ?))))| (b, (b', (->, (->, ?))))]]%csum_included
  [=]).
Time +
Time exists CsumBot.
Time (rewrite csum_included; eauto).
Time +
Time (destruct (pcore a) as [ca| ] eqn:?; simplify_option_eq).
Time (destruct (cmra_pcore_mono a a' ca) as (ca', (->, ?)); auto).
Time exists (Cinl ca').
Time (rewrite csum_included; eauto  10).
Time +
Time (destruct (pcore b) as [cb| ] eqn:?; simplify_option_eq).
Time (destruct (cmra_pcore_mono b b' cb) as (cb', (->, ?)); auto).
Time exists (Cinr cb').
Time (rewrite csum_included; eauto  10).
Time -
Time
(intros n [a1| b1| ] [a2| b2| ]; simpl; eauto using cmra_validN_op_l; done).
Time -
Time (intros n [a| b| ] y1 y2 Hx Hx').
Time +
Time
(destruct y1 as [a1| b1| ], y2 as [a2| b2| ]; try by exfalso; inversion Hx').
Time
(destruct (cmra_extend n a a1 a2) as (z1, (z2, (?, (?, ?))));
  [ done | apply (inj Cinl), Hx' |  ]).
Time exists (Cinl z1),(Cinl z2).
Time by repeat constructor.
Time +
Time
(destruct y1 as [a1| b1| ], y2 as [a2| b2| ]; try by exfalso; inversion Hx').
Time
(destruct (cmra_extend n b b1 b2) as (z1, (z2, (?, (?, ?))));
  [ done | apply (inj Cinr), Hx' |  ]).
Time exists (Cinr z1),(Cinr z2).
Time by repeat constructor.
Time +
Time by exists CsumBot,CsumBot; destruct y1, y2; inversion_clear Hx'.
Time Qed.
Time Canonical Structure csumR := CmraT (csum A B) csum_cmra_mixin.
Time #[global]
Instance csum_cmra_discrete :
 (CmraDiscrete A \226\134\146 CmraDiscrete B \226\134\146 CmraDiscrete csumR).
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  apply _).
Time by move  {}=>[a|b|] HH /=; try apply cmra_discrete_valid.
Time Qed.
Time #[global]Instance Cinl_core_id  a: (CoreId a \226\134\146 CoreId (Cinl a)).
Time Proof.
Time rewrite /CoreId /=.
Time (inversion_clear 1; by repeat constructor).
Time Qed.
Time #[global]Instance Cinr_core_id  b: (CoreId b \226\134\146 CoreId (Cinr b)).
Time Proof.
Time rewrite /CoreId /=.
Time (inversion_clear 1; by repeat constructor).
Time Qed.
Time #[global]Instance Cinl_exclusive  a: (Exclusive a \226\134\146 Exclusive (Cinl a)).
Time Proof.
Time by <ssreflect_plugin::ssrtclintros@0> move  {}=>H [] ? =>[/H||].
Time Qed.
Time #[global]Instance Cinr_exclusive  b: (Exclusive b \226\134\146 Exclusive (Cinr b)).
Time Proof.
Time by <ssreflect_plugin::ssrtclintros@0> move  {}=>H [] ? =>[|/H|].
Time Qed.
Time #[global]
Instance Cinl_cancelable  a: (Cancelable a \226\134\146 Cancelable (Cinl a)).
Time Proof.
Time (move  {}=>? ? [y|y|] [z|z|] ? EQ //; inversion_clear EQ).
Time constructor.
Time by eapply (cancelableN a).
Time Qed.
Time #[global]
Instance Cinr_cancelable  b: (Cancelable b \226\134\146 Cancelable (Cinr b)).
Time Proof.
Time (move  {}=>? ? [y|y|] [z|z|] ? EQ //; inversion_clear EQ).
Time constructor.
Time by eapply (cancelableN b).
Time Qed.
Time #[global]Instance Cinl_id_free  a: (IdFree a \226\134\146 IdFree (Cinl a)).
Time Proof.
Time (intros ? [] ? EQ; inversion_clear EQ).
Time by eapply id_free0_r.
Time Qed.
Time #[global]Instance Cinr_id_free  b: (IdFree b \226\134\146 IdFree (Cinr b)).
Time Proof.
Time (intros ? [] ? EQ; inversion_clear EQ).
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
Time Lemma csum_update_l (a1 a2 : A) : a1 ~~> a2 \226\134\146 Cinl a1 ~~> Cinl a2.
Time Proof.
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
Time Qed.
Time
Lemma csum_updateP_l (P : A \226\134\146 Prop) (Q : csum A B \226\134\146 Prop) 
  a : a ~~>: P \226\134\146 (\226\136\128 a', P a' \226\134\146 Q (Cinl a')) \226\134\146 Cinl a ~~>: Q.
Time Proof.
Time (intros Hx HP n mf Hm).
Time (destruct mf as [[a'| b'| ]| ]; try by destruct Hm).
Time -
Time (destruct (Hx n (Some a')) as (c, (?, ?)); naive_solver).
Time -
Time
(destruct (Hx n None) as (c, (?, ?)); naive_solver eauto
  using cmra_validN_op_l).
Time Qed.
Time
Lemma csum_updateP_r (P : B \226\134\146 Prop) (Q : csum A B \226\134\146 Prop) 
  b : b ~~>: P \226\134\146 (\226\136\128 b', P b' \226\134\146 Q (Cinr b')) \226\134\146 Cinr b ~~>: Q.
Time Proof.
Time (intros Hx HP n mf Hm).
Time (destruct mf as [[a'| b'| ]| ]; try by destruct Hm).
Time -
Time (destruct (Hx n (Some b')) as (c, (?, ?)); naive_solver).
Time -
Time
(destruct (Hx n None) as (c, (?, ?)); naive_solver eauto
  using cmra_validN_op_l).
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
Time }
Time split.
Time done.
Time by destruct mf as [[]| ]; inversion_clear Ha1; constructor.
Time Qed.
Time
Lemma csum_local_update_r (b1 b2 b1' b2' : B) :
  (b1, b2) ~l~> (b1', b2') \226\134\146 (Cinr b1, Cinr b2) ~l~> (Cinr b1', Cinr b2').
Time Proof.
Time (intros Hup n mf ? Ha1; simpl in *).
Time (destruct (Hup n (mf \226\137\171= maybe Cinr)); auto).
Time {
Time by destruct mf as [[]| ]; inversion_clear Ha1.
Time }
Time split.
Time done.
Time by destruct mf as [[]| ]; inversion_clear Ha1; constructor.
Time Qed.
Time End cmra.
Time Arguments csumR : clear implicits.
Time
Instance csum_map_cmra_morphism  {A A' B B' : cmraT} 
 (f : A \226\134\146 A') (g : B \226\134\146 B'):
 (CmraMorphism f \226\134\146 CmraMorphism g \226\134\146 CmraMorphism (csum_map f g)).
Time Proof.
Time (split; try apply _).
Time -
Time (intros n [a| b| ]; simpl; auto using cmra_morphism_validN).
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> move  {}=>[a|b|] =>//=; rewrite
  -cmra_morphism_pcore; by destruct pcore).
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> intros [xa| ya| ] [xb| yb| ] =>//=; by
  rewrite cmra_morphism_op).
Time Qed.
Time #[program]
Definition csumRF (Fa Fb : rFunctor) : rFunctor :=
  {|
  rFunctor_car := fun A _ B _ =>
                  csumR (rFunctor_car Fa A B) (rFunctor_car Fb A B);
  rFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  csumO_map (rFunctor_map Fa fg) (rFunctor_map Fb fg) |}.
Time Next Obligation.
Time
by
 intros Fa Fb A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply csumO_map_ne;
  try apply rFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros Fa Fb A ? B ? x).
Time rewrite /= -{+2}(csum_map_id x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply csum_map_ext =>y; apply rFunctor_id).
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
Time by apply csumO_map_ne; try apply rFunctor_contractive.
Time Qed.

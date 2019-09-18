Time From iris.algebra Require Export frac agree local_updates.
Time From iris.algebra Require Import proofmode_classes.
Time From iris.base_logic Require Import base_logic.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time
Record auth (A : Type) :=
 Auth {auth_auth_proj : option (frac * agree A); auth_frag_proj : A}.
Time Add Printing Constructor auth.
Time Arguments Auth {_} _ _.
Time Arguments auth_auth_proj {_} _.
Time Arguments auth_frag_proj {_} _.
Time Instance: (Params (@Auth) 1) := { }.
Time Instance: (Params (@auth_auth_proj) 1) := { }.
Time Instance: (Params (@auth_frag_proj) 1) := { }.
Time Definition auth_frag {A : ucmraT} (a : A) : auth A := Auth None a.
Time
Definition auth_auth {A : ucmraT} (q : Qp) (a : A) : 
  auth A := Auth (Some (q, to_agree a)) \206\181.
Time Typeclasses Opaque auth_auth auth_frag.
Time Instance: (Params (@auth_frag) 1) := { }.
Time Instance: (Params (@auth_auth) 1) := { }.
Time Notation "\226\151\175 a" := (auth_frag a) (at level 20).
Time
Notation "\226\151\143{ q } a" := (auth_auth q a) (at level 20, format "\226\151\143{ q }  a").
Time Notation "\226\151\143 a" := (auth_auth 1 a) (at level 20).
Time Section ofe.
Time Context {A : ofeT}.
Time Implicit Type a : option (frac * agree A).
Time Implicit Type b : A.
Time Implicit Types x y : auth A.
Time
Instance auth_equiv : (Equiv (auth A)) :=
 (\206\187 x y,
    auth_auth_proj x \226\137\161 auth_auth_proj y \226\136\167 auth_frag_proj x \226\137\161 auth_frag_proj y).
Time
Instance auth_dist : (Dist (auth A)) :=
 (\206\187 n x y,
    auth_auth_proj x \226\137\161{n}\226\137\161 auth_auth_proj y
    \226\136\167 auth_frag_proj x \226\137\161{n}\226\137\161 auth_frag_proj y).
Time #[global]Instance Auth_ne : (NonExpansive2 (@Auth A)).
Time Proof.
Time by split.
Time Qed.
Time #[global]
Instance Auth_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) (@Auth A)).
Time Proof.
Time by split.
Time Qed.
Time #[global]
Instance auth_auth_proj_ne : (NonExpansive (@auth_auth_proj A)).
Time Proof.
Time by destruct 1.
Time Qed.
Time #[global]
Instance auth_auth_proj_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (@auth_auth_proj A)).
Time Proof.
Time by destruct 1.
Time Qed.
Time #[global]
Instance auth_frag_proj_ne : (NonExpansive (@auth_frag_proj A)).
Time Proof.
Time by destruct 1.
Time Qed.
Time #[global]
Instance auth_frag_proj_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (@auth_frag_proj A)).
Time Proof.
Time by destruct 1.
Time Qed.
Time Definition auth_ofe_mixin : OfeMixin (auth A).
Time Proof.
Time by apply (iso_ofe_mixin (\206\187 x, (auth_auth_proj x, auth_frag_proj x))).
Time Qed.
Time Canonical Structure authO := OfeT (auth A) auth_ofe_mixin.
Time #[global]
Instance Auth_discrete  a b: (Discrete a \226\134\146 Discrete b \226\134\146 Discrete (Auth a b)).
Time Proof.
Time by intros ? ? [? ?] [? ?]; split; apply : {}discrete {}.
Time Qed.
Time #[global]
Instance auth_ofe_discrete : (OfeDiscrete A \226\134\146 OfeDiscrete authO).
Time Proof.
Time (intros ? [? ?]; apply _).
Time Qed.
Time End ofe.
Time Arguments authO : clear implicits.
Time Section cmra.
Time Context {A : ucmraT}.
Time Implicit Types a b : A.
Time Implicit Types x y : auth A.
Time #[global]Instance auth_frag_ne : (NonExpansive (@auth_frag A)).
Time Proof.
Time done.
Time Qed.
Time #[global]
Instance auth_frag_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (@auth_frag A)).
Time Proof.
Time done.
Time Qed.
Time #[global]Instance auth_auth_ne  q: (NonExpansive (@auth_auth A q)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance auth_auth_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) (@auth_auth A)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance auth_auth_discrete  q a:
 (Discrete a \226\134\146 Discrete (\206\181 : A) \226\134\146 Discrete (\226\151\143{q} a)).
Time Proof.
Time (intros).
Time (apply Auth_discrete; apply _).
Time Qed.
Time #[global]Instance auth_frag_discrete  a: (Discrete a \226\134\146 Discrete (\226\151\175 a)).
Time Proof.
Time (intros).
Time (apply Auth_discrete; apply _).
Time Qed.
Time
Instance auth_valid : (Valid (auth A)) :=
 (\206\187 x,
    match auth_auth_proj x with
    | Some (q, ag) =>
        \226\156\147 q
        \226\136\167 (\226\136\128 n, \226\136\131 a, ag \226\137\161{n}\226\137\161 to_agree a \226\136\167 auth_frag_proj x \226\137\188{n} a \226\136\167 \226\156\147{n} a)
    | None => \226\156\147 auth_frag_proj x
    end).
Time #[global]Arguments auth_valid !_ /.
Time
Instance auth_validN : (ValidN (auth A)) :=
 (\206\187 n x,
    match auth_auth_proj x with
    | Some (q, ag) =>
        \226\156\147{n} q
        \226\136\167 (\226\136\131 a, ag \226\137\161{n}\226\137\161 to_agree a \226\136\167 auth_frag_proj x \226\137\188{n} a \226\136\167 \226\156\147{n} a)
    | None => \226\156\147{n} auth_frag_proj x
    end).
Time #[global]Arguments auth_validN _ !_ /.
Time
Instance auth_pcore : (PCore (auth A)) :=
 (\206\187 x, Some (Auth (core (auth_auth_proj x)) (core (auth_frag_proj x)))).
Time
Instance auth_op : (Op (auth A)) :=
 (\206\187 x y,
    Auth (auth_auth_proj x \226\139\133 auth_auth_proj y)
      (auth_frag_proj x \226\139\133 auth_frag_proj y)).
Time
Definition auth_valid_eq :
  valid =
  (\206\187 x,
     match auth_auth_proj x with
     | Some (q, ag) =>
         \226\156\147 q
         \226\136\167 (\226\136\128 n, \226\136\131 a, ag \226\137\161{n}\226\137\161 to_agree a \226\136\167 auth_frag_proj x \226\137\188{n} a \226\136\167 \226\156\147{n} a)
     | None => \226\156\147 auth_frag_proj x
     end) := eq_refl _.
Time
Definition auth_validN_eq :
  validN =
  (\206\187 n x,
     match auth_auth_proj x with
     | Some (q, ag) =>
         \226\156\147{n} q
         \226\136\167 (\226\136\131 a, ag \226\137\161{n}\226\137\161 to_agree a \226\136\167 auth_frag_proj x \226\137\188{n} a \226\136\167 \226\156\147{n} a)
     | None => \226\156\147{n} auth_frag_proj x
     end) := eq_refl _.
Time
Lemma auth_included (x y : auth A) :
  x \226\137\188 y
  \226\134\148 auth_auth_proj x \226\137\188 auth_auth_proj y \226\136\167 auth_frag_proj x \226\137\188 auth_frag_proj y.
Time Proof.
Time
(split;
  [ intros [[z1 z2] Hz]; split; [ exists z1 | exists z2 ]; apply Hz |  ]).
Time (intros [[z1 Hz1] [z2 Hz2]]; exists (Auth z1 z2); split; auto).
Time Qed.
Time Lemma auth_auth_proj_validN n x : \226\156\147{n} x \226\134\146 \226\156\147{n} auth_auth_proj x.
Time Proof.
Time (destruct x as [[[]| ]]; [ by intros (?, (?, (->, ?))) | done ]).
Time Qed.
Time Lemma auth_frag_proj_validN n x : \226\156\147{n} x \226\134\146 \226\156\147{n} auth_frag_proj x.
Time Proof.
Time rewrite auth_validN_eq.
Time (destruct x as [[[]| ]]; [  | done ]).
Time naive_solver eauto using cmra_validN_includedN.
Time Qed.
Time Lemma auth_auth_proj_valid x : \226\156\147 x \226\134\146 \226\156\147 auth_auth_proj x.
Time Proof.
Time (destruct x as [[[]| ]]; [ intros [? H] | done ]).
Time (split; [ done |  ]).
Time (intros n).
Time by destruct (H n) as [? [-> [? ?]]].
Time Qed.
Time Lemma auth_frag_proj_valid x : \226\156\147 x \226\134\146 \226\156\147 auth_frag_proj x.
Time Proof.
Time (destruct x as [[[]| ]]; [ intros [? H] | done ]).
Time (apply cmra_valid_validN).
Time (intros n).
Time (destruct (H n) as [? [? [? ?]]]).
Time naive_solver eauto using cmra_validN_includedN.
Time Qed.
Time Lemma auth_frag_validN n a : \226\156\147{n} (\226\151\175 a) \226\134\148 \226\156\147{n} a.
Time Proof.
Time done.
Time Qed.
Time Lemma auth_auth_frac_validN n q a : \226\156\147{n} (\226\151\143{q} a) \226\134\148 \226\156\147{n} q \226\136\167 \226\156\147{n} a.
Time Proof.
Time rewrite auth_validN_eq /=.
Time (apply and_iff_compat_l).
Time split.
Time -
Time by intros [? [->%to_agree_injN []]].
Time -
Time naive_solver eauto using ucmra_unit_leastN.
Time Qed.
Time Lemma auth_auth_validN n a : \226\156\147{n} a \226\134\148 \226\156\147{n} (\226\151\143 a).
Time Proof.
Time rewrite auth_auth_frac_validN -cmra_discrete_valid_iff frac_valid'.
Time naive_solver.
Time Qed.
Time
Lemma auth_both_frac_validN n q a b :
  \226\156\147{n} (\226\151\143{q} a \226\139\133 \226\151\175 b) \226\134\148 \226\156\147{n} q \226\136\167 b \226\137\188{n} a \226\136\167 \226\156\147{n} a.
Time Proof.
Time rewrite auth_validN_eq /=.
Time (apply and_iff_compat_l).
Time setoid_rewrite (left_id _ _ b).
Time split.
Time -
Time by intros [? [->%to_agree_injN]].
Time -
Time naive_solver.
Time Qed.
Time Lemma auth_both_validN n a b : \226\156\147{n} (\226\151\143 a \226\139\133 \226\151\175 b) \226\134\148 b \226\137\188{n} a \226\136\167 \226\156\147{n} a.
Time Proof.
Time rewrite auth_both_frac_validN -cmra_discrete_valid_iff frac_valid'.
Time naive_solver.
Time Qed.
Time Lemma auth_frag_valid a : \226\156\147 (\226\151\175 a) \226\134\148 \226\156\147 a.
Time Proof.
Time done.
Time Qed.
Time Lemma auth_auth_frac_valid q a : \226\156\147 (\226\151\143{q} a) \226\134\148 \226\156\147 q \226\136\167 \226\156\147 a.
Time Proof.
Time rewrite auth_valid_eq /=.
Time (apply and_iff_compat_l).
Time split.
Time -
Time (intros H').
Time (apply cmra_valid_validN).
Time (intros n).
Time by destruct (H' n) as [? [->%to_agree_injN [? ?]]].
Time -
Time (intros).
Time exists a.
Time (split; [ done |  ]).
Time (split; by [ apply ucmra_unit_leastN | apply cmra_valid_validN ]).
Time Qed.
Time Lemma auth_auth_valid a : \226\156\147 (\226\151\143 a) \226\134\148 \226\156\147 a.
Time Proof.
Time rewrite auth_auth_frac_valid frac_valid'.
Time naive_solver.
Time Qed.
Time
Lemma auth_both_frac_valid_2 q a b : \226\156\147 q \226\134\146 \226\156\147 a \226\134\146 b \226\137\188 a \226\134\146 \226\156\147 (\226\151\143{q} a \226\139\133 \226\151\175 b).
Time Proof.
Time (intros Val1 Val2 Incl).
Time rewrite auth_valid_eq /=.
Time (split; [ done |  ]).
Time (intros n).
Time exists a.
Time (split; [ done |  ]).
Time rewrite left_id.
Time (split; by [ apply cmra_included_includedN | apply cmra_valid_validN ]).
Time Qed.
Time Lemma auth_both_valid_2 a b : \226\156\147 a \226\134\146 b \226\137\188 a \226\134\146 \226\156\147 (\226\151\143 a \226\139\133 \226\151\175 b).
Time Proof.
Time (intros ? ?).
Time by apply auth_both_frac_valid_2.
Time Qed.
Time
Lemma auth_valid_discrete `{!CmraDiscrete A} x :
  \226\156\147 x
  \226\134\148 match auth_auth_proj x with
    | Some (q, ag) =>
        \226\156\147 q \226\136\167 (\226\136\131 a, ag \226\137\161 to_agree a \226\136\167 auth_frag_proj x \226\137\188 a \226\136\167 \226\156\147 a)
    | None => \226\156\147 auth_frag_proj x
    end.
Time Proof.
Time rewrite auth_valid_eq.
Time (destruct x as [[[? ?]| ] ?]; simpl; [  | done ]).
Time setoid_rewrite  <- cmra_discrete_included_iff.
Time setoid_rewrite  <- (discrete_iff _ a).
Time setoid_rewrite  <- cmra_discrete_valid_iff.
Time naive_solver eauto using O.
Time Qed.
Time
Lemma auth_both_frac_valid `{!CmraDiscrete A} q a 
  b : \226\156\147 (\226\151\143{q} a \226\139\133 \226\151\175 b) \226\134\148 \226\156\147 q \226\136\167 b \226\137\188 a \226\136\167 \226\156\147 a.
Time Proof.
Time rewrite auth_valid_discrete /=.
Time (apply and_iff_compat_l).
Time setoid_rewrite (left_id _ _ b).
Time split.
Time -
Time by intros [? [->%to_agree_inj]].
Time -
Time naive_solver.
Time Qed.
Time
Lemma auth_both_valid `{!CmraDiscrete A} a b : \226\156\147 (\226\151\143 a \226\139\133 \226\151\175 b) \226\134\148 b \226\137\188 a \226\136\167 \226\156\147 a.
Time Proof.
Time rewrite auth_both_frac_valid frac_valid'.
Time naive_solver.
Time Qed.
Time Lemma auth_cmra_mixin : CmraMixin (auth A).
Time Proof.
Time (apply cmra_total_mixin).
Time -
Time eauto.
Time -
Time by intros n x y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
Time -
Time by intros n y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
Time -
Time (intros n [x a] [y b] [Hx Ha]; simpl in *).
Time rewrite !auth_validN_eq.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct Hx as [x y Hx| ] ; first 
  destruct Hx as [? Hx]; [ destruct x, y |  ]; intros VI; ofe_subst; auto).
Time -
Time
(intros [[[]| ]]; rewrite /= ?auth_valid_eq ?auth_validN_eq /=
  ?cmra_valid_validN; naive_solver).
Time -
Time
(intros n [[[]| ]]; rewrite !auth_validN_eq /=; naive_solver eauto
  using dist_S, cmra_includedN_S, cmra_validN_S).
Time -
Time by split; simpl; rewrite assoc.
Time -
Time by split; simpl; rewrite comm.
Time -
Time by split; simpl; rewrite ?cmra_core_l.
Time -
Time by split; simpl; rewrite ?cmra_core_idemp.
Time -
Time (intros ? ?; rewrite !auth_included; intros [? ?]).
Time by split; simpl; apply : {}cmra_core_mono {}.
Time -
Time (assert (\226\136\128 n (a b1 b2 : A), b1 \226\139\133 b2 \226\137\188{n} a \226\134\146 b1 \226\137\188{n} a)).
Time {
Time (intros n a b1 b2 <-; apply cmra_includedN_l).
Time }
Time
(intros n [[[q1 a1]| ] b1] [[[q2 a2]| ] b2]; rewrite auth_validN_eq /=;
  try naive_solver eauto using cmra_validN_op_l, cmra_validN_includedN).
Time (intros [? [a [Eq [? Valid]]]]).
Time (assert (Eq' : a1 \226\137\161{n}\226\137\161 a2)).
Time {
Time by apply agree_op_invN; rewrite Eq.
Time }
Time (split; [ naive_solver eauto using cmra_validN_op_l |  ]).
Time exists a.
Time rewrite -Eq -Eq' agree_idemp.
Time naive_solver.
Time -
Time (intros n x y1 y2 ? [? ?]; simpl in *).
Time
(destruct
  (cmra_extend n (auth_auth_proj x) (auth_auth_proj y1) (auth_auth_proj y2))
  as (ea1, (ea2, (?, (?, ?)))); auto using auth_auth_proj_validN).
Time
(destruct
  (cmra_extend n (auth_frag_proj x) (auth_frag_proj y1) (auth_frag_proj y2))
  as (b1, (b2, (?, (?, ?)))); auto using auth_frag_proj_validN).
Time by exists (Auth ea1 b1),(Auth ea2 b2).
Time Qed.
Time Canonical Structure authR := CmraT (auth A) auth_cmra_mixin.
Time #[global]
Instance auth_cmra_discrete : (CmraDiscrete A \226\134\146 CmraDiscrete authR).
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  apply _).
Time (intros [[[]| ] ?]; rewrite auth_valid_eq auth_validN_eq /=; auto).
Time -
Time setoid_rewrite  <- cmra_discrete_included_iff.
Time rewrite -cmra_discrete_valid_iff.
Time setoid_rewrite  <- cmra_discrete_valid_iff.
Time setoid_rewrite  <- (discrete_iff _ a).
Time tauto.
Time -
Time by rewrite -cmra_discrete_valid_iff.
Time Qed.
Time Instance auth_empty : (Unit (auth A)) := (Auth \206\181 \206\181).
Time Lemma auth_ucmra_mixin : UcmraMixin (auth A).
Time Proof.
Time (split; simpl).
Time -
Time rewrite auth_valid_eq /=.
Time (apply ucmra_unit_valid).
Time -
Time by intros x; constructor; rewrite /= left_id.
Time -
Time (do 2 constructor; [ done | apply (core_id_core _) ]).
Time Qed.
Time Canonical Structure authUR := UcmraT (auth A) auth_ucmra_mixin.
Time #[global]Instance auth_frag_core_id  a: (CoreId a \226\134\146 CoreId (\226\151\175 a)).
Time Proof.
Time (do 2 constructor; simpl; auto).
Time by apply core_id_core.
Time Qed.
Time Lemma auth_frag_op a b : \226\151\175 (a \226\139\133 b) = \226\151\175 a \226\139\133 \226\151\175 b.
Time Proof.
Time done.
Time Qed.
Time Lemma auth_frag_mono a b : a \226\137\188 b \226\134\146 \226\151\175 a \226\137\188 \226\151\175 b.
Time Proof.
Time (intros [c ->]).
Time rewrite auth_frag_op.
Time (apply cmra_included_l).
Time Qed.
Time #[global]
Instance auth_frag_sep_homomorphism :
 (MonoidHomomorphism op op (\226\137\161) (@auth_frag A)).
Time Proof.
Time by split; [ split; try apply _ |  ].
Time Qed.
Time
Lemma auth_both_frac_op q a b : Auth (Some (q, to_agree a)) b \226\137\161 \226\151\143{q} a \226\139\133 \226\151\175 b.
Time Proof.
Time by rewrite /op /auth_op /= left_id.
Time Qed.
Time Lemma auth_both_op a b : Auth (Some (1%Qp, to_agree a)) b \226\137\161 \226\151\143 a \226\139\133 \226\151\175 b.
Time Proof.
Time by rewrite auth_both_frac_op.
Time Qed.
Time Lemma auth_auth_frac_op p q a : \226\151\143{p + q} a \226\137\161 \226\151\143{p} a \226\139\133 \226\151\143{q} a.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> intros; split; simpl ; last  by rewrite
 left_id).
Time by rewrite -Some_op -pair_op agree_idemp.
Time Qed.
Time
Lemma auth_auth_frac_op_invN n p a q b : \226\156\147{n} (\226\151\143{p} a \226\139\133 \226\151\143{q} b) \226\134\146 a \226\137\161{n}\226\137\161 b.
Time Proof.
Time rewrite /op /auth_op /= left_id -Some_op -pair_op auth_validN_eq /=.
Time (intros (?, (?, (Eq, (?, ?))))).
Time (apply to_agree_injN, agree_op_invN).
Time by rewrite Eq.
Time Qed.
Time Lemma auth_auth_frac_op_inv p a q b : \226\156\147 (\226\151\143{p} a \226\139\133 \226\151\143{q} b) \226\134\146 a \226\137\161 b.
Time Proof.
Time (intros ?).
Time (apply equiv_dist).
Time (intros n).
Time by eapply auth_auth_frac_op_invN, cmra_valid_validN.
Time Qed.
Time
Lemma auth_auth_frac_op_invL `{!LeibnizEquiv A} q 
  a p b : \226\156\147 (\226\151\143{p} a \226\139\133 \226\151\143{q} b) \226\134\146 a = b.
Time Proof.
Time by intros ?%leibniz_equiv%auth_auth_frac_op_inv.
Time Qed.
Time
Lemma auth_equivI {M} x y :
  x \226\137\161 y
  \226\138\163\226\138\162@{ uPredI M} auth_auth_proj x \226\137\161 auth_auth_proj y
                 \226\136\167 auth_frag_proj x \226\137\161 auth_frag_proj y.
Time Proof.
Time by uPred.unseal.
Time Qed.
Time
Lemma auth_validI {M} x :
  \226\156\147 x
  \226\138\163\226\138\162@{ uPredI M} match auth_auth_proj x with
                 | Some (q, ag) =>
                     \226\156\147 q
                     \226\136\167 (\226\136\131 a,
                          ag \226\137\161 to_agree a
                          \226\136\167 (\226\136\131 b, a \226\137\161 auth_frag_proj x \226\139\133 b) \226\136\167 \226\156\147 a)
                 | None => \226\156\147 auth_frag_proj x
                 end.
Time Proof.
Time uPred.unseal.
Time by destruct x as [[[]| ]].
Time Qed.
Time Lemma auth_frag_validI {M} (a : A) : \226\156\147 (\226\151\175 a) \226\138\163\226\138\162@{ uPredI M} \226\156\147 a.
Time Proof.
Time by rewrite auth_validI.
Time Qed.
Time
Lemma auth_both_validI {M} q (a b : A) :
  \226\156\147 (\226\151\143{q} a \226\139\133 \226\151\175 b) \226\138\163\226\138\162@{ uPredI M} \226\156\147 q \226\136\167 (\226\136\131 c, a \226\137\161 b \226\139\133 c) \226\136\167 \226\156\147 a.
Time Proof.
Time rewrite -auth_both_frac_op auth_validI /=.
Time (apply bi.and_proper; [ done |  ]).
Time setoid_rewrite agree_equivI.
Time iSplit.
Time -
Time iDestruct 1 as ( a' ) "[#Eq [H V]]".
Time iDestruct "H" as ( b' ) "H".
Time iRewrite - "Eq" in "H".
Time iRewrite - "Eq" in "V".
Time auto.
Time -
Time iDestruct 1 as "[H V]".
Time iExists a.
Time auto.
Time Qed.
Time
Lemma auth_auth_validI {M} q (a b : A) : \226\156\147 (\226\151\143{q} a) \226\138\163\226\138\162@{ uPredI M} \226\156\147 q \226\136\167 \226\156\147 a.
Time Proof.
Time rewrite auth_validI /=.
Time (apply bi.and_proper; [ done |  ]).
Time setoid_rewrite agree_equivI.
Time iSplit.
Time -
Time iDestruct 1 as ( a' ) "[Eq [_ V]]".
Time by iRewrite - "Eq" in "V".
Time -
Time iIntros "V".
Time iExists a.
Time (iSplit; [ done |  ]).
Time (iSplit; [  | done ]).
Time iExists a.
Time by rewrite left_id.
Time Qed.
Time
Lemma auth_update a b a' b' :
  (a, b) ~l~> (a', b') \226\134\146 \226\151\143 a \226\139\133 \226\151\175 b ~~> \226\151\143 a' \226\139\133 \226\151\175 b'.
Time Proof.
Time (intros Hup; apply cmra_total_update).
Time
(move  {}=>n [[[? ?]|] bf1] [/= VL [a0 [Eq [[bf2 Ha] VL2]]]]; do 2 red;
  simpl in *).
Time +
Time exfalso.
Time move : {}VL {} =>/frac_valid'.
Time rewrite frac_op'.
Time by apply Qp_not_plus_q_ge_1.
Time +
Time (split; [ done |  ]).
Time (apply to_agree_injN in Eq).
Time
(move : {}Ha {}; <ssreflect_plugin::ssrtclintros@0> rewrite !left_id -assoc
  =>Ha).
Time (destruct (Hup n (Some (bf1 \226\139\133 bf2))); [ by rewrite Eq.. | idtac ]).
Time (simpl in *).
Time exists a'.
Time (split; [ done |  ]).
Time (split; [  | done ]).
Time exists bf2.
Time by rewrite left_id -assoc.
Time Qed.
Time
Lemma auth_update_alloc a a' b' : (a, \206\181) ~l~> (a', b') \226\134\146 \226\151\143 a ~~> \226\151\143 a' \226\139\133 \226\151\175 b'.
Time Proof.
Time (intros).
Time rewrite -(right_id _ _ (\226\151\143 a)).
Time by apply auth_update.
Time Qed.
Time Lemma auth_update_auth a a' b' : (a, \206\181) ~l~> (a', b') \226\134\146 \226\151\143 a ~~> \226\151\143 a'.
Time Proof.
Time (intros).
Time
(<ssreflect_plugin::ssrtclseq@0> etrans ; first  exact : {}auth_update_alloc
 {}).
Time exact : {}cmra_update_op_l {}.
Time Qed.
Time Lemma auth_update_core_id a b `{!CoreId b} : b \226\137\188 a \226\134\146 \226\151\143 a ~~> \226\151\143 a \226\139\133 \226\151\175 b.
Time Proof.
Time (intros Hincl).
Time apply : {}auth_update_alloc {}.
Time rewrite -(left_id \206\181 _ b).
Time apply : {}core_id_local_update {}.
Time done.
Time Qed.
Time
Lemma auth_update_dealloc a b a' : (a, b) ~l~> (a', \206\181) \226\134\146 \226\151\143 a \226\139\133 \226\151\175 b ~~> \226\151\143 a'.
Time Proof.
Time (intros).
Time rewrite -(right_id _ _ (\226\151\143 a')).
Time by apply auth_update.
Time Qed.
Time
Lemma auth_local_update (a b0 b1 a' b0' b1' : A) :
  (b0, b1) ~l~> (b0', b1')
  \226\134\146 b0' \226\137\188 a'
    \226\134\146 \226\156\147 a' \226\134\146 (\226\151\143 a \226\139\133 \226\151\175 b0, \226\151\143 a \226\139\133 \226\151\175 b1) ~l~> (\226\151\143 a' \226\139\133 \226\151\175 b0', \226\151\143 a' \226\139\133 \226\151\175 b1').
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite !local_update_unital =>Hup ? ? n
 /=).
Time move  {}=>[[[qc ac]|] bc] /auth_both_validN [Le Val] [] /=.
Time -
Time move  {}=>Ha.
Time exfalso.
Time move : {}Ha {}.
Time rewrite right_id -Some_op -pair_op.
Time move  {}=>/Some_dist_inj [/=].
Time (<ssreflect_plugin::ssrtclintros@0> rewrite frac_op' =>Eq _).
Time (apply (Qp_not_plus_q_ge_1 qc)).
Time by rewrite -Eq.
Time -
Time move  {}=>_.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite !left_id =>?).
Time (destruct (Hup n bc) as [Hval' Heq]; eauto using cmra_validN_includedN).
Time rewrite -!auth_both_op auth_validN_eq /=.
Time (split_and !; [ done |  | done ]).
Time exists a'.
Time
(split_and !;
  [ done | by apply cmra_included_includedN | by apply cmra_valid_validN ]).
Time Qed.
Time End cmra.
Time Arguments authR : clear implicits.
Time Arguments authUR : clear implicits.
Time
Instance is_op_auth_frag  {A : ucmraT} (a b1 b2 : A):
 (IsOp a b1 b2 \226\134\146 IsOp' (\226\151\175 a) (\226\151\175 b1) (\226\151\175 b2)).
Time Proof.
Time done.
Time Qed.
Time
Instance is_op_auth_auth_frac  {A : ucmraT} (q q1 q2 : frac) 
 (a : A): (IsOp q q1 q2 \226\134\146 IsOp' (\226\151\143{q} a) (\226\151\143{q1} a) (\226\151\143{q2} a)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsOp' /IsOp =>{+}->).
Time by rewrite -auth_auth_frac_op.
Time Qed.
Time
Definition auth_map {A} {B} (f : A \226\134\146 B) (x : auth A) : 
  auth B :=
  Auth (prod_map id (agree_map f) <$> auth_auth_proj x)
    (f (auth_frag_proj x)).
Time Lemma auth_map_id {A} (x : auth A) : auth_map id x = x.
Time Proof.
Time (destruct x as [[[]| ]]; by rewrite // /auth_map /= agree_map_id).
Time Qed.
Time
Lemma auth_map_compose {A} {B} {C} (f : A \226\134\146 B) (g : B \226\134\146 C) 
  (x : auth A) : auth_map (g \226\136\152 f) x = auth_map g (auth_map f x).
Time Proof.
Time (destruct x as [[[]| ]]; by rewrite // /auth_map /= agree_map_compose).
Time Qed.
Time
Lemma auth_map_ext {A B : ofeT} (f g : A \226\134\146 B) `{!NonExpansive f} 
  x : (\226\136\128 x, f x \226\137\161 g x) \226\134\146 auth_map f x \226\137\161 auth_map g x.
Time Proof.
Time (constructor; simpl; auto).
Time
(<ssreflect_plugin::ssrtclintros@0> apply option_fmap_equiv_ext =>a; by
  rewrite /prod_map /= agree_map_ext).
Time Qed.
Time
Instance auth_map_ne  {A B : ofeT} (f : A -> B) `{Hf : !NonExpansive f}:
 (NonExpansive (auth_map f)).
Time Proof.
Time (intros n [? ?] [? ?] [? ?]; split; simpl in *; [  | by apply Hf ]).
Time
(<ssreflect_plugin::ssrtclintros@0> apply option_fmap_ne; [  | done ] =>x y
 ?).
Time (apply prod_map_ne; [ done |  | done ]).
Time by apply agree_map_ne.
Time Qed.
Time
Instance auth_map_cmra_morphism  {A B : ucmraT} (f : A \226\134\146 B):
 (CmraMorphism f \226\134\146 CmraMorphism (auth_map f)).
Time Proof.
Time (split; try apply _).
Time -
Time
(intros n [[[? ?]| ] b]; rewrite !auth_validN_eq;
  [ 
  | naive_solver
  eauto
  using cmra_morphism_monotoneN, cmra_morphism_validN ]).
Time (intros [? [a' [Eq [? ?]]]]).
Time (split; [ done |  ]).
Time exists (f a').
Time rewrite -agree_map_to_agree -Eq.
Time naive_solver eauto using cmra_morphism_monotoneN, cmra_morphism_validN.
Time -
Time (intros [? ?]).
Time (apply Some_proper; rewrite /auth_map /=).
Time by f_equiv; rewrite /= cmra_morphism_core.
Time -
Time
(intros [[[? ?]| ] ?] [[[? ?]| ] ?];
  try <ssreflect_plugin::ssrtclintros@0> apply Auth_proper =>//=; by rewrite
  cmra_morphism_op).
Time Qed.
Time
Definition authO_map {A} {B} (f : A -n> B) : authO A -n> authO B :=
  OfeMor (auth_map f).
Time Lemma authO_map_ne A B : NonExpansive (@authO_map A B).
Time Proof.
Time
(intros n f f' Hf [[[]| ]]; repeat constructor; try naive_solver;
  apply agreeO_map_ne; auto).
Time Qed.
Time #[program]
Definition authRF (F : urFunctor) : rFunctor :=
  {|
  rFunctor_car := fun A _ B _ => authR (urFunctor_car F A B);
  rFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  authO_map (urFunctor_map F fg) |}.
Time Next Obligation.
Time
by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply authO_map_ne, urFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x).
Time rewrite /= -{+2}(auth_map_id x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply (auth_map_ext _ _) =>y;
  apply urFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -auth_map_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply (auth_map_ext _ _) =>y;
  apply urFunctor_compose).
Time Qed.
Time
Instance authRF_contractive  F:
 (urFunctorContractive F \226\134\146 rFunctorContractive (authRF F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply authO_map_ne, urFunctor_contractive.
Time Qed.
Time #[program]
Definition authURF (F : urFunctor) : urFunctor :=
  {|
  urFunctor_car := fun A _ B _ => authUR (urFunctor_car F A B);
  urFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                   authO_map (urFunctor_map F fg) |}.
Time Next Obligation.
Time
by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply authO_map_ne, urFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x).
Time rewrite /= -{+2}(auth_map_id x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply (auth_map_ext _ _) =>y;
  apply urFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -auth_map_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply (auth_map_ext _ _) =>y;
  apply urFunctor_compose).
Time Qed.
Time
Instance authURF_contractive  F:
 (urFunctorContractive F \226\134\146 urFunctorContractive (authURF F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply authO_map_ne, urFunctor_contractive.
Time Qed.

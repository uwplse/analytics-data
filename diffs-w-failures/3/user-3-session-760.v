Time From iris.algebra Require Export gmap coPset local_updates.
Time From stdpp Require Import namespaces.
Time From iris.algebra Require Import updates.
Time From iris.algebra Require Import proofmode_classes.
Time Set Default Proof Using "Type".
Time
Record namespace_map (A : Type) :=
 NamespaceMap {namespace_map_data_proj : gmap positive A;
               namespace_map_token_proj : coPset_disj}.
Time Add Printing Constructor namespace_map.
Time Arguments NamespaceMap {_} _ _.
Time Arguments namespace_map_data_proj {_} _.
Time Arguments namespace_map_token_proj {_} _.
Time Instance: (Params (@NamespaceMap) 1) := { }.
Time Instance: (Params (@namespace_map_data_proj) 1) := { }.
Time Instance: (Params (@namespace_map_token_proj) 1) := { }.
Time
Definition namespace_map_data {A : cmraT} (N : namespace) 
  (a : A) : namespace_map A := NamespaceMap {[positives_flatten N := a]} \206\181.
Time
Definition namespace_map_token {A : cmraT} (E : coPset) : 
  namespace_map A := NamespaceMap \226\136\133 (CoPset E).
Time Instance: (Params (@namespace_map_data) 2) := { }.
Time Section ofe.
Time Context {A : ofeT}.
Time Implicit Types x y : namespace_map A.
Time
Instance namespace_map_equiv : (Equiv (namespace_map A)) :=
 (\206\187 x y,
    namespace_map_data_proj x \226\137\161 namespace_map_data_proj y
    \226\136\167 namespace_map_token_proj x = namespace_map_token_proj y).
Time
Instance namespace_map_dist : (Dist (namespace_map A)) :=
 (\206\187 n x y,
    namespace_map_data_proj x \226\137\161{n}\226\137\161 namespace_map_data_proj y
    \226\136\167 namespace_map_token_proj x = namespace_map_token_proj y).
Time #[global]Instance Awesome_ne : (NonExpansive2 (@NamespaceMap A)).
Time Proof.
Time by split.
Time Qed.
Time #[global]
Instance Awesome_proper : (Proper ((\226\137\161) ==> (=) ==> (\226\137\161)) (@NamespaceMap A)).
Time Proof.
Time by split.
Time Qed.
Time #[global]
Instance namespace_map_data_proj_ne :
 (NonExpansive (@namespace_map_data_proj A)).
Time Proof.
Time by destruct 1.
Time Qed.
Time #[global]
Instance namespace_map_data_proj_proper :
 (Proper ((\226\137\161) ==> (\226\137\161)) (@namespace_map_data_proj A)).
Time Proof.
Time by destruct 1.
Time Qed.
Time Definition namespace_map_ofe_mixin : OfeMixin (namespace_map A).
Time Proof.
Time
by
 apply
  (iso_ofe_mixin
     (\206\187 x, (namespace_map_data_proj x, namespace_map_token_proj x))).
Time Qed.
Time
Canonical Structure namespace_mapC :=
  OfeT (namespace_map A) namespace_map_ofe_mixin.
Time #[global]
Instance NamespaceMap_discrete  a b:
 (Discrete a \226\134\146 Discrete b \226\134\146 Discrete (NamespaceMap a b)).
Time Proof.
Time (intros ? ? [? ?] [? ?]; split; unfold_leibniz; by eapply discrete).
Time Qed.
Time #[global]
Instance namespace_map_ofe_discrete :
 (OfeDiscrete A \226\134\146 OfeDiscrete namespace_mapC).
Time Proof.
Time (intros ? [? ?]; apply _).
Time Qed.
Time End ofe.
Time Arguments namespace_mapC : clear implicits.
Time Section cmra.
Time Context {A : cmraT}.
Time Implicit Types a b : A.
Time Implicit Types x y : namespace_map A.
Time #[global]
Instance namespace_map_data_ne  i: (NonExpansive (@namespace_map_data A i)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance namespace_map_data_proper  N:
 (Proper ((\226\137\161) ==> (\226\137\161)) (@namespace_map_data A N)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance namespace_map_data_discrete  N a:
 (Discrete a \226\134\146 Discrete (namespace_map_data N a)).
Time Proof.
Time (intros).
Time (apply NamespaceMap_discrete; apply _).
Time Qed.
Time #[global]
Instance namespace_map_token_discrete  E:
 (Discrete (@namespace_map_token A E)).
Time Proof.
Time (intros).
Time (apply NamespaceMap_discrete; apply _).
Time Qed.
Time
Instance namespace_map_valid : (Valid (namespace_map A)) :=
 (\206\187 x,
    match namespace_map_token_proj x with
    | CoPset E =>
        \226\156\147 namespace_map_data_proj x
        \226\136\167 (\226\136\128 i, namespace_map_data_proj x !! i = None \226\136\168 i \226\136\137 E)
    | CoPsetBot => False
    end).
Time #[global]Arguments namespace_map_valid !_ /.
Time
Instance namespace_map_validN : (ValidN (namespace_map A)) :=
 (\206\187 n x,
    match namespace_map_token_proj x with
    | CoPset E =>
        \226\156\147{n} namespace_map_data_proj x
        \226\136\167 (\226\136\128 i, namespace_map_data_proj x !! i = None \226\136\168 i \226\136\137 E)
    | CoPsetBot => False
    end).
Time #[global]Arguments namespace_map_validN !_ /.
Time
Instance namespace_map_pcore : (PCore (namespace_map A)) :=
 (\206\187 x, Some (NamespaceMap (core (namespace_map_data_proj x)) \206\181)).
Time
Instance namespace_map_op : (Op (namespace_map A)) :=
 (\206\187 x y,
    NamespaceMap (namespace_map_data_proj x \226\139\133 namespace_map_data_proj y)
      (namespace_map_token_proj x \226\139\133 namespace_map_token_proj y)).
Time
Definition namespace_map_valid_eq :
  valid =
  (\206\187 x,
     match namespace_map_token_proj x with
     | CoPset E =>
         \226\156\147 namespace_map_data_proj x
         \226\136\167 (\226\136\128 i, namespace_map_data_proj x !! i = None \226\136\168 i \226\136\137 E)
     | CoPsetBot => False
     end) := eq_refl _.
Time
Definition namespace_map_validN_eq :
  validN =
  (\206\187 n x,
     match namespace_map_token_proj x with
     | CoPset E =>
         \226\156\147{n} namespace_map_data_proj x
         \226\136\167 (\226\136\128 i, namespace_map_data_proj x !! i = None \226\136\168 i \226\136\137 E)
     | CoPsetBot => False
     end) := eq_refl _.
Time
Lemma namespace_map_included x y :
  x \226\137\188 y
  \226\134\148 namespace_map_data_proj x \226\137\188 namespace_map_data_proj y
    \226\136\167 namespace_map_token_proj x \226\137\188 namespace_map_token_proj y.
Time Proof.
Time
(split;
  [ intros [[z1 z2] Hz]; split; [ exists z1 | exists z2 ]; apply Hz |  ]).
Time (intros [[z1 Hz1] [z2 Hz2]]; exists (NamespaceMap z1 z2); split; auto).
Time Qed.
Time
Lemma namespace_map_data_proj_validN n x :
  \226\156\147{n} x \226\134\146 \226\156\147{n} namespace_map_data_proj x.
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> destruct x as [? [?| ]] =>// - [? ?].
Time Qed.
Time
Lemma namespace_map_token_proj_validN n x :
  \226\156\147{n} x \226\134\146 \226\156\147{n} namespace_map_token_proj x.
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> destruct x as [? [?| ]] =>// - [? ?].
Time Qed.
Time Lemma namespace_map_cmra_mixin : CmraMixin (namespace_map A).
Time Proof.
Time (apply cmra_total_mixin).
Time -
Time eauto.
Time -
Time by intros n x y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
Time -
Time solve_proper.
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> intros n [m1 [E1| ]] [m2 [E2| ]] [Hm ?]
  =>// - [? ?]; split; simplify_eq /=).
Time +
Time by rewrite -Hm.
Time +
Time (intros i).
Time by rewrite -(dist_None n) -Hm dist_None.
Time -
Time
(intros [m [E| ]]; rewrite namespace_map_valid_eq namespace_map_validN_eq /=
  ?cmra_valid_validN; naive_solver eauto using 0).
Time -
Time
(intros n [m [E| ]]; rewrite namespace_map_validN_eq /=; naive_solver eauto
  using cmra_validN_S).
Time -
Time (split; simpl; [ by rewrite assoc | by rewrite assoc_L ]).
Time -
Time (split; simpl; [ by rewrite comm | by rewrite comm_L ]).
Time -
Time (split; simpl; [ by rewrite cmra_core_l | by rewrite left_id_L ]).
Time -
Time (split; simpl; [ by rewrite cmra_core_idemp | done ]).
Time -
Time (intros ? ?; rewrite !namespace_map_included; intros [? ?]).
Time by split; simpl; apply : {}cmra_core_mono {}.
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> intros n [m1 [E1| ]] [m2 [E2| ]] =>//=;
  rewrite namespace_map_validN_eq /=).
Time rewrite {+1}/op /cmra_op /=.
Time (<ssreflect_plugin::ssrtclseq@0> case_decide ; last  done).
Time
(<ssreflect_plugin::ssrtclseq@0> intros [Hm Hdisj]; split ; first  by eauto
 using cmra_validN_op_l).
Time (intros i).
Time move : {}(Hdisj i) {}.
Time rewrite lookup_op.
Time
(<ssreflect_plugin::ssrtclseq@0> case : {}(m1 !! i) {} =>[a|] ; last  auto).
Time move  {}=>[].
Time by case : {}(m2 !! i) {}.
Time set_solver.
Time -
Time (intros n x y1 y2 ? [? ?]; simpl in *).
Time
(destruct
  (cmra_extend n (namespace_map_data_proj x) (namespace_map_data_proj y1)
     (namespace_map_data_proj y2)) as (m1, (m2, (?, (?, ?)))); auto
  using namespace_map_data_proj_validN).
Time
(destruct
  (cmra_extend n (namespace_map_token_proj x) (namespace_map_token_proj y1)
     (namespace_map_token_proj y2)) as (E1, (E2, (?, (?, ?)))); auto
  using namespace_map_token_proj_validN).
Time by exists (NamespaceMap m1 E1),(NamespaceMap m2 E2).
Time Qed.
Time
Canonical Structure namespace_mapR :=
  CmraT (namespace_map A) namespace_map_cmra_mixin.
Time #[global]
Instance namespace_map_cmra_discrete :
 (CmraDiscrete A \226\134\146 CmraDiscrete namespace_mapR).
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  apply _).
Time
(intros [m [E| ]]; rewrite namespace_map_validN_eq namespace_map_valid_eq //=).
Time naive_solver eauto using (cmra_discrete_valid m).
Time Qed.
Time
Instance namespace_map_empty : (Unit (namespace_map A)) := (NamespaceMap \206\181 \206\181).
Time Lemma namespace_map_ucmra_mixin : UcmraMixin (namespace_map A).
Time Proof.
Time (split; simpl).
Time -
Time rewrite namespace_map_valid_eq /=.
Time split.
Time (apply ucmra_unit_valid).
Time set_solver.
Time -
Time (split; simpl; [ by rewrite left_id | by rewrite left_id_L ]).
Time -
Time (do 2 constructor; [ apply (core_id_core _) | done ]).
Time Qed.
Time
Canonical Structure namespace_mapUR :=
  UcmraT (namespace_map A) namespace_map_ucmra_mixin.
Time #[global]
Instance namespace_map_data_core_id  N a:
 (CoreId a \226\134\146 CoreId (namespace_map_data N a)).
Time Proof.
Time (do 2 constructor; simpl; auto).
Time (apply core_id_core, _).
Time Qed.
Time Lemma namespace_map_data_valid N a : \226\156\147 namespace_map_data N a \226\134\148 \226\156\147 a.
Time Proof.
Time rewrite namespace_map_valid_eq /= singleton_valid.
Time set_solver.
Time Qed.
Time Lemma namespace_map_token_valid E : \226\156\147 namespace_map_token E.
Time Proof.
Time rewrite namespace_map_valid_eq /=.
Time split.
Time done.
Time by left.
Time Qed.
Time
Lemma namespace_map_data_op N a b :
  namespace_map_data N (a \226\139\133 b) =
  namespace_map_data N a \226\139\133 namespace_map_data N b.
Time Proof.
Time
by rewrite {+2}/op /namespace_map_op /namespace_map_data /= -op_singleton
 left_id_L.
Time Qed.
Time
Lemma namespace_map_data_mono N a b :
  a \226\137\188 b \226\134\146 namespace_map_data N a \226\137\188 namespace_map_data N b.
Time Proof.
Time (intros [c ->]).
Time rewrite namespace_map_data_op.
Time (apply cmra_included_l).
Time Qed.
Time #[global]
Instance is_op_namespace_map_data  N a b1 b2:
 (IsOp a b1 b2
  \226\134\146 IsOp' (namespace_map_data N a) (namespace_map_data N b1)
      (namespace_map_data N b2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsOp' /IsOp =>{+}->).
Time by rewrite namespace_map_data_op.
Time Qed.
Time
Lemma namespace_map_token_union E1 E2 :
  E1 ## E2
  \226\134\146 namespace_map_token (E1 \226\136\170 E2) =
    namespace_map_token E1 \226\139\133 namespace_map_token E2.
Time Proof.
Time (intros).
Time
by rewrite /op /namespace_map_op /namespace_map_token /= coPset_disj_union //
 left_id_L.
Time Qed.
Time
Lemma namespace_map_token_difference E1 E2 :
  E1 \226\138\134 E2
  \226\134\146 namespace_map_token E2 =
    namespace_map_token E1 \226\139\133 namespace_map_token (E2 \226\136\150 E1).
Time Proof.
Time (intros).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite -namespace_map_token_union ; last 
 set_solver).
Time by rewrite -union_difference_L.
Time Qed.
Time
Lemma namespace_map_token_valid_op E1 E2 :
  \226\156\147 (namespace_map_token E1 \226\139\133 namespace_map_token E2) \226\134\148 E1 ## E2.
Time Proof.
Time rewrite namespace_map_valid_eq /= {+1}/op /cmra_op /=.
Time (<ssreflect_plugin::ssrtclseq@0> case_decide ; last  done).
Time (split; [ done |  ]; intros _).
Time split.
Time -
Time by rewrite left_id.
Time -
Time (intros i).
Time rewrite lookup_op lookup_empty.
Time auto.
Time Qed.
Time
Lemma namespace_map_alloc_update E N a :
  \226\134\145N \226\138\134 E \226\134\146 \226\156\147 a \226\134\146 namespace_map_token E ~~> namespace_map_data N a.
Time Proof.
Time (assert (positives_flatten N \226\136\136 (\226\134\145N : coPset))).
Time {
Time rewrite nclose_eq.
Time (apply elem_coPset_suffixes).
Time exists 1%positive.
Time by rewrite left_id_L.
Time }
Time (intros ? ?).
Time
(<ssreflect_plugin::ssrtclintros@0> apply cmra_total_update =>n 
 [mf [Ef|]] //).
Time rewrite namespace_map_validN_eq /= {+1}/op /cmra_op /=.
Time (<ssreflect_plugin::ssrtclseq@0> case_decide ; last  done).
Time rewrite left_id_L {+1}left_id.
Time (intros [Hmf Hdisj]; split).
Time -
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (Hdisj (positives_flatten N)) as [Hmfi| ] ; last  set_solver).
Time move : {}Hmfi {}.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite lookup_op lookup_empty left_id_L
 =>Hmfi).
Time (intros j).
Time rewrite lookup_op.
Time (destruct (decide (positives_flatten N = j)) as [<-| ]).
Time +
Time rewrite Hmfi lookup_singleton right_id_L.
Time by apply cmra_valid_validN.
Time +
Time by rewrite lookup_singleton_ne // left_id_L.
Time -
Time (intros j).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (decide (positives_flatten N = j))
 ; first  set_solver).
Time rewrite lookup_op lookup_singleton_ne //.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (Hdisj j) as [Hmfi| ?] ; last 
 set_solver).
Time move : {}Hmfi {}.
Time (rewrite lookup_op lookup_empty; auto).
Time Qed.
Time
Lemma namespace_map_updateP P (Q : namespace_map A \226\134\146 Prop) 
  N a :
  a ~~>: P
  \226\134\146 (\226\136\128 a', P a' \226\134\146 Q (namespace_map_data N a'))
    \226\134\146 namespace_map_data N a ~~>: Q.
Time Proof.
Time (intros Hup HP).
Time
(<ssreflect_plugin::ssrtclintros@0> apply cmra_total_updateP =>n 
 [mf [Ef|]] //).
Time rewrite namespace_map_validN_eq /= left_id_L.
Time (intros [Hmf Hdisj]).
Time (destruct (Hup n (mf !! positives_flatten N)) as (a', (?, ?))).
Time {
Time move : {}(Hmf (positives_flatten N)) {}.
Time by rewrite lookup_op lookup_singleton Some_op_opM.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> exists (namespace_map_data N a'); split ;
 first  by eauto).
Time rewrite /= left_id_L.
Time split.
Time -
Time (intros j).
Time (destruct (decide (positives_flatten N = j)) as [<-| ]).
Time +
Time by rewrite lookup_op lookup_singleton Some_op_opM.
Time +
Time rewrite lookup_op lookup_singleton_ne // left_id_L.
Time move : {}(Hmf j) {}.
Time rewrite lookup_op.
Time eauto using cmra_validN_op_r.
Time -
Time (intros j).
Time move : {}(Hdisj j) {}.
Time rewrite !lookup_op !op_None !lookup_singleton_None.
Time naive_solver.
Time Qed.
Time
Lemma namespace_map_update N a b :
  a ~~> b \226\134\146 namespace_map_data N a ~~> namespace_map_data N b.
Time Proof.
Time rewrite !cmra_update_updateP.
Time eauto using namespace_map_updateP with subst.
Time Qed.
Time End cmra.
Time Arguments namespace_mapR : clear implicits.
Time Arguments namespace_mapUR : clear implicits.

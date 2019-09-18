Time From iris.algebra Require Export cmra.
Time From stdpp Require Export list.
Time From iris.base_logic Require Import base_logic.
Time From iris.algebra Require Import updates local_updates.
Time Set Default Proof Using "Type".
Time Section cofe.
Time Context {A : ofeT}.
Time Implicit Type l : list A.
Time Instance list_dist : (Dist (list A)) := (\206\187 n, Forall2 (dist n)).
Time
Lemma list_dist_lookup n l1 l2 : l1 \226\137\161{n}\226\137\161 l2 \226\134\148 (\226\136\128 i, l1 !! i \226\137\161{n}\226\137\161 l2 !! i).
Time Proof.
Time setoid_rewrite dist_option_Forall2.
Time (apply Forall2_lookup).
Time Qed.
Time #[global]Instance cons_ne : (NonExpansive2 (@cons A)) := _.
Time #[global]Instance app_ne : (NonExpansive2 (@app A)) := _.
Time #[global]
Instance length_ne  n: (Proper (dist n ==> (=)) (@length A)) := _.
Time #[global]Instance tail_ne : (NonExpansive (@tail A)) := _.
Time #[global]Instance take_ne : (NonExpansive (@take A n)) := _.
Time #[global]Instance drop_ne : (NonExpansive (@drop A n)) := _.
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
Time #[global]
Instance list_inserts_ne  i: (NonExpansive2 (@list_inserts A i)) := _.
Time #[global]
Instance list_delete_ne  i: (NonExpansive (delete (M:=list A) i)) := _.
Time #[global]Instance option_list_ne : (NonExpansive (@option_list A)).
Time Proof.
Time (intros ? ? ? ?; by apply Forall2_option_list, dist_option_Forall2).
Time Qed.
Time #[global]
Instance list_filter_ne  n P `{\226\136\128 x, Decision (P x)}:
 (Proper (dist n ==> iff) P
  \226\134\146 Proper (dist n ==> dist n) (filter (B:=list A) P)) := _.
Time #[global]Instance replicate_ne : (NonExpansive (@replicate A n)) := _.
Time #[global]Instance reverse_ne : (NonExpansive (@reverse A)) := _.
Time #[global]Instance last_ne : (NonExpansive (@last A)).
Time Proof.
Time (intros ? ? ? ?; by apply dist_option_Forall2, Forall2_last).
Time Qed.
Time #[global]Instance resize_ne  n: (NonExpansive2 (@resize A n)) := _.
Time
Lemma list_dist_cons_inv_l n x l k :
  x :: l \226\137\161{n}\226\137\161 k \226\134\146 \226\136\131 y k', x \226\137\161{n}\226\137\161 y \226\136\167 l \226\137\161{n}\226\137\161 k' \226\136\167 k = y :: k'.
Time Proof.
Time (apply Forall2_cons_inv_l).
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
Time -
Time rewrite /dist /list_dist.
Time eauto using Forall2_impl, dist_S.
Time Qed.
Time Canonical Structure listO := OfeT (list A) list_ofe_mixin.
Time
Fixpoint list_compl_go `{!Cofe A} (c0 : list A) (c : chain listO) : listO :=
  match c0 with
  | [] => []
  | x :: c0 =>
      compl (chain_map (default x \226\136\152 head) c)
      :: list_compl_go c0 (chain_map tail c)
  end.
Time #[global, program]
Instance list_cofe  `{!Cofe A}: (Cofe listO) :=
 {| compl := fun c => list_compl_go (c 0) c |}.
Time Next Obligation.
Time (intros ? n c; rewrite /compl).
Time (assert (Hc0 : c 0 \226\137\161{0}\226\137\161 c n) by (symmetry; apply chain_cauchy; lia)).
Time revert Hc0.
Time (<ssreflect_plugin::ssrtclintros@0> generalize (c 0) =>c0).
Time revert c.
Time
(<ssreflect_plugin::ssrtclintros@0> induction c0 as [| x c0 IH] =>c Hc0 /=).
Time {
Time by inversion Hc0.
Time }
Time (apply list_dist_cons_inv_l in Hc0 as (x', (xs', (Hx, (Hc0, Hcn))))).
Time rewrite Hcn.
Time f_equiv.
Time -
Time by rewrite conv_compl /= Hcn /=.
Time -
Time rewrite IH /= ?Hcn //.
Time Qed.
Time #[global]
Instance list_ofe_discrete : (OfeDiscrete A \226\134\146 OfeDiscrete listO).
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
Time Qed.
Time End cofe.
Time Arguments listO : clear implicits.
Time
Lemma list_fmap_ext_ne {A} {B : ofeT} (f g : A \226\134\146 B) 
  (l : list A) n : (\226\136\128 x, f x \226\137\161{n}\226\137\161 g x) \226\134\146 f <$> l \226\137\161{n}\226\137\161 g <$> l.
Time Proof.
Time (intros Hf).
Time by apply Forall2_fmap, Forall_Forall2, Forall_true.
Time Qed.
Time
Instance list_fmap_ne  {A B : ofeT} (f : A \226\134\146 B) n:
 (Proper (dist n ==> dist n) f
  \226\134\146 Proper (dist n ==> dist n) (fmap (M:=list) f)).
Time Proof.
Time (intros Hf l k ?; by eapply Forall2_fmap, Forall2_impl; eauto).
Time Qed.
Time
Definition listO_map {A} {B} (f : A -n> B) : listO A -n> listO B :=
  OfeMor (fmap f : listO A \226\134\146 listO B).
Time Instance listO_map_ne  A B: (NonExpansive (@listO_map A B)).
Time Proof.
Time (intros n f g ? l).
Time by apply list_fmap_ext_ne.
Time Qed.
Time #[program]
Definition listOF (F : oFunctor) : oFunctor :=
  {|
  oFunctor_car := fun A _ B _ => listO (oFunctor_car F A B);
  oFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg => listO_map (oFunctor_map F fg) |}.
Time Next Obligation.
Time
by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply listO_map_ne, oFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x).
Time rewrite /= -{+2}(list_fmap_id x).
Time (<ssreflect_plugin::ssrtclintros@0> apply list_fmap_equiv_ext =>y).
Time (apply oFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -list_fmap_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply list_fmap_equiv_ext =>y;
  apply oFunctor_compose).
Time Qed.
Time
Instance listOF_contractive  F:
 (oFunctorContractive F \226\134\146 oFunctorContractive (listOF F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply listO_map_ne, oFunctor_contractive.
Time Qed.
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
Time (intros Hl i).
Time by destruct (l !! i) as [x| ] eqn:?; [ apply (Hl i) |  ].
Time -
Time (intros Hl i x Hi).
Time (move : {}(Hl i) {}; by rewrite Hi).
Time Qed.
Time Lemma list_lookup_validN n l : \226\156\147{n} l \226\134\148 (\226\136\128 i, \226\156\147{n} (l !! i)).
Time Proof.
Time (rewrite {+1}/validN /list_validN Forall_lookup; split).
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
Time Definition list_cmra_mixin : CmraMixin (list A).
Time Proof.
Time (apply cmra_total_mixin).
Time -
Time eauto.
Time -
Time
(intros n l l1 l2; <ssreflect_plugin::ssrtclintros@0> rewrite
  !list_dist_lookup =>Hl i).
Time by rewrite !list_lookup_op Hl.
Time -
Time (intros n l1 l2 Hl; by rewrite /core /= Hl).
Time -
Time
(intros n l1 l2; <ssreflect_plugin::ssrtclintros@0> rewrite !list_dist_lookup
  !list_lookup_validN =>Hl ? i).
Time by rewrite -Hl.
Time -
Time (intros l).
Time rewrite list_lookup_valid.
Time setoid_rewrite list_lookup_validN.
Time setoid_rewrite cmra_valid_validN.
Time naive_solver.
Time -
Time (intros n x).
Time rewrite !list_lookup_validN.
Time auto using cmra_validN_S.
Time -
Time
(intros l1 l2 l3; <ssreflect_plugin::ssrtclintros@0> rewrite
  list_equiv_lookup =>i).
Time by rewrite !list_lookup_op assoc.
Time -
Time
(intros l1 l2; <ssreflect_plugin::ssrtclintros@0> rewrite list_equiv_lookup
  =>i).
Time by rewrite !list_lookup_op comm.
Time -
Time
(intros l; <ssreflect_plugin::ssrtclintros@0> rewrite list_equiv_lookup =>i).
Time by rewrite list_lookup_op list_lookup_core cmra_core_l.
Time -
Time
(intros l; <ssreflect_plugin::ssrtclintros@0> rewrite list_equiv_lookup =>i).
Time by rewrite !list_lookup_core cmra_core_idemp.
Time -
Time
(intros l1 l2; <ssreflect_plugin::ssrtclintros@0> rewrite
  !list_lookup_included =>Hl i).
Time rewrite !list_lookup_core.
Time by apply cmra_core_mono.
Time -
Time (intros n l1 l2).
Time rewrite !list_lookup_validN.
Time setoid_rewrite list_lookup_op.
Time eauto using cmra_validN_op_l.
Time -
Time (intros n l).
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>- 
  [|y1 l1] [|y2 l2] Hl Heq; try by exfalso; inversion Heq).
Time +
Time by exists [],[].
Time +
Time (exists [],(x :: l); inversion Heq; by repeat constructor).
Time +
Time (exists (x :: l),[]; inversion Heq; by repeat constructor).
Time +
Time
(destruct (IH l1 l2) as (l1', (l2', (?, (?, ?)))), 
  (cmra_extend n x y1 y2) as (y1', (y2', (?, (?, ?))));
  [ by inversion_clear Heq; inversion_clear Hl.. | idtac ]).
Time (exists (y1' :: l1'),(y2' :: l2'); repeat constructor; auto).
Time Qed.
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
Time by apply cmra_discrete_valid.
Time Qed.
Time #[global]Instance list_core_id  l: ((\226\136\128 x : A, CoreId x) \226\134\146 CoreId l).
Time Proof.
Time
(intros ?; constructor; <ssreflect_plugin::ssrtclintros@0>
  apply list_equiv_lookup =>i).
Time by rewrite list_lookup_core (core_id_core (l !! i)).
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
Time Qed.
Time #[global]Instance list_op_nil_l : (LeftId (=) (@nil A) op).
Time Proof.
Time done.
Time Qed.
Time #[global]Instance list_op_nil_r : (RightId (=) (@nil A) op).
Time Proof.
Time by intros [].
Time Qed.
Time
Lemma list_op_app l1 l2 l3 :
  (l1 ++ l3) \226\139\133 l2 = l1 \226\139\133 take (length l1) l2 ++ l3 \226\139\133 drop (length l1) l2.
Time Proof.
Time revert l2 l3.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l1 as [| x1 l1] =>- 
  [|x2 l2] [|x3 l3]; f_equal /=; auto).
Time Qed.
Time
Lemma list_op_app_le l1 l2 l3 :
  length l2 \226\137\164 length l1 \226\134\146 (l1 ++ l3) \226\139\133 l2 = l1 \226\139\133 l2 ++ l3.
Time Proof.
Time (intros ?).
Time by rewrite list_op_app take_ge // drop_ge // right_id_L.
Time Qed.
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
Time naive_solver.
Time Qed.
Time Lemma list_lookup_singletonM i x : ({[i := x]} : list A) !! i = Some x.
Time Proof.
Time (induction i; by f_equal /=).
Time Qed.
Time
Lemma list_lookup_singletonM_ne i j x :
  i \226\137\160 j
  \226\134\146 ({[i := x]} : list A) !! j = None \226\136\168 ({[i := x]} : list A) !! j = Some \206\181.
Time Proof.
Time (revert j; induction i; intros [| j]; naive_solver auto with lia).
Time Qed.
Time
Lemma list_singletonM_validN n i x : \226\156\147{n} ({[i := x]} : list A) \226\134\148 \226\156\147{n} x.
Time Proof.
Time rewrite list_lookup_validN.
Time split.
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
Time Qed.
Time Lemma list_singleton_valid i x : \226\156\147 ({[i := x]} : list A) \226\134\148 \226\156\147 x.
Time Proof.
Time rewrite !cmra_valid_validN.
Time by setoid_rewrite list_singletonM_validN.
Time Qed.
Time Lemma list_singletonM_length i x : length {[i := x]} = S i.
Time Proof.
Time
(rewrite /singletonM /list_singletonM app_length replicate_length /=; lia).
Time Qed.
Time
Lemma list_core_singletonM i (x : A) : core {[i := x]} \226\137\161 {[i := core x]}.
Time Proof.
Time rewrite /singletonM /list_singletonM.
Time by rewrite {+1}/core /= fmap_app fmap_replicate (core_id_core \226\136\133).
Time Qed.
Time
Lemma list_op_singletonM i (x y : A) :
  {[i := x]} \226\139\133 {[i := y]} \226\137\161 {[i := x \226\139\133 y]}.
Time Proof.
Time rewrite /singletonM /list_singletonM /=.
Time (induction i; constructor; rewrite ?left_id; auto).
Time Qed.
Time
Lemma list_alter_singletonM f i x :
  alter f i ({[i := x]} : list A) = {[i := f x]}.
Time Proof.
Time rewrite /singletonM /list_singletonM /=.
Time (induction i; f_equal /=; auto).
Time Qed.
Time #[global]
Instance list_singleton_core_id  i (x : A): (CoreId x \226\134\146 CoreId {[i := x]}).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite !core_id_total
 list_core_singletonM =>{+}->.
Time Qed.
Time Lemma list_singleton_snoc l x : {[length l := x]} \226\139\133 l \226\137\161 l ++ [x].
Time Proof.
Time elim : {}l {} =>//= ? ? {+}<-.
Time by rewrite left_id.
Time Qed.
Time
Lemma list_singleton_updateP (P : A \226\134\146 Prop) (Q : list A \226\134\146 Prop) 
  x : x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q [y]) \226\134\146 [x] ~~>: Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite !cmra_total_updateP =>Hup HQ n lf
 /list_lookup_validN Hv).
Time (destruct (Hup n (default \206\181 (lf !! 0))) as (y, (?, Hv'))).
Time {
Time move : {}(Hv 0) {}.
Time by destruct lf; rewrite /= ?right_id.
Time }
Time (<ssreflect_plugin::ssrtclseq@0> exists [y]; split ; first  by auto).
Time (<ssreflect_plugin::ssrtclintros@0> apply list_lookup_validN =>i).
Time move : {}(Hv i) {}Hv' {}.
Time by destruct i, lf; rewrite /= ?right_id.
Time Qed.
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
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite list_op_app app_validN =>- [? ?]).
Time (destruct (Hup1 n (take (length l1) lf)) as (k1, (?, ?)); auto).
Time (destruct (Hup2 n (drop (length l1) lf)) as (k2, (?, ?)); auto).
Time exists (k1 ++ k2).
Time rewrite list_op_app app_validN.
Time by destruct (HQ k1 k2) as [<- ?].
Time Qed.
Time
Lemma app_update l1 l2 k1 k2 :
  length l1 = length k1 \226\134\146 l1 ~~> k1 \226\134\146 l2 ~~> k2 \226\134\146 l1 ++ l2 ~~> k1 ++ k2.
Time Proof.
Time (rewrite !cmra_update_updateP; eauto using app_updateP with subst).
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
Time Qed.
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
Time -
Time naive_solver.
Time Qed.
Time
Lemma list_middle_update l1 l2 x y :
  x ~~> y \226\134\146 l1 ++ x :: l2 ~~> l1 ++ y :: l2.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite !cmra_update_updateP =>?; eauto
  using list_middle_updateP with subst).
Time Qed.
Time
Lemma list_alloc_singleton_local_update x l :
  \226\156\147 x \226\134\146 (l, \206\181) ~l~> (l ++ [x], {[length l := x]}).
Time Proof.
Time move  {}=>?.
Time
have {+}->: {[length l := x]} \226\137\161 {[length l := x]} \226\139\133 \206\181by rewrite right_id.
Time rewrite -list_singleton_snoc.
Time (<ssreflect_plugin::ssrtclintros@0> apply op_local_update =>? ?).
Time rewrite list_singleton_snoc app_validN cons_validN.
Time
(<ssreflect_plugin::ssrtclintros@0> split_and ? =>//; [  | constructor ]).
Time by apply cmra_valid_validN.
Time Qed.
Time End properties.
Time
Instance list_fmap_cmra_morphism  {A B : ucmraT} (f : A \226\134\146 B)
 `{!CmraMorphism f}: (CmraMorphism (fmap f : list A \226\134\146 list B)).
Time Proof.
Time (split; try apply _).
Time -
Time (intros n l).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite !list_lookup_validN =>Hl i).
Time rewrite list_lookup_fmap.
Time by apply (cmra_morphism_validN (fmap f : option A \226\134\146 option B)).
Time -
Time (intros l).
Time (apply Some_proper).
Time rewrite -!list_fmap_compose.
Time (apply list_fmap_equiv_ext, cmra_morphism_core, _).
Time -
Time (intros l1 l2).
Time (<ssreflect_plugin::ssrtclintros@0> apply list_equiv_lookup =>i).
Time
by rewrite list_lookup_op !list_lookup_fmap list_lookup_op cmra_morphism_op.
Time Qed.
Time #[program]
Definition listURF (F : urFunctor) : urFunctor :=
  {|
  urFunctor_car := fun A _ B _ => listUR (urFunctor_car F A B);
  urFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                   listO_map (urFunctor_map F fg) |}.
Time Next Obligation.
Time
by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply listO_map_ne, urFunctor_ne.
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
  apply listO_map_ne, urFunctor_contractive.
Time Qed.

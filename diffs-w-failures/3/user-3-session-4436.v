Time From iris.algebra Require Export big_op.
Time From iris.bi Require Import derived_laws_sbi.
Time From stdpp Require Import countable fin_sets functions.
Time Set Default Proof Using "Type".
Time Import interface.bi derived_laws_bi.bi derived_laws_sbi.bi.
Time
Notation "'[\226\136\151' 'list]' k \226\134\166 x \226\136\136 l , P" := (big_opL bi_sep (\206\187 k x, P) l) :
  bi_scope.
Time
Notation "'[\226\136\151' 'list]' x \226\136\136 l , P" := (big_opL bi_sep (\206\187 _ x, P) l) : bi_scope.
Time Notation "'[\226\136\151]' Ps" := (big_opL bi_sep (\206\187 _ x, x) Ps) : bi_scope.
Time
Notation "'[\226\136\167' 'list]' k \226\134\166 x \226\136\136 l , P" := (big_opL bi_and (\206\187 k x, P) l) :
  bi_scope.
Time
Notation "'[\226\136\167' 'list]' x \226\136\136 l , P" := (big_opL bi_and (\206\187 _ x, P) l) : bi_scope.
Time Notation "'[\226\136\167]' Ps" := (big_opL bi_and (\206\187 _ x, x) Ps) : bi_scope.
Time
Notation "'[\226\136\168' 'list]' k \226\134\166 x \226\136\136 l , P" := (big_opL bi_or (\206\187 k x, P) l) :
  bi_scope.
Time
Notation "'[\226\136\168' 'list]' x \226\136\136 l , P" := (big_opL bi_or (\206\187 _ x, P) l) : bi_scope.
Time Notation "'[\226\136\168]' Ps" := (big_opL bi_or (\206\187 _ x, x) Ps) : bi_scope.
Time
Notation "'[\226\136\151' 'map]' k \226\134\166 x \226\136\136 m , P" := (big_opM bi_sep (\206\187 k x, P) m) :
  bi_scope.
Time
Notation "'[\226\136\151' 'map]' x \226\136\136 m , P" := (big_opM bi_sep (\206\187 _ x, P) m) : bi_scope.
Time
Notation "'[\226\136\151' 'set]' x \226\136\136 X , P" := (big_opS bi_sep (\206\187 x, P) X) : bi_scope.
Time
Notation "'[\226\136\151' 'mset]' x \226\136\136 X , P" := (big_opMS bi_sep (\206\187 x, P) X) : bi_scope.
Time
Fixpoint big_sepL2 {PROP : bi} {A B} (\206\166 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP) 
(l1 : list A) (l2 : list B) : PROP :=
  match l1, l2 with
  | [], [] => emp
  | x1 :: l1, x2 :: l2 => \206\166 0 x1 x2 \226\136\151 big_sepL2 (\206\187 n, \206\166 (S n)) l1 l2
  | _, _ => False
  end%I.
Time Instance: (Params (@big_sepL2) 3) := { }.
Time Arguments big_sepL2 {PROP} {A} {B} _ !_ !_ /.
Time Typeclasses Opaque big_sepL2.
Time
Notation "'[\226\136\151' 'list]' k \226\134\166 x1 ; x2 \226\136\136 l1 ; l2 , P" :=
  (big_sepL2 (\206\187 k x1 x2, P) l1 l2) : bi_scope.
Time
Notation "'[\226\136\151' 'list]' x1 ; x2 \226\136\136 l1 ; l2 , P" :=
  (big_sepL2 (\206\187 _ x1 x2, P) l1 l2) : bi_scope.
Time
Definition big_sepM2 {PROP : bi} `{Countable K} {A} 
  {B} (\206\166 : K \226\134\146 A \226\134\146 B \226\134\146 PROP) (m1 : gmap K A) (m2 : gmap K B) : PROP :=
  (\226\140\156\226\136\128 k, is_Some (m1 !! k) \226\134\148 is_Some (m2 !! k)\226\140\157
   \226\136\167 ([\226\136\151 map] k\226\134\166xy \226\136\136 map_zip m1 m2, \206\166 k xy.1 xy.2))%I.
Time Instance: (Params (@big_sepM2) 6) := { }.
Time Typeclasses Opaque big_sepM2.
Time
Notation "'[\226\136\151' 'map]' k \226\134\166 x1 ; x2 \226\136\136 m1 ; m2 , P" :=
  (big_sepM2 (\206\187 k x1 x2, P) m1 m2) : bi_scope.
Time
Notation "'[\226\136\151' 'map]' x1 ; x2 \226\136\136 m1 ; m2 , P" :=
  (big_sepM2 (\206\187 _ x1 x2, P) m1 m2) : bi_scope.
Time Section bi_big_op.
Time Context {PROP : bi}.
Time Implicit Types P Q : PROP.
Time Implicit Types Ps Qs : list PROP.
Time Implicit Type A : Type.
Time Section sep_list.
Time Context {A : Type}.
Time Implicit Type l : list A.
Time Implicit Types \206\166 \206\168 : nat \226\134\146 A \226\134\146 PROP.
Time Lemma big_sepL_nil \206\166 : ([\226\136\151 list] k\226\134\166y \226\136\136 nil, \206\166 k y) \226\138\163\226\138\162 emp.
Time Proof.
Time done.
Time Qed.
Time
Lemma big_sepL_nil' `{BiAffine PROP} P \206\166 : P \226\138\162 [\226\136\151 list] k\226\134\166y \226\136\136 nil, \206\166 k y.
Time Proof.
Time (apply (affine _)).
Time Qed.
Time
Lemma big_sepL_cons \206\166 x l :
  ([\226\136\151 list] k\226\134\166y \226\136\136 (x :: l), \206\166 k y) \226\138\163\226\138\162 \206\166 0 x \226\136\151 ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 (S k) y).
Time Proof.
Time by rewrite big_opL_cons.
Time Qed.
Time Lemma big_sepL_singleton \206\166 x : ([\226\136\151 list] k\226\134\166y \226\136\136 [x], \206\166 k y) \226\138\163\226\138\162 \206\166 0 x.
Time Proof.
Time by rewrite big_opL_singleton.
Time Qed.
Time
Lemma big_sepL_app \206\166 l1 l2 :
  ([\226\136\151 list] k\226\134\166y \226\136\136 (l1 ++ l2), \206\166 k y)
  \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166y \226\136\136 l1, \206\166 k y) \226\136\151 ([\226\136\151 list] k\226\134\166y \226\136\136 l2, \206\166 (length l1 + k) y).
Time Proof.
Time by rewrite big_opL_app.
Time Qed.
Time
Lemma big_sepL_mono \206\166 \206\168 l :
  (\226\136\128 k y, l !! k = Some y \226\134\146 \206\166 k y \226\138\162 \206\168 k y)
  \226\134\146 ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y) \226\138\162 [\226\136\151 list] k\226\134\166y \226\136\136 l, \206\168 k y.
Time Proof.
Time (apply big_opL_forall; apply _).
Time Qed.
Time
Lemma big_sepL_proper \206\166 \206\168 l :
  (\226\136\128 k y, l !! k = Some y \226\134\146 \206\166 k y \226\138\163\226\138\162 \206\168 k y)
  \226\134\146 ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y) \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\168 k y).
Time Proof.
Time (apply big_opL_proper).
Time Qed.
Time
Lemma big_sepL_submseteq `{BiAffine PROP} (\206\166 : A \226\134\146 PROP) 
  l1 l2 : l1 \226\138\134+ l2 \226\134\146 ([\226\136\151 list] y \226\136\136 l2, \206\166 y) \226\138\162 [\226\136\151 list] y \226\136\136 l1, \206\166 y.
Time Proof.
Time (intros [l ->]%submseteq_Permutation).
Time by rewrite big_sepL_app sep_elim_l.
Time Qed.
Time #[global]
Instance big_sepL_mono' :
 (Proper (pointwise_relation _ (pointwise_relation _ (\226\138\162)) ==> (=) ==> (\226\138\162))
    (big_opL (@bi_sep PROP) (A:=A))).
Time Proof.
Time (intros f g Hf m ? <-).
Time (apply big_opL_forall; apply _ || intros; apply Hf).
Time Qed.
Time #[global]
Instance big_sepL_id_mono' :
 (Proper (Forall2 (\226\138\162) ==> (\226\138\162)) (big_opL (@bi_sep PROP) (\206\187 _ P, P))).
Time Proof.
Time by induction 1 as [| P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH.
Time Qed.
Time Lemma big_sepL_emp l : ([\226\136\151 list] k\226\134\166y \226\136\136 l, emp) \226\138\163\226\138\162@{ PROP} emp.
Time Proof.
Time by rewrite big_opL_unit.
Time Qed.
Time
Lemma big_sepL_lookup_acc \206\166 l i x :
  l !! i = Some x
  \226\134\146 ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y) \226\138\162 \206\166 i x \226\136\151 (\206\166 i x -\226\136\151 [\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y).
Time Proof.
Time (intros Hli).
Time rewrite -(take_drop_middle l i x) // big_sepL_app /=.
Time
(rewrite Nat.add_0_r take_length_le; eauto
  using lookup_lt_Some, Nat.lt_le_incl).
Time rewrite assoc -!(comm _ (\206\166 _ _)) -assoc.
Time by apply sep_mono_r, wand_intro_l.
Time Qed.
Time
Lemma big_sepL_lookup \206\166 l i x `{!Absorbing (\206\166 i x)} :
  l !! i = Some x \226\134\146 ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y) \226\138\162 \206\166 i x.
Time Proof.
Time (intros).
Time rewrite big_sepL_lookup_acc //.
Time by rewrite sep_elim_l.
Time Qed.
Time
Lemma big_sepL_elem_of (\206\166 : A \226\134\146 PROP) l x `{!Absorbing (\206\166 x)} :
  x \226\136\136 l \226\134\146 ([\226\136\151 list] y \226\136\136 l, \206\166 y) \226\138\162 \206\166 x.
Time Proof.
Time
(intros [i ?]%elem_of_list_lookup; eauto using (big_sepL_lookup (\206\187 _, \206\166))).
Time Qed.
Time
Lemma big_sepL_fmap {B} (f : A \226\134\146 B) (\206\166 : nat \226\134\146 B \226\134\146 PROP) 
  l : ([\226\136\151 list] k\226\134\166y \226\136\136 (f <$> l), \206\166 k y) \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k (f y)).
Time Proof.
Time by rewrite big_opL_fmap.
Time Qed.
Time
Lemma big_sepL_bind {B} (f : A \226\134\146 list B) (\206\166 : B \226\134\146 PROP) 
  l : ([\226\136\151 list] y \226\136\136 (l \226\137\171= f), \206\166 y) \226\138\163\226\138\162 ([\226\136\151 list] x \226\136\136 l, [\226\136\151 list] y \226\136\136 f x, \206\166 y).
Time Proof.
Time by rewrite big_opL_bind.
Time Qed.
Time
Lemma big_sepL_sep \206\166 \206\168 l :
  ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x \226\136\151 \206\168 k x)
  \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\136\151 ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\168 k x).
Time Proof.
Time by rewrite big_opL_op.
Time Qed.
Time
Lemma big_sepL_and \206\166 \206\168 l :
  ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x \226\136\167 \206\168 k x)
  \226\138\162 ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\136\167 ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\168 k x).
Time Proof.
Time auto using and_intro, big_sepL_mono, and_elim_l, and_elim_r.
Time Qed.
Time
Lemma big_sepL_persistently `{BiAffine PROP} \206\166 l :
  <pers> ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166x \226\136\136 l, <pers> \206\166 k x).
Time Proof.
Time (apply (big_opL_commute _)).
Time Qed.
Time
Lemma big_sepL_forall `{BiAffine PROP} \206\166 l :
  (\226\136\128 k x, Persistent (\206\166 k x))
  \226\134\146 ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\138\163\226\138\162 (\226\136\128 k x, \226\140\156l !! k = Some x\226\140\157 \226\134\146 \206\166 k x).
Time Proof.
Time (intros H\206\166).
Time (apply (anti_symm _)).
Time {
Time
(<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>k;
  <ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply impl_intro_l, pure_elim_l =>?; by
  apply : {}big_sepL_lookup {}).
Time }
Time revert \206\166 H\206\166.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>\206\166 H\206\166;
  [ by auto using big_sepL_nil' |  ]).
Time rewrite big_sepL_cons.
Time (rewrite -persistent_and_sep; apply and_intro).
Time -
Time by rewrite (forall_elim 0) (forall_elim x) pure_True // True_impl.
Time -
Time rewrite -IH.
Time
(<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>k; by rewrite
  (forall_elim (S k))).
Time Qed.
Time
Lemma big_sepL_impl \206\166 \206\168 l :
  ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x)
  -\226\136\151 \226\150\161 (\226\136\128 k x, \226\140\156l !! k = Some x\226\140\157 \226\134\146 \206\166 k x -\226\136\151 \206\168 k x) -\226\136\151 [\226\136\151 list] k\226\134\166x \226\136\136 l, \206\168 k x.
Time Proof.
Time (apply wand_intro_l).
Time revert \206\166 \206\168.
Time (<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>\206\166 \206\168 /=).
Time {
Time by rewrite sep_elim_r.
Time }
Time
rewrite intuitionistically_sep_dup -assoc [(\226\150\161 _ \226\136\151 _)%I]comm -!assoc assoc.
Time (apply sep_mono).
Time -
Time rewrite (forall_elim 0) (forall_elim x) pure_True // True_impl.
Time by rewrite intuitionistically_elim wand_elim_l.
Time -
Time rewrite comm -(IH (\206\166 \226\136\152 S) (\206\168 \226\136\152 S)) /=.
Time (apply sep_mono_l, affinely_mono, persistently_mono).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>k).
Time by rewrite (forall_elim (S k)).
Time Qed.
Time
Lemma big_sepL_delete \206\166 l i x :
  l !! i = Some x
  \226\134\146 ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y)
    \226\138\163\226\138\162 \206\166 i x \226\136\151 ([\226\136\151 list] k\226\134\166y \226\136\136 l, if decide (k = i) then emp else \206\166 k y).
Time Proof.
Time (intros).
Time rewrite -(take_drop_middle l i x) // !big_sepL_app /= Nat.add_0_r.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite take_length_le ; last  eauto
 using lookup_lt_Some, Nat.lt_le_incl).
Time rewrite decide_True // left_id.
Time rewrite assoc -!(comm _ (\206\166 _ _)) -assoc.
Time (do 2 f_equiv).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply big_sepL_proper =>k y Hk).
Time (apply lookup_lt_Some in Hk).
Time rewrite take_length in  {} Hk.
Time by <ssreflect_plugin::ssrtclseq@0> rewrite decide_False ; last  lia.
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply big_sepL_proper =>k y _).
Time by <ssreflect_plugin::ssrtclseq@0> rewrite decide_False ; last  lia.
Time Qed.
Time
Lemma big_sepL_delete' `{!BiAffine PROP} \206\166 l i x :
  l !! i = Some x
  \226\134\146 ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y) \226\138\163\226\138\162 \206\166 i x \226\136\151 ([\226\136\151 list] k\226\134\166y \226\136\136 l, \226\140\156k \226\137\160 i\226\140\157 \226\134\146 \206\166 k y).
Time Proof.
Time (intros).
Time rewrite big_sepL_delete //.
Time (<ssreflect_plugin::ssrtclintros@0> do 2 f_equiv =>k y).
Time rewrite -decide_emp.
Time by repeat case_decide.
Time Qed.
Time
Lemma big_sepL_replicate l P :
  [\226\136\151] replicate (length l) P \226\138\163\226\138\162 ([\226\136\151 list] y \226\136\136 l, P).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l] =>//=; by f_equiv).
Time Qed.
Time #[global]
Instance big_sepL_nil_persistent  \206\166: (Persistent ([\226\136\151 list] k\226\134\166x \226\136\136 [], \206\166 k x)).
Time Proof.
Time (simpl; apply _).
Time Qed.
Time #[global]
Instance big_sepL_persistent  \206\166 l:
 ((\226\136\128 k x, Persistent (\206\166 k x)) \226\134\146 Persistent ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x)).
Time Proof.
Time revert \206\166.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>\206\166 ? /=;
  apply _).
Time Qed.
Time #[global]
Instance big_sepL_persistent_id  Ps:
 (TCForall Persistent Ps \226\134\146 Persistent ([\226\136\151] Ps)).
Time Proof.
Time (induction 1; simpl; apply _).
Time Qed.
Time #[global]
Instance big_sepL_nil_affine  \206\166: (Affine ([\226\136\151 list] k\226\134\166x \226\136\136 [], \206\166 k x)).
Time Proof.
Time (simpl; apply _).
Time Qed.
Time #[global]
Instance big_sepL_affine  \206\166 l:
 ((\226\136\128 k x, Affine (\206\166 k x)) \226\134\146 Affine ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x)).
Time Proof.
Time revert \206\166.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>\206\166 ? /=;
  apply _).
Time Qed.
Time #[global]
Instance big_sepL_affine_id  Ps: (TCForall Affine Ps \226\134\146 Affine ([\226\136\151] Ps)).
Time Proof.
Time (induction 1; simpl; apply _).
Time Qed.
Time End sep_list.
Time Section sep_list_more.
Time Context {A : Type}.
Time Implicit Type l : list A.
Time Implicit Types \206\166 \206\168 : nat \226\134\146 A \226\134\146 PROP.
Time
Lemma big_sepL_zip_with {B} {C} \206\166 f (l1 : list B) 
  (l2 : list C) :
  ([\226\136\151 list] k\226\134\166x \226\136\136 zip_with f l1 l2, \206\166 k x)
  \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166x \226\136\136 l1, match l2 !! k with
                         | Some y => \206\166 k (f x y)
                         | _ => emp
                         end).
Time Proof.
Time
(revert \206\166 l2; <ssreflect_plugin::ssrtclintros@0> induction l1 as [| x l1 IH]
  =>\206\166 [|y l2] //=).
Time -
Time by rewrite big_sepL_emp left_id.
Time -
Time by rewrite IH.
Time Qed.
Time End sep_list_more.
Time
Lemma big_sepL2_alt {A} {B} (\206\166 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP) 
  l1 l2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)
  \226\138\163\226\138\162 \226\140\156length l1 = length l2\226\140\157 \226\136\167 ([\226\136\151 list] k\226\134\166y \226\136\136 zip l1 l2, \206\166 k y.1 y.2).
Time Proof.
Time (apply (anti_symm _)).
Time -
Time (apply and_intro).
Time +
Time revert \206\166 l2.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l1 as [| x1 l1 IH] =>\206\166 -
  [|x2 l2] /=; auto using pure_intro, False_elim).
Time rewrite IH sep_elim_r.
Time (apply pure_mono; auto).
Time +
Time revert \206\166 l2.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l1 as [| x1 l1 IH] =>\206\166 -
  [|x2 l2] /=; auto using pure_intro, False_elim).
Time by rewrite IH.
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>/Forall2_same_length
 Hl).
Time revert \206\166.
Time
(<ssreflect_plugin::ssrtclintros@0> induction Hl as [| x1 l1 x2 l2 _ _ IH]
 =>\206\166 //=).
Time by rewrite -IH.
Time Qed.
Time Section sep_list2.
Time Context {A B : Type}.
Time Implicit Types \206\166 \206\168 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP.
Time Lemma big_sepL2_nil \206\166 : ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 [];[], \206\166 k y1 y2) \226\138\163\226\138\162 emp.
Time Proof.
Time done.
Time Qed.
Time
Lemma big_sepL2_nil' `{BiAffine PROP} P \206\166 :
  P \226\138\162 [\226\136\151 list] k\226\134\166y1;y2 \226\136\136 [];[], \206\166 k y1 y2.
Time Proof.
Time (apply (affine _)).
Time Qed.
Time
Lemma big_sepL2_cons \206\166 x1 x2 l1 l2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 (x1 :: l1);(x2 :: l2), \206\166 k y1 y2)
  \226\138\163\226\138\162 \206\166 0 x1 x2 \226\136\151 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 (S k) y1 y2).
Time Proof.
Time done.
Time Qed.
Time
Lemma big_sepL2_cons_inv_l \206\166 x1 l1 l2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 (x1 :: l1);l2, \206\166 k y1 y2)
  -\226\136\151 \226\136\131 x2 l2',
       \226\140\156l2 = x2 :: l2'\226\140\157
       \226\136\167 \206\166 0 x1 x2 \226\136\151 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2', \206\166 (S k) y1 y2).
Time Proof.
Time (destruct l2 as [| x2 l2]; simpl; auto using False_elim).
Time by rewrite -(exist_intro x2) -(exist_intro l2) pure_True // left_id.
Time Qed.
Time
Lemma big_sepL2_cons_inv_r \206\166 x2 l1 l2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;(x2 :: l2), \206\166 k y1 y2)
  -\226\136\151 \226\136\131 x1 l1',
       \226\140\156l1 = x1 :: l1'\226\140\157
       \226\136\167 \206\166 0 x1 x2 \226\136\151 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1';l2, \206\166 (S k) y1 y2).
Time Proof.
Time (destruct l1 as [| x1 l1]; simpl; auto using False_elim).
Time by rewrite -(exist_intro x1) -(exist_intro l1) pure_True // left_id.
Time Qed.
Time
Lemma big_sepL2_singleton \206\166 x1 x2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 [x1];[x2], \206\166 k y1 y2) \226\138\163\226\138\162 \206\166 0 x1 x2.
Time Proof.
Time by rewrite /= right_id.
Time Qed.
Time
Lemma big_sepL2_length \206\166 l1 l2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2) -\226\136\151 \226\140\156length l1 = length l2\226\140\157.
Time Proof.
Time by rewrite big_sepL2_alt and_elim_l.
Time Qed.
Time
Lemma big_sepL2_app \206\166 l1 l2 l1' l2' :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l1', \206\166 k y1 y2)
  -\226\136\151 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l2;l2', \206\166 (length l1 + k) y1 y2)
     -\226\136\151 [\226\136\151 list] k\226\134\166y1;y2 \226\136\136 (l1 ++ l2);(l1' ++ l2'), 
     \206\166 k y1 y2.
Time Proof.
Time (apply wand_intro_r).
Time revert \206\166 l1'.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l1 as [| x1 l1 IH] =>\206\166 -
 [|x1' l1'] /=).
Time -
Time by rewrite left_id.
Time -
Time rewrite left_absorb.
Time (apply False_elim).
Time -
Time rewrite left_absorb.
Time (apply False_elim).
Time -
Time by rewrite -assoc IH.
Time Qed.
Time
Lemma big_sepL2_app_inv_l \206\166 l1' l1'' l2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 (l1' ++ l1'');l2, \206\166 k y1 y2)
  -\226\136\151 \226\136\131 l2' l2'',
       \226\140\156l2 = l2' ++ l2''\226\140\157
       \226\136\167 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1';l2', \206\166 k y1 y2)
         \226\136\151 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1'';l2'', \206\166 (length l1' + k) y1 y2).
Time Proof.
Time
rewrite -(exist_intro (take (length l1') l2))
 -(exist_intro (drop (length l1') l2)) take_drop pure_True // left_id.
Time revert \206\166 l2.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l1' as [| x1 l1' IH] =>\206\166 -
  [|x2 l2] /=;
  [ by rewrite left_id | by rewrite left_id | apply False_elim |  ]).
Time by rewrite IH -assoc.
Time Qed.
Time
Lemma big_sepL2_app_inv_r \206\166 l1 l2' l2'' :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;(l2' ++ l2''), \206\166 k y1 y2)
  -\226\136\151 \226\136\131 l1' l1'',
       \226\140\156l1 = l1' ++ l1''\226\140\157
       \226\136\167 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1';l2', \206\166 k y1 y2)
         \226\136\151 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1'';l2'', \206\166 (length l2' + k) y1 y2).
Time Proof.
Time
rewrite -(exist_intro (take (length l2') l1))
 -(exist_intro (drop (length l2') l1)) take_drop pure_True // left_id.
Time revert \206\166 l1.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l2' as [| x2 l2' IH] =>\206\166 -
  [|x1 l1] /=;
  [ by rewrite left_id | by rewrite left_id | apply False_elim |  ]).
Time by rewrite IH -assoc.
Time Qed.
Time
Lemma big_sepL2_app_inv \206\166 l1 l2 l1' l2' :
  length l1 = length l1'
  \226\134\146 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 (l1 ++ l2);(l1' ++ l2'), \206\166 k y1 y2)
    -\226\136\151 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l1', \206\166 k y1 y2)
       \226\136\151 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l2;l2', \206\166 (length l1 + k)%nat y1 y2).
Time Proof.
Time revert \206\166 l1'.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l1 as [| x1 l1 IH] =>\206\166 -
  [|x1' l1'] //= ?; simplify_eq).
Time -
Time by rewrite left_id.
Time -
Time by rewrite -assoc IH.
Time Qed.
Time
Lemma big_sepL2_mono \206\166 \206\168 l1 l2 :
  (\226\136\128 k y1 y2, l1 !! k = Some y1 \226\134\146 l2 !! k = Some y2 \226\134\146 \206\166 k y1 y2 \226\138\162 \206\168 k y1 y2)
  \226\134\146 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)
    \226\138\162 [\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\168 k y1 y2.
Time Proof.
Time (intros H).
Time rewrite !big_sepL2_alt.
Time f_equiv.
Time (<ssreflect_plugin::ssrtclintros@0> apply big_sepL_mono =>k [y1 y2]).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite lookup_zip_with =>?;
  simplify_option_eq; auto).
Time Qed.
Time
Lemma big_sepL2_proper \206\166 \206\168 l1 l2 :
  (\226\136\128 k y1 y2, l1 !! k = Some y1 \226\134\146 l2 !! k = Some y2 \226\134\146 \206\166 k y1 y2 \226\138\163\226\138\162 \206\168 k y1 y2)
  \226\134\146 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)
    \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\168 k y1 y2).
Time Proof.
Time
(intros; apply (anti_symm _); apply big_sepL2_mono; auto
  using equiv_entails, equiv_entails_sym).
Time Qed.
Time #[global]
Instance big_sepL2_ne  n:
 (Proper
    (pointwise_relation _
       (pointwise_relation _ (pointwise_relation _ (dist n))) ==>
     (=) ==> (=) ==> dist n) (big_sepL2 (PROP:=PROP) (A:=A) (B:=B))).
Time Proof.
Time (intros \206\1661 \206\1662 H\206\166 x1 ? <- x2 ? <-).
Time rewrite !big_sepL2_alt.
Time f_equiv.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>k [y1 y2]).
Time (apply H\206\166).
Time Qed.
Time #[global]
Instance big_sepL2_mono' :
 (Proper
    (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (\226\138\162))) ==>
     (=) ==> (=) ==> (\226\138\162)) (big_sepL2 (PROP:=PROP) (A:=A) (B:=B))).
Time Proof.
Time (intros f g Hf l1 ? <- l2 ? <-).
Time (apply big_sepL2_mono; intros; apply Hf).
Time Qed.
Time #[global]
Instance big_sepL2_proper' :
 (Proper
    (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (\226\138\163\226\138\162))) ==>
     (=) ==> (=) ==> (\226\138\163\226\138\162)) (big_sepL2 (PROP:=PROP) (A:=A) (B:=B))).
Time Proof.
Time (intros f g Hf l1 ? <- l2 ? <-).
Time (apply big_sepL2_proper; intros; apply Hf).
Time Qed.
Time
Lemma big_sepL2_lookup_acc \206\166 l1 l2 i x1 x2 :
  l1 !! i = Some x1
  \226\134\146 l2 !! i = Some x2
    \226\134\146 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)
      \226\138\162 \206\166 i x1 x2 \226\136\151 (\206\166 i x1 x2 -\226\136\151 [\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2).
Time Proof.
Time (intros Hl1 Hl2).
Time rewrite big_sepL2_alt.
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>Hl).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite {+1}big_sepL_lookup_acc ; last  by
 rewrite lookup_zip_with; simplify_option_eq).
Time by rewrite pure_True // left_id.
Time Qed.
Time
Lemma big_sepL2_lookup \206\166 l1 l2 i x1 x2 `{!Absorbing (\206\166 i x1 x2)} :
  l1 !! i = Some x1
  \226\134\146 l2 !! i = Some x2 \226\134\146 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2) \226\138\162 \206\166 i x1 x2.
Time Proof.
Time (intros).
Time rewrite big_sepL2_lookup_acc //.
Time by rewrite sep_elim_l.
Time Qed.
Time
Lemma big_sepL2_fmap_l {A'} (f : A \226\134\146 A') (\206\166 : nat \226\134\146 A' \226\134\146 B \226\134\146 PROP) 
  l1 l2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 (f <$> l1);l2, \206\166 k y1 y2)
  \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k (f y1) y2).
Time Proof.
Time
rewrite !big_sepL2_alt fmap_length zip_with_fmap_l zip_with_zip big_sepL_fmap.
Time by f_equiv; <ssreflect_plugin::ssrtclintros@0> f_equiv =>k [? ?].
Time Qed.
Time
Lemma big_sepL2_fmap_r {B'} (g : B \226\134\146 B') (\206\166 : nat \226\134\146 A \226\134\146 B' \226\134\146 PROP) 
  l1 l2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;(g <$> l2), \206\166 k y1 y2)
  \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 (g y2)).
Time Proof.
Time
rewrite !big_sepL2_alt fmap_length zip_with_fmap_r zip_with_zip big_sepL_fmap.
Time by f_equiv; <ssreflect_plugin::ssrtclintros@0> f_equiv =>k [? ?].
Time Qed.
Time
Lemma big_sepL2_reverse_2 (\206\166 : A \226\134\146 B \226\134\146 PROP) l1 l2 :
  ([\226\136\151 list] y1;y2 \226\136\136 l1;l2, \206\166 y1 y2)
  \226\138\162 [\226\136\151 list] y1;y2 \226\136\136 reverse l1;reverse l2, \206\166 y1 y2.
Time Proof.
Time revert l2.
Time
(induction l1 as [| x1 l1 IH]; intros [| x2 l2]; simpl; auto using False_elim).
Time rewrite !reverse_cons (comm bi_sep) IH.
Time
by rewrite (big_sepL2_app _ _ [x1] _ [x2]) big_sepL2_singleton wand_elim_l.
Time Qed.
Time
Lemma big_sepL2_reverse (\206\166 : A \226\134\146 B \226\134\146 PROP) l1 l2 :
  ([\226\136\151 list] y1;y2 \226\136\136 reverse l1;reverse l2, \206\166 y1 y2)
  \226\138\163\226\138\162 ([\226\136\151 list] y1;y2 \226\136\136 l1;l2, \206\166 y1 y2).
Time Proof.
Time
(apply (anti_symm _); by rewrite big_sepL2_reverse_2 ?reverse_involutive).
Time Qed.
Time
Lemma big_sepL2_sep \206\166 \206\168 l1 l2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2 \226\136\151 \206\168 k y1 y2)
  \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)
     \226\136\151 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\168 k y1 y2).
Time Proof.
Time rewrite !big_sepL2_alt big_sepL_sep !persistent_and_affinely_sep_l.
Time rewrite -assoc (assoc _ _ (<affine> _)%I).
Time rewrite -(comm bi_sep (<affine> _)%I).
Time
rewrite -assoc (assoc _ _ (<affine> _)%I) -!persistent_and_affinely_sep_l.
Time by rewrite affinely_and_r persistent_and_affinely_sep_l idemp.
Time Qed.
Time
Lemma big_sepL2_and \206\166 \206\168 l1 l2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2 \226\136\167 \206\168 k y1 y2)
  \226\138\162 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)
    \226\136\167 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\168 k y1 y2).
Time Proof.
Time auto using and_intro, big_sepL2_mono, and_elim_l, and_elim_r.
Time Qed.
Time
Lemma big_sepL2_persistently `{BiAffine PROP} \206\166 l1 
  l2 :
  <pers> ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)
  \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, <pers> \206\166 k y1 y2).
Time Proof.
Time
by rewrite !big_sepL2_alt persistently_and persistently_pure
 big_sepL_persistently.
Time Qed.
Time
Lemma big_sepL2_impl \206\166 \206\168 l1 l2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)
  -\226\136\151 \226\150\161 (\226\136\128 k x1 x2,
          \226\140\156l1 !! k = Some x1\226\140\157 \226\134\146 \226\140\156l2 !! k = Some x2\226\140\157 \226\134\146 \206\166 k x1 x2 -\226\136\151 \206\168 k x1 x2)
     -\226\136\151 [\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\168 k y1 y2.
Time Proof.
Time (apply wand_intro_l).
Time revert \206\166 \206\168 l2.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l1 as [| x1 l1 IH] =>\206\166 \206\168
  [|x2 l2] /=; [ by rewrite sep_elim_r.. | idtac ]).
Time
rewrite intuitionistically_sep_dup -assoc [(\226\150\161 _ \226\136\151 _)%I]comm -!assoc assoc.
Time (apply sep_mono).
Time -
Time
rewrite (forall_elim 0) (forall_elim x1) (forall_elim x2) !pure_True //
 !True_impl.
Time by rewrite intuitionistically_elim wand_elim_l.
Time -
Time rewrite comm -(IH (\206\166 \226\136\152 S) (\206\168 \226\136\152 S)) /=.
Time (apply sep_mono_l, affinely_mono, persistently_mono).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>k).
Time by rewrite (forall_elim (S k)).
Time Qed.
Time #[global]
Instance big_sepL2_nil_persistent  \206\166:
 (Persistent ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 [];[], \206\166 k y1 y2)).
Time Proof.
Time (simpl; apply _).
Time Qed.
Time #[global]
Instance big_sepL2_persistent  \206\166 l1 l2:
 ((\226\136\128 k x1 x2, Persistent (\206\166 k x1 x2))
  \226\134\146 Persistent ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)).
Time Proof.
Time rewrite big_sepL2_alt.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepL2_nil_affine  \206\166:
 (Affine ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 [];[], \206\166 k y1 y2)).
Time Proof.
Time (simpl; apply _).
Time Qed.
Time #[global]
Instance big_sepL2_affine  \206\166 l1 l2:
 ((\226\136\128 k x1 x2, Affine (\206\166 k x1 x2))
  \226\134\146 Affine ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)).
Time Proof.
Time rewrite big_sepL2_alt.
Time (apply _).
Time Qed.
Time End sep_list2.
Time Section and_list.
Time Context {A : Type}.
Time Implicit Type l : list A.
Time Implicit Types \206\166 \206\168 : nat \226\134\146 A \226\134\146 PROP.
Time Lemma big_andL_nil \206\166 : ([\226\136\167 list] k\226\134\166y \226\136\136 nil, \206\166 k y) \226\138\163\226\138\162 True.
Time Proof.
Time done.
Time Qed.
Time Lemma big_andL_nil' P \206\166 : P \226\138\162 [\226\136\167 list] k\226\134\166y \226\136\136 nil, \206\166 k y.
Time Proof.
Time by apply pure_intro.
Time Qed.
Time
Lemma big_andL_cons \206\166 x l :
  ([\226\136\167 list] k\226\134\166y \226\136\136 (x :: l), \206\166 k y) \226\138\163\226\138\162 \206\166 0 x \226\136\167 ([\226\136\167 list] k\226\134\166y \226\136\136 l, \206\166 (S k) y).
Time Proof.
Time by rewrite big_opL_cons.
Time Qed.
Time Lemma big_andL_singleton \206\166 x : ([\226\136\167 list] k\226\134\166y \226\136\136 [x], \206\166 k y) \226\138\163\226\138\162 \206\166 0 x.
Time Proof.
Time by rewrite big_opL_singleton.
Time Qed.
Time
Lemma big_andL_app \206\166 l1 l2 :
  ([\226\136\167 list] k\226\134\166y \226\136\136 (l1 ++ l2), \206\166 k y)
  \226\138\163\226\138\162 ([\226\136\167 list] k\226\134\166y \226\136\136 l1, \206\166 k y) \226\136\167 ([\226\136\167 list] k\226\134\166y \226\136\136 l2, \206\166 (length l1 + k) y).
Time Proof.
Time by rewrite big_opL_app.
Time Qed.
Time
Lemma big_andL_mono \206\166 \206\168 l :
  (\226\136\128 k y, l !! k = Some y \226\134\146 \206\166 k y \226\138\162 \206\168 k y)
  \226\134\146 ([\226\136\167 list] k\226\134\166y \226\136\136 l, \206\166 k y) \226\138\162 [\226\136\167 list] k\226\134\166y \226\136\136 l, \206\168 k y.
Time Proof.
Time (apply big_opL_forall; apply _).
Time Qed.
Time
Lemma big_andL_proper \206\166 \206\168 l :
  (\226\136\128 k y, l !! k = Some y \226\134\146 \206\166 k y \226\138\163\226\138\162 \206\168 k y)
  \226\134\146 ([\226\136\167 list] k\226\134\166y \226\136\136 l, \206\166 k y) \226\138\163\226\138\162 ([\226\136\167 list] k\226\134\166y \226\136\136 l, \206\168 k y).
Time Proof.
Time (apply big_opL_proper).
Time Qed.
Time
Lemma big_andL_submseteq (\206\166 : A \226\134\146 PROP) l1 l2 :
  l1 \226\138\134+ l2 \226\134\146 ([\226\136\167 list] y \226\136\136 l2, \206\166 y) \226\138\162 [\226\136\167 list] y \226\136\136 l1, \206\166 y.
Time Proof.
Time (intros [l ->]%submseteq_Permutation).
Time by rewrite big_andL_app and_elim_l.
Time Qed.
Time #[global]
Instance big_andL_mono' :
 (Proper (pointwise_relation _ (pointwise_relation _ (\226\138\162)) ==> (=) ==> (\226\138\162))
    (big_opL (@bi_and PROP) (A:=A))).
Time Proof.
Time (intros f g Hf m ? <-).
Time (apply big_opL_forall; apply _ || intros; apply Hf).
Time Qed.
Time #[global]
Instance big_andL_id_mono' :
 (Proper (Forall2 (\226\138\162) ==> (\226\138\162)) (big_opL (@bi_and PROP) (\206\187 _ P, P))).
Time Proof.
Time by induction 1 as [| P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH.
Time Qed.
Time
Lemma big_andL_lookup \206\166 l i x :
  l !! i = Some x \226\134\146 ([\226\136\167 list] k\226\134\166y \226\136\136 l, \206\166 k y) \226\138\162 \206\166 i x.
Time Proof.
Time (intros).
Time rewrite -(take_drop_middle l i x) // big_andL_app /=.
Time
(rewrite Nat.add_0_r take_length_le; eauto
  using lookup_lt_Some, Nat.lt_le_incl, and_elim_l', and_elim_r').
Time Qed.
Time
Lemma big_andL_elem_of (\206\166 : A \226\134\146 PROP) l x :
  x \226\136\136 l \226\134\146 ([\226\136\167 list] y \226\136\136 l, \206\166 y) \226\138\162 \206\166 x.
Time Proof.
Time
(intros [i ?]%elem_of_list_lookup; eauto using (big_andL_lookup (\206\187 _, \206\166))).
Time Qed.
Time
Lemma big_andL_fmap {B} (f : A \226\134\146 B) (\206\166 : nat \226\134\146 B \226\134\146 PROP) 
  l : ([\226\136\167 list] k\226\134\166y \226\136\136 (f <$> l), \206\166 k y) \226\138\163\226\138\162 ([\226\136\167 list] k\226\134\166y \226\136\136 l, \206\166 k (f y)).
Time Proof.
Time by rewrite big_opL_fmap.
Time Qed.
Time
Lemma big_andL_bind {B} (f : A \226\134\146 list B) (\206\166 : B \226\134\146 PROP) 
  l : ([\226\136\167 list] y \226\136\136 (l \226\137\171= f), \206\166 y) \226\138\163\226\138\162 ([\226\136\167 list] x \226\136\136 l, [\226\136\167 list] y \226\136\136 f x, \206\166 y).
Time Proof.
Time by rewrite big_opL_bind.
Time Qed.
Time
Lemma big_andL_and \206\166 \206\168 l :
  ([\226\136\167 list] k\226\134\166x \226\136\136 l, \206\166 k x \226\136\167 \206\168 k x)
  \226\138\163\226\138\162 ([\226\136\167 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\136\167 ([\226\136\167 list] k\226\134\166x \226\136\136 l, \206\168 k x).
Time Proof.
Time by rewrite big_opL_op.
Time Qed.
Time
Lemma big_andL_persistently \206\166 l :
  <pers> ([\226\136\167 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\138\163\226\138\162 ([\226\136\167 list] k\226\134\166x \226\136\136 l, <pers> \206\166 k x).
Time Proof.
Time (apply (big_opL_commute _)).
Time Qed.
Time
Lemma big_andL_forall \206\166 l :
  ([\226\136\167 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\138\163\226\138\162 (\226\136\128 k x, \226\140\156l !! k = Some x\226\140\157 \226\134\146 \206\166 k x).
Time Proof.
Time (apply (anti_symm _)).
Time {
Time
(<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>k;
  <ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply impl_intro_l, pure_elim_l =>?; by
  apply : {}big_andL_lookup {}).
Time }
Time revert \206\166.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>\206\166;
  [ by auto using big_andL_nil' |  ]).
Time rewrite big_andL_cons.
Time (apply and_intro).
Time -
Time by rewrite (forall_elim 0) (forall_elim x) pure_True // True_impl.
Time -
Time rewrite -IH.
Time
(<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>k; by rewrite
  (forall_elim (S k))).
Time Qed.
Time #[global]
Instance big_andL_nil_persistent  \206\166: (Persistent ([\226\136\167 list] k\226\134\166x \226\136\136 [], \206\166 k x)).
Time Proof.
Time (simpl; apply _).
Time Qed.
Time #[global]
Instance big_andL_persistent  \206\166 l:
 ((\226\136\128 k x, Persistent (\206\166 k x)) \226\134\146 Persistent ([\226\136\167 list] k\226\134\166x \226\136\136 l, \206\166 k x)).
Time Proof.
Time revert \206\166.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>\206\166 ? /=;
  apply _).
Time Qed.
Time End and_list.
Time Section or_list.
Time Context {A : Type}.
Time Implicit Type l : list A.
Time Implicit Types \206\166 \206\168 : nat \226\134\146 A \226\134\146 PROP.
Time Lemma big_orL_nil \206\166 : ([\226\136\168 list] k\226\134\166y \226\136\136 nil, \206\166 k y) \226\138\163\226\138\162 False.
Time Proof.
Time done.
Time Qed.
Time
Lemma big_orL_cons \206\166 x l :
  ([\226\136\168 list] k\226\134\166y \226\136\136 (x :: l), \206\166 k y) \226\138\163\226\138\162 \206\166 0 x \226\136\168 ([\226\136\168 list] k\226\134\166y \226\136\136 l, \206\166 (S k) y).
Time Proof.
Time by rewrite big_opL_cons.
Time Qed.
Time Lemma big_orL_singleton \206\166 x : ([\226\136\168 list] k\226\134\166y \226\136\136 [x], \206\166 k y) \226\138\163\226\138\162 \206\166 0 x.
Time Proof.
Time by rewrite big_opL_singleton.
Time Qed.
Time
Lemma big_orL_app \206\166 l1 l2 :
  ([\226\136\168 list] k\226\134\166y \226\136\136 (l1 ++ l2), \206\166 k y)
  \226\138\163\226\138\162 ([\226\136\168 list] k\226\134\166y \226\136\136 l1, \206\166 k y) \226\136\168 ([\226\136\168 list] k\226\134\166y \226\136\136 l2, \206\166 (length l1 + k) y).
Time Proof.
Time by rewrite big_opL_app.
Time Qed.
Time
Lemma big_orL_mono \206\166 \206\168 l :
  (\226\136\128 k y, l !! k = Some y \226\134\146 \206\166 k y \226\138\162 \206\168 k y)
  \226\134\146 ([\226\136\168 list] k\226\134\166y \226\136\136 l, \206\166 k y) \226\138\162 [\226\136\168 list] k\226\134\166y \226\136\136 l, \206\168 k y.
Time Proof.
Time (apply big_opL_forall; apply _).
Time Qed.
Time
Lemma big_orL_proper \206\166 \206\168 l :
  (\226\136\128 k y, l !! k = Some y \226\134\146 \206\166 k y \226\138\163\226\138\162 \206\168 k y)
  \226\134\146 ([\226\136\168 list] k\226\134\166y \226\136\136 l, \206\166 k y) \226\138\163\226\138\162 ([\226\136\168 list] k\226\134\166y \226\136\136 l, \206\168 k y).
Time Proof.
Time (apply big_opL_proper).
Time Qed.
Time
Lemma big_orL_submseteq (\206\166 : A \226\134\146 PROP) l1 l2 :
  l1 \226\138\134+ l2 \226\134\146 ([\226\136\168 list] y \226\136\136 l1, \206\166 y) \226\138\162 [\226\136\168 list] y \226\136\136 l2, \206\166 y.
Time Proof.
Time (intros [l ->]%submseteq_Permutation).
Time by rewrite big_orL_app -or_intro_l.
Time Qed.
Time #[global]
Instance big_orL_mono' :
 (Proper (pointwise_relation _ (pointwise_relation _ (\226\138\162)) ==> (=) ==> (\226\138\162))
    (big_opL (@bi_or PROP) (A:=A))).
Time Proof.
Time (intros f g Hf m ? <-).
Time (apply big_opL_forall; apply _ || intros; apply Hf).
Time Qed.
Time #[global]
Instance big_orL_id_mono' :
 (Proper (Forall2 (\226\138\162) ==> (\226\138\162)) (big_opL (@bi_or PROP) (\206\187 _ P, P))).
Time Proof.
Time by induction 1 as [| P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH.
Time Qed.
Time
Lemma big_orL_lookup \206\166 l i x :
  l !! i = Some x \226\134\146 \206\166 i x \226\138\162 [\226\136\168 list] k\226\134\166y \226\136\136 l, \206\166 k y.
Time Proof.
Time (intros).
Time rewrite -(take_drop_middle l i x) // big_orL_app /=.
Time
(rewrite Nat.add_0_r take_length_le; eauto
  using lookup_lt_Some, Nat.lt_le_incl, or_intro_l', or_intro_r').
Time Qed.
Time
Lemma big_orL_elem_of (\206\166 : A \226\134\146 PROP) l x : x \226\136\136 l \226\134\146 \206\166 x \226\138\162 [\226\136\168 list] y \226\136\136 l, \206\166 y.
Time Proof.
Time
(intros [i ?]%elem_of_list_lookup; eauto using (big_orL_lookup (\206\187 _, \206\166))).
Time Qed.
Time
Lemma big_orL_fmap {B} (f : A \226\134\146 B) (\206\166 : nat \226\134\146 B \226\134\146 PROP) 
  l : ([\226\136\168 list] k\226\134\166y \226\136\136 (f <$> l), \206\166 k y) \226\138\163\226\138\162 ([\226\136\168 list] k\226\134\166y \226\136\136 l, \206\166 k (f y)).
Time Proof.
Time by rewrite big_opL_fmap.
Time Qed.
Time
Lemma big_orL_bind {B} (f : A \226\134\146 list B) (\206\166 : B \226\134\146 PROP) 
  l : ([\226\136\168 list] y \226\136\136 (l \226\137\171= f), \206\166 y) \226\138\163\226\138\162 ([\226\136\168 list] x \226\136\136 l, [\226\136\168 list] y \226\136\136 f x, \206\166 y).
Time Proof.
Time by rewrite big_opL_bind.
Time Qed.
Time
Lemma big_orL_or \206\166 \206\168 l :
  ([\226\136\168 list] k\226\134\166x \226\136\136 l, \206\166 k x \226\136\168 \206\168 k x)
  \226\138\163\226\138\162 ([\226\136\168 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\136\168 ([\226\136\168 list] k\226\134\166x \226\136\136 l, \206\168 k x).
Time Proof.
Time by rewrite big_opL_op.
Time Qed.
Time
Lemma big_orL_persistently \206\166 l :
  <pers> ([\226\136\168 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\138\163\226\138\162 ([\226\136\168 list] k\226\134\166x \226\136\136 l, <pers> \206\166 k x).
Time Proof.
Time (apply (big_opL_commute _)).
Time Qed.
Time
Lemma big_orL_exist \206\166 l :
  ([\226\136\168 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\138\163\226\138\162 (\226\136\131 k x, \226\140\156l !! k = Some x\226\140\157 \226\136\167 \206\166 k x).
Time Proof.
Time (apply (anti_symm _)).
Time {
Time revert \206\166.
Time (<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>\206\166).
Time {
Time rewrite big_orL_nil.
Time (apply False_elim).
Time }
Time rewrite big_orL_cons.
Time (apply or_elim).
Time -
Time by rewrite -(exist_intro 0) -(exist_intro x) pure_True // left_id.
Time -
Time rewrite IH.
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>k).
Time by rewrite -(exist_intro (S k)).
Time }
Time
(<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>k;
  <ssreflect_plugin::ssrtclintros@0> apply exist_elim =>x).
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>?).
Time by apply : {}big_orL_lookup {}.
Time Qed.
Time
Lemma big_orL_sep_l P \206\166 l :
  P \226\136\151 ([\226\136\168 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\138\163\226\138\162 ([\226\136\168 list] k\226\134\166x \226\136\136 l, P \226\136\151 \206\166 k x).
Time Proof.
Time rewrite !big_orL_exist sep_exist_l.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>k).
Time rewrite sep_exist_l.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>x).
Time by rewrite !persistent_and_affinely_sep_l !assoc (comm _ P).
Time Qed.
Time
Lemma big_orL_sep_r Q \206\166 l :
  ([\226\136\168 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\136\151 Q \226\138\163\226\138\162 ([\226\136\168 list] k\226\134\166x \226\136\136 l, \206\166 k x \226\136\151 Q).
Time Proof.
Time setoid_rewrite (comm bi_sep).
Time (apply big_orL_sep_l).
Time Qed.
Time #[global]
Instance big_orL_nil_persistent  \206\166: (Persistent ([\226\136\168 list] k\226\134\166x \226\136\136 [], \206\166 k x)).
Time Proof.
Time (simpl; apply _).
Time Qed.
Time #[global]
Instance big_orL_persistent  \206\166 l:
 ((\226\136\128 k x, Persistent (\206\166 k x)) \226\134\146 Persistent ([\226\136\168 list] k\226\134\166x \226\136\136 l, \206\166 k x)).
Time Proof.
Time revert \206\166.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>\206\166 ? /=;
  apply _).
Time Qed.
Time End or_list.
Time Section map.
Time Context `{Countable K} {A : Type}.
Time Implicit Type m : gmap K A.
Time Implicit Types \206\166 \206\168 : K \226\134\146 A \226\134\146 PROP.
Time
Lemma big_sepM_mono \206\166 \206\168 m :
  (\226\136\128 k x, m !! k = Some x \226\134\146 \206\166 k x \226\138\162 \206\168 k x)
  \226\134\146 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x) \226\138\162 [\226\136\151 map] k\226\134\166x \226\136\136 m, \206\168 k x.
Time Proof.
Time (apply big_opM_forall; apply _ || auto).
Time Qed.
Time
Lemma big_sepM_proper \206\166 \206\168 m :
  (\226\136\128 k x, m !! k = Some x \226\134\146 \206\166 k x \226\138\163\226\138\162 \206\168 k x)
  \226\134\146 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x) \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\168 k x).
Time Proof.
Time (apply big_opM_proper).
Time Qed.
Time
Lemma big_sepM_subseteq `{BiAffine PROP} \206\166 m1 m2 :
  m2 \226\138\134 m1 \226\134\146 ([\226\136\151 map] k\226\134\166x \226\136\136 m1, \206\166 k x) \226\138\162 [\226\136\151 map] k\226\134\166x \226\136\136 m2, \206\166 k x.
Time Proof.
Time (intros).
Time by apply big_sepL_submseteq, map_to_list_submseteq.
Time Qed.
Time #[global]
Instance big_sepM_mono' :
 (Proper (pointwise_relation _ (pointwise_relation _ (\226\138\162)) ==> (=) ==> (\226\138\162))
    (big_opM (@bi_sep PROP) (K:=K) (A:=A))).
Time Proof.
Time (intros f g Hf m ? <-).
Time
(<ssreflect_plugin::ssrtclintros@0> apply big_sepM_mono =>? ? ?; apply Hf).
Time Qed.
Time Lemma big_sepM_empty \206\166 : ([\226\136\151 map] k\226\134\166x \226\136\136 \226\136\133, \206\166 k x) \226\138\163\226\138\162 emp.
Time Proof.
Time by rewrite big_opM_empty.
Time Qed.
Time Lemma big_sepM_empty' `{BiAffine PROP} P \206\166 : P \226\138\162 [\226\136\151 map] k\226\134\166x \226\136\136 \226\136\133, \206\166 k x.
Time Proof.
Time rewrite big_sepM_empty.
Time apply : {}affine {}.
Time Qed.
Time
Lemma big_sepM_insert \206\166 m i x :
  m !! i = None
  \226\134\146 ([\226\136\151 map] k\226\134\166y \226\136\136 <[i:=x]> m, \206\166 k y) \226\138\163\226\138\162 \206\166 i x \226\136\151 ([\226\136\151 map] k\226\134\166y \226\136\136 m, \206\166 k y).
Time Proof.
Time (apply big_opM_insert).
Time Qed.
Time
Lemma big_sepM_delete \206\166 m i x :
  m !! i = Some x
  \226\134\146 ([\226\136\151 map] k\226\134\166y \226\136\136 m, \206\166 k y) \226\138\163\226\138\162 \206\166 i x \226\136\151 ([\226\136\151 map] k\226\134\166y \226\136\136 delete i m, \206\166 k y).
Time Proof.
Time (apply big_opM_delete).
Time Qed.
Time
Lemma big_sepM_insert_2 \206\166 m i x :
  TCOr (\226\136\128 x, Affine (\206\166 i x)) (Absorbing (\206\166 i x))
  \226\134\146 \206\166 i x -\226\136\151 ([\226\136\151 map] k\226\134\166y \226\136\136 m, \206\166 k y) -\226\136\151 [\226\136\151 map] k\226\134\166y \226\136\136 <[i:=x]> m, \206\166 k y.
Time Proof.
Time (intros Ha).
Time (apply wand_intro_r).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (m !! i) as [y| ] eqn:Hi ; last 
 first).
Time {
Time by rewrite -big_sepM_insert.
Time }
Time (assert (TCOr (Affine (\206\166 i y)) (Absorbing (\206\166 i x)))).
Time {
Time (destruct Ha; try apply _).
Time }
Time rewrite big_sepM_delete // assoc.
Time rewrite (sep_elim_l (\206\166 i x)) -big_sepM_insert ?lookup_delete //.
Time by rewrite insert_delete.
Time Qed.
Time
Lemma big_sepM_lookup_acc \206\166 m i x :
  m !! i = Some x
  \226\134\146 ([\226\136\151 map] k\226\134\166y \226\136\136 m, \206\166 k y) \226\138\162 \206\166 i x \226\136\151 (\206\166 i x -\226\136\151 [\226\136\151 map] k\226\134\166y \226\136\136 m, \206\166 k y).
Time Proof.
Time (intros).
Time rewrite big_sepM_delete //.
Time by apply sep_mono_r, wand_intro_l.
Time Qed.
Time
Lemma big_sepM_lookup \206\166 m i x `{!Absorbing (\206\166 i x)} :
  m !! i = Some x \226\134\146 ([\226\136\151 map] k\226\134\166y \226\136\136 m, \206\166 k y) \226\138\162 \206\166 i x.
Time Proof.
Time (intros).
Time rewrite big_sepM_lookup_acc //.
Time by rewrite sep_elim_l.
Time Qed.
Time
Lemma big_sepM_lookup_dom (\206\166 : K \226\134\146 PROP) m i `{!Absorbing (\206\166 i)} :
  is_Some (m !! i) \226\134\146 ([\226\136\151 map] k\226\134\166_ \226\136\136 m, \206\166 k) \226\138\162 \206\166 i.
Time Proof.
Time (intros [x ?]).
Time by eapply (big_sepM_lookup (\206\187 i x, \206\166 i)).
Time Qed.
Time
Lemma big_sepM_singleton \206\166 i x : ([\226\136\151 map] k\226\134\166y \226\136\136 {[i := x]}, \206\166 k y) \226\138\163\226\138\162 \206\166 i x.
Time Proof.
Time by rewrite big_opM_singleton.
Time Qed.
Time
Lemma big_sepM_fmap {B} (f : A \226\134\146 B) (\206\166 : K \226\134\146 B \226\134\146 PROP) 
  m : ([\226\136\151 map] k\226\134\166y \226\136\136 (f <$> m), \206\166 k y) \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166y \226\136\136 m, \206\166 k (f y)).
Time Proof.
Time by rewrite big_opM_fmap.
Time Qed.
Time
Lemma big_sepM_insert_override \206\166 m i x x' :
  m !! i = Some x
  \226\134\146 \206\166 i x \226\138\163\226\138\162 \206\166 i x'
    \226\134\146 ([\226\136\151 map] k\226\134\166y \226\136\136 <[i:=x']> m, \206\166 k y) \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166y \226\136\136 m, \206\166 k y).
Time Proof.
Time (apply big_opM_insert_override).
Time Qed.
Time
Lemma big_sepM_insert_override_1 \206\166 m i x x' :
  m !! i = Some x
  \226\134\146 ([\226\136\151 map] k\226\134\166y \226\136\136 <[i:=x']> m, \206\166 k y)
    \226\138\162 (\206\166 i x' -\226\136\151 \206\166 i x) -\226\136\151 [\226\136\151 map] k\226\134\166y \226\136\136 m, \206\166 k y.
Time Proof.
Time (intros ?).
Time (apply wand_intro_l).
Time rewrite -insert_delete big_sepM_insert ?lookup_delete //.
Time by rewrite assoc wand_elim_l -big_sepM_delete.
Time Qed.
Time
Lemma big_sepM_insert_override_2 \206\166 m i x x' :
  m !! i = Some x
  \226\134\146 ([\226\136\151 map] k\226\134\166y \226\136\136 m, \206\166 k y)
    \226\138\162 (\206\166 i x -\226\136\151 \206\166 i x') -\226\136\151 [\226\136\151 map] k\226\134\166y \226\136\136 <[i:=x']> m, \206\166 k y.
Time Proof.
Time (intros ?).
Time (apply wand_intro_l).
Time (rewrite {+1}big_sepM_delete //; rewrite assoc wand_elim_l).
Time rewrite -insert_delete big_sepM_insert ?lookup_delete //.
Time Qed.
Time
Lemma big_sepM_insert_acc \206\166 m i x :
  m !! i = Some x
  \226\134\146 ([\226\136\151 map] k\226\134\166y \226\136\136 m, \206\166 k y)
    \226\138\162 \206\166 i x \226\136\151 (\226\136\128 x', \206\166 i x' -\226\136\151 [\226\136\151 map] k\226\134\166y \226\136\136 <[i:=x']> m, \206\166 k y).
Time Proof.
Time (intros ?).
Time rewrite {+1}big_sepM_delete //.
Time (apply sep_mono; [ done |  ]).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x').
Time rewrite -insert_delete big_sepM_insert ?lookup_delete //.
Time by apply wand_intro_l.
Time Qed.
Time
Lemma big_sepM_fn_insert {B} (\206\168 : K \226\134\146 A \226\134\146 B \226\134\146 PROP) 
  (f : K \226\134\146 B) m i x b :
  m !! i = None
  \226\134\146 ([\226\136\151 map] k\226\134\166y \226\136\136 <[i:=x]> m, \206\168 k y (<[i:=b]> f k))
    \226\138\163\226\138\162 \206\168 i x b \226\136\151 ([\226\136\151 map] k\226\134\166y \226\136\136 m, \206\168 k y (f k)).
Time Proof.
Time (apply big_opM_fn_insert).
Time Qed.
Time
Lemma big_sepM_fn_insert' (\206\166 : K \226\134\146 PROP) m i x P :
  m !! i = None
  \226\134\146 ([\226\136\151 map] k\226\134\166y \226\136\136 <[i:=x]> m, <[i:=P]> \206\166 k) \226\138\163\226\138\162 P \226\136\151 ([\226\136\151 map] k\226\134\166y \226\136\136 m, \206\166 k).
Time Proof.
Time (apply big_opM_fn_insert').
Time Qed.
Time
Lemma big_sepM_union \206\166 m1 m2 :
  m1 ##\226\130\152 m2
  \226\134\146 ([\226\136\151 map] k\226\134\166y \226\136\136 (m1 \226\136\170 m2), \206\166 k y)
    \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166y \226\136\136 m1, \206\166 k y) \226\136\151 ([\226\136\151 map] k\226\134\166y \226\136\136 m2, \206\166 k y).
Time Proof.
Time (apply big_opM_union).
Time Qed.
Time
Lemma big_sepM_sep \206\166 \206\168 m :
  ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x \226\136\151 \206\168 k x)
  \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x) \226\136\151 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\168 k x).
Time Proof.
Time (apply big_opM_op).
Time Qed.
Time
Lemma big_sepM_and \206\166 \206\168 m :
  ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x \226\136\167 \206\168 k x)
  \226\138\162 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x) \226\136\167 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\168 k x).
Time Proof.
Time auto using and_intro, big_sepM_mono, and_elim_l, and_elim_r.
Time Qed.
Time
Lemma big_sepM_persistently `{BiAffine PROP} \206\166 m :
  <pers> ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x) \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166x \226\136\136 m, <pers> \206\166 k x).
Time Proof.
Time (apply (big_opM_commute _)).
Time Qed.
Time
Lemma big_sepM_forall `{BiAffine PROP} \206\166 m :
  (\226\136\128 k x, Persistent (\206\166 k x))
  \226\134\146 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x) \226\138\163\226\138\162 (\226\136\128 k x, \226\140\156m !! k = Some x\226\140\157 \226\134\146 \206\166 k x).
Time Proof.
Time (intros).
Time (apply (anti_symm _)).
Time {
Time
(<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>k;
  <ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply impl_intro_l, pure_elim_l =>?; by
  apply : {}big_sepM_lookup {}).
Time }
Time
(induction m as [| i x m ? IH] using map_ind; auto using big_sepM_empty').
Time rewrite big_sepM_insert // -persistent_and_sep.
Time (apply and_intro).
Time -
Time rewrite (forall_elim i) (forall_elim x) lookup_insert.
Time by rewrite pure_True // True_impl.
Time -
Time rewrite -IH.
Time
(<ssreflect_plugin::ssrtclintros@0> apply forall_mono =>k;
  <ssreflect_plugin::ssrtclintros@0> apply forall_mono =>y).
Time
(<ssreflect_plugin::ssrtclintros@0> apply impl_intro_l, pure_elim_l =>?).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite lookup_insert_ne ; last  by
 intros ?; simplify_map_eq).
Time by rewrite pure_True // True_impl.
Time Qed.
Time
Lemma big_sepM_impl \206\166 \206\168 m :
  ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x)
  -\226\136\151 \226\150\161 (\226\136\128 k x, \226\140\156m !! k = Some x\226\140\157 \226\134\146 \206\166 k x -\226\136\151 \206\168 k x) -\226\136\151 [\226\136\151 map] k\226\134\166x \226\136\136 m, \206\168 k x.
Time Proof.
Time (apply wand_intro_l).
Time (induction m as [| i x m ? IH] using map_ind).
Time {
Time by rewrite sep_elim_r.
Time }
Time rewrite !big_sepM_insert // intuitionistically_sep_dup.
Time rewrite -assoc [(\226\150\161 _ \226\136\151 _)%I]comm -!assoc assoc.
Time (apply sep_mono).
Time -
Time rewrite (forall_elim i) (forall_elim x) pure_True ?lookup_insert //.
Time by rewrite True_impl intuitionistically_elim wand_elim_l.
Time -
Time rewrite comm -IH /=.
Time
(<ssreflect_plugin::ssrtclintros@0>
 apply sep_mono_l, affinely_mono, persistently_mono, forall_mono =>k).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_mono =>y).
Time
(<ssreflect_plugin::ssrtclintros@0> apply impl_intro_l, pure_elim_l =>?).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite lookup_insert_ne ; last  by
 intros ?; simplify_map_eq).
Time by rewrite pure_True // True_impl.
Time Qed.
Time #[global]
Instance big_sepM_empty_persistent  \206\166: (Persistent ([\226\136\151 map] k\226\134\166x \226\136\136 \226\136\133, \206\166 k x)).
Time Proof.
Time rewrite /big_opM map_to_list_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepM_persistent  \206\166 m:
 ((\226\136\128 k x, Persistent (\206\166 k x)) \226\134\146 Persistent ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x)).
Time Proof.
Time (intros).
Time
(<ssreflect_plugin::ssrtclintros@0> apply big_sepL_persistent =>_ 
  [? ?]; apply _).
Time Qed.
Time #[global]
Instance big_sepM_empty_affine  \206\166: (Affine ([\226\136\151 map] k\226\134\166x \226\136\136 \226\136\133, \206\166 k x)).
Time Proof.
Time rewrite /big_opM map_to_list_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepM_affine  \206\166 m:
 ((\226\136\128 k x, Affine (\206\166 k x)) \226\134\146 Affine ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x)).
Time Proof.
Time (intros).
Time
(<ssreflect_plugin::ssrtclintros@0> apply big_sepL_affine =>_ [? ?]; apply _).
Time Qed.
Time End map.
Time Section map2.
Time Context `{Countable K} {A B : Type}.
Time Implicit Types \206\166 \206\168 : K \226\134\146 A \226\134\146 B \226\134\146 PROP.
Time
Lemma big_sepM2_dom \206\166 m1 m2 :
  ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2) -\226\136\151 \226\140\156dom (gset K) m1 = dom (gset K) m2\226\140\157.
Time Proof.
Time rewrite /big_sepM2 and_elim_l.
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_mono =>Hm).
Time (<ssreflect_plugin::ssrtclintros@0> set_unfold =>k).
Time by rewrite !elem_of_dom.
Time Qed.
Time
Lemma big_sepM2_mono \206\166 \206\168 m1 m2 :
  (\226\136\128 k y1 y2, m1 !! k = Some y1 \226\134\146 m2 !! k = Some y2 \226\134\146 \206\166 k y1 y2 \226\138\162 \206\168 k y1 y2)
  \226\134\146 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2) \226\138\162 [\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\168 k y1 y2.
Time Proof.
Time (intros Hm1m2).
Time rewrite /big_sepM2.
Time (apply and_mono_r, big_sepM_mono).
Time (intros k [x1 x2]).
Time rewrite map_lookup_zip_with.
Time specialize (Hm1m2 k x1 x2).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (m1 !! k) as [y1| ] ; last  done).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (m2 !! k) as [y2| ]; simpl ; last 
 done).
Time (intros ?; simplify_eq).
Time by apply Hm1m2.
Time Qed.
Time
Lemma big_sepM2_proper \206\166 \206\168 m1 m2 :
  (\226\136\128 k y1 y2, m1 !! k = Some y1 \226\134\146 m2 !! k = Some y2 \226\134\146 \206\166 k y1 y2 \226\138\163\226\138\162 \206\168 k y1 y2)
  \226\134\146 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2)
    \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\168 k y1 y2).
Time Proof.
Time
(intros; apply (anti_symm _); apply big_sepM2_mono; auto
  using equiv_entails, equiv_entails_sym).
Time Qed.
Time #[global]
Instance big_sepM2_ne  n:
 (Proper
    (pointwise_relation _
       (pointwise_relation _ (pointwise_relation _ (dist n))) ==>
     (=) ==> (=) ==> dist n) (big_sepM2 (PROP:=PROP) (K:=K) (A:=A) (B:=B))).
Time Proof.
Time (intros \206\1661 \206\1662 H\206\166 x1 ? <- x2 ? <-).
Time rewrite /big_sepM2.
Time f_equiv.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>k [y1 y2]).
Time (apply H\206\166).
Time Qed.
Time #[global]
Instance big_sepM2_mono' :
 (Proper
    (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (\226\138\162))) ==>
     (=) ==> (=) ==> (\226\138\162)) (big_sepM2 (PROP:=PROP) (K:=K) (A:=A) (B:=B))).
Time Proof.
Time (intros f g Hf m1 ? <- m2 ? <-).
Time (apply big_sepM2_mono; intros; apply Hf).
Time Qed.
Time #[global]
Instance big_sepM2_proper' :
 (Proper
    (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (\226\138\163\226\138\162))) ==>
     (=) ==> (=) ==> (\226\138\163\226\138\162)) (big_sepM2 (PROP:=PROP) (K:=K) (A:=A) (B:=B))).
Time Proof.
Time (intros f g Hf m1 ? <- m2 ? <-).
Time (apply big_sepM2_proper; intros; apply Hf).
Time Qed.
Time Lemma big_sepM2_empty \206\166 : ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 \226\136\133;\226\136\133, \206\166 k y1 y2) \226\138\163\226\138\162 emp.
Time Proof.
Time rewrite /big_sepM2 pure_True ?left_id //.
Time (intros k).
Time (rewrite !lookup_empty; split; by inversion 1).
Time Qed.
Time
Lemma big_sepM2_empty' `{BiAffine PROP} P \206\166 :
  P \226\138\162 [\226\136\151 map] k\226\134\166y1;y2 \226\136\136 \226\136\133;\226\136\133, \206\166 k y1 y2.
Time Proof.
Time rewrite big_sepM2_empty.
Time (apply (affine _)).
Time Qed.
Time
Lemma big_sepM2_empty_l m1 \206\166 : ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;\226\136\133, \206\166 k y1 y2) \226\138\162 \226\140\156m1 = \226\136\133\226\140\157.
Time Proof.
Time rewrite big_sepM2_dom dom_empty_L.
Time (apply pure_mono, dom_empty_inv_L).
Time Qed.
Time
Lemma big_sepM2_empty_r m2 \206\166 : ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 \226\136\133;m2, \206\166 k y1 y2) \226\138\162 \226\140\156m2 = \226\136\133\226\140\157.
Time Proof.
Time rewrite big_sepM2_dom dom_empty_L.
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_mono =>?).
Time (eapply (dom_empty_inv_L (D:=gset K))).
Time eauto.
Time Qed.
Time
Lemma big_sepM2_insert \206\166 m1 m2 i x1 x2 :
  m1 !! i = None
  \226\134\146 m2 !! i = None
    \226\134\146 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 <[i:=x1]> m1;<[i:=x2]> m2, \206\166 k y1 y2)
      \226\138\163\226\138\162 \206\166 i x1 x2 \226\136\151 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2).
Time Proof.
Time (intros Hm1 Hm2).
Time rewrite /big_sepM2 -map_insert_zip_with.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite big_sepM_insert ; last  by rewrite
 map_lookup_zip_with Hm1).
Time rewrite !persistent_and_affinely_sep_l /=.
Time rewrite sep_assoc (sep_comm _ (\206\166 _ _ _)) -sep_assoc.
Time (repeat <ssreflect_plugin::ssrtclintros@0> apply sep_proper =>//).
Time (apply affinely_proper, pure_proper).
Time split.
Time -
Time (intros H1 k).
Time (destruct (decide (i = k)) as [->| ?]).
Time +
Time rewrite Hm1 Hm2 //.
Time by split; intros ?; exfalso; eapply is_Some_None.
Time +
Time specialize (H1 k).
Time revert H1.
Time rewrite !lookup_insert_ne //.
Time -
Time (intros H1 k).
Time (destruct (decide (i = k)) as [->| ?]).
Time +
Time rewrite !lookup_insert.
Time (split; by econstructor).
Time +
Time rewrite !lookup_insert_ne //.
Time Qed.
Time
Lemma big_sepM2_delete \206\166 m1 m2 i x1 x2 :
  m1 !! i = Some x1
  \226\134\146 m2 !! i = Some x2
    \226\134\146 ([\226\136\151 map] k\226\134\166x;y \226\136\136 m1;m2, \206\166 k x y)
      \226\138\163\226\138\162 \206\166 i x1 x2 \226\136\151 ([\226\136\151 map] k\226\134\166x;y \226\136\136 delete i m1;delete i m2, \206\166 k x y).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /big_sepM2 =>Hx1 Hx2).
Time rewrite !persistent_and_affinely_sep_l /=.
Time rewrite sep_assoc (sep_comm (\206\166 _ _ _)) -sep_assoc.
Time (apply sep_proper).
Time -
Time (apply affinely_proper, pure_proper).
Time split.
Time +
Time (intros Hm k).
Time (destruct (decide (i = k)) as [->| ?]).
Time {
Time rewrite !lookup_delete.
Time (split; intros []%is_Some_None).
Time }
Time rewrite !lookup_delete_ne //.
Time +
Time (intros Hm k).
Time specialize (Hm k).
Time revert Hm.
Time (destruct (decide (i = k)) as [->| ?]).
Time {
Time (intros _).
Time rewrite Hx1 Hx2.
Time (split; eauto).
Time }
Time rewrite !lookup_delete_ne //.
Time -
Time rewrite -map_delete_zip_with.
Time
(apply (big_sepM_delete (\206\187 i xx, \206\166 i xx.1 xx.2) (map_zip m1 m2) i (x1, x2))).
Time by rewrite map_lookup_zip_with Hx1 Hx2.
Time Qed.
Time
Lemma big_sepM2_insert_acc \206\166 m1 m2 i x1 x2 :
  m1 !! i = Some x1
  \226\134\146 m2 !! i = Some x2
    \226\134\146 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2)
      \226\138\162 \206\166 i x1 x2
        \226\136\151 (\226\136\128 x1' x2',
             \206\166 i x1' x2'
             -\226\136\151 [\226\136\151 map] k\226\134\166y1;y2 \226\136\136 <[i:=x1']> m1;<[i:=x2']> m2, 
             \206\166 k y1 y2).
Time Proof.
Time (intros ? ?).
Time rewrite {+1}big_sepM2_delete //.
Time (apply sep_mono; [ done |  ]).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x1').
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x2').
Time
rewrite -(insert_delete m1) -(insert_delete m2) big_sepM2_insert
 ?lookup_delete //.
Time by apply wand_intro_l.
Time Qed.
Time
Lemma big_sepM2_insert_2 \206\166 m1 m2 i x1 x2 :
  TCOr (\226\136\128 x y, Affine (\206\166 i x y)) (Absorbing (\206\166 i x1 x2))
  \226\134\146 \206\166 i x1 x2
    -\226\136\151 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2)
       -\226\136\151 [\226\136\151 map] k\226\134\166y1;y2 \226\136\136 <[i:=x1]> m1;<[i:=x2]> m2, 
       \206\166 k y1 y2.
Time Proof.
Time (intros Ha).
Time rewrite /big_sepM2.
Time (assert (TCOr (\226\136\128 x, Affine (\206\166 i x.1 x.2)) (Absorbing (\206\166 i x1 x2)))).
Time {
Time (destruct Ha; try apply _).
Time }
Time (apply wand_intro_r).
Time rewrite !persistent_and_affinely_sep_l /=.
Time rewrite (sep_comm (\206\166 _ _ _)) -sep_assoc.
Time (apply sep_mono).
Time {
Time (apply affinely_mono, pure_mono).
Time (intros Hm k).
Time (destruct (decide (i = k)) as [->| ]).
Time -
Time rewrite !lookup_insert.
Time (split; eauto).
Time -
Time rewrite !lookup_insert_ne //.
Time }
Time
rewrite
 (big_sepM_insert_2 (\206\187 k xx, \206\166 k xx.1 xx.2) (map_zip m1 m2) i (x1, x2)).
Time rewrite map_insert_zip_with.
Time (apply wand_elim_r).
Time Qed.
Time
Lemma big_sepM2_lookup_acc \206\166 m1 m2 i x1 x2 :
  m1 !! i = Some x1
  \226\134\146 m2 !! i = Some x2
    \226\134\146 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2)
      \226\138\162 \206\166 i x1 x2 \226\136\151 (\206\166 i x1 x2 -\226\136\151 [\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2).
Time Proof.
Time (intros Hm1 Hm2).
Time
(<ssreflect_plugin::ssrtclseq@0> etrans ; first 
 <ssreflect_plugin::ssrtclintros@0> apply big_sepM2_insert_acc =>//).
Time (apply sep_mono_r).
Time rewrite (forall_elim x1) (forall_elim x2).
Time rewrite !insert_id //.
Time Qed.
Time
Lemma big_sepM2_lookup \206\166 m1 m2 i x1 x2 `{!Absorbing (\206\166 i x1 x2)} :
  m1 !! i = Some x1
  \226\134\146 m2 !! i = Some x2 \226\134\146 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2) \226\138\162 \206\166 i x1 x2.
Time Proof.
Time (intros).
Time rewrite big_sepM2_lookup_acc //.
Time by rewrite sep_elim_l.
Time Qed.
Time
Lemma big_sepM2_lookup_1 \206\166 m1 m2 i x1 `{!\226\136\128 x2, Absorbing (\206\166 i x1 x2)} :
  m1 !! i = Some x1
  \226\134\146 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2)
    \226\138\162 \226\136\131 x2, \226\140\156m2 !! i = Some x2\226\140\157 \226\136\167 \206\166 i x1 x2.
Time Proof.
Time (intros Hm1).
Time rewrite /big_sepM2.
Time rewrite persistent_and_sep_1.
Time (apply wand_elim_l').
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim' =>Hm).
Time (assert (is_Some (m2 !! i)) as [x2 Hm2]).
Time {
Time (apply Hm).
Time by econstructor.
Time }
Time (apply wand_intro_r).
Time rewrite -(exist_intro x2).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite /big_sepM2
 (big_sepM_lookup _ _ i (x1, x2)) ; last  by rewrite map_lookup_zip_with Hm1
 Hm2).
Time rewrite pure_True // sep_elim_r.
Time (<ssreflect_plugin::ssrtclintros@0> apply and_intro =>//).
Time by apply pure_intro.
Time Qed.
Time
Lemma big_sepM2_lookup_2 \206\166 m1 m2 i x2 `{!\226\136\128 x1, Absorbing (\206\166 i x1 x2)} :
  m2 !! i = Some x2
  \226\134\146 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2)
    \226\138\162 \226\136\131 x1, \226\140\156m1 !! i = Some x1\226\140\157 \226\136\167 \206\166 i x1 x2.
Time Proof.
Time (intros Hm2).
Time rewrite /big_sepM2.
Time rewrite persistent_and_sep_1.
Time (apply wand_elim_l').
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim' =>Hm).
Time (assert (is_Some (m1 !! i)) as [x1 Hm1]).
Time {
Time (apply Hm).
Time by econstructor.
Time }
Time (apply wand_intro_r).
Time rewrite -(exist_intro x1).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite /big_sepM2
 (big_sepM_lookup _ _ i (x1, x2)) ; last  by rewrite map_lookup_zip_with Hm1
 Hm2).
Time rewrite pure_True // sep_elim_r.
Time (<ssreflect_plugin::ssrtclintros@0> apply and_intro =>//).
Time by apply pure_intro.
Time Qed.
Time
Lemma big_sepM2_singleton \206\166 i x1 x2 :
  ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 {[i := x1]};{[i := x2]}, \206\166 k y1 y2) \226\138\163\226\138\162 \206\166 i x1 x2.
Time Proof.
Time rewrite /big_sepM2 map_zip_with_singleton big_sepM_singleton.
Time (apply (anti_symm _)).
Time -
Time (apply and_elim_r).
Time -
Time (rewrite <- (left_id True%I (\226\136\167)%I (\206\166 i x1 x2))).
Time (<ssreflect_plugin::ssrtclintros@0> apply and_mono =>//).
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_mono =>_ k).
Time rewrite !lookup_insert_is_Some' !lookup_empty -!not_eq_None_Some.
Time naive_solver.
Time Qed.
Time
Lemma big_sepM2_fmap {A'} {B'} (f : A \226\134\146 A') (g : B \226\134\146 B')
  (\206\166 : nat \226\134\146 A' \226\134\146 B' \226\134\146 PROP) m1 m2 :
  ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 (f <$> m1);(g <$> m2), \206\166 k y1 y2)
  \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k (f y1) (g y2)).
Time Proof.
Time rewrite /big_sepM2.
Time rewrite map_fmap_zip.
Time (apply and_proper).
Time -
Time (apply pure_proper).
Time split.
Time +
Time (intros Hm k).
Time specialize (Hm k).
Time revert Hm.
Time by rewrite !lookup_fmap !fmap_is_Some.
Time +
Time (intros Hm k).
Time specialize (Hm k).
Time revert Hm.
Time by rewrite !lookup_fmap !fmap_is_Some.
Time -
Time by rewrite big_sepM_fmap.
Time Qed.
Time
Lemma big_sepM2_fmap_l {A'} (f : A \226\134\146 A') (\206\166 : nat \226\134\146 A' \226\134\146 B \226\134\146 PROP) 
  m1 m2 :
  ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 (f <$> m1);m2, \206\166 k y1 y2)
  \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k (f y1) y2).
Time Proof.
Time rewrite -{+1}(map_fmap_id m2).
Time (apply big_sepM2_fmap).
Time Qed.
Time
Lemma big_sepM2_fmap_r {B'} (g : B \226\134\146 B') (\206\166 : nat \226\134\146 A \226\134\146 B' \226\134\146 PROP) 
  m1 m2 :
  ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;(g <$> m2), \206\166 k y1 y2)
  \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 (g y2)).
Time Proof.
Time rewrite -{+1}(map_fmap_id m1).
Time (apply big_sepM2_fmap).
Time Qed.
Time
Lemma big_sepM2_sep \206\166 \206\168 m1 m2 :
  ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2 \226\136\151 \206\168 k y1 y2)
  \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2)
     \226\136\151 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\168 k y1 y2).
Time Proof.
Time rewrite /big_sepM2.
Time
rewrite -{+1}(and_idem \226\140\156\226\136\128 k : K, is_Some (m1 !! k) \226\134\148 is_Some (m2 !! k)\226\140\157%I).
Time rewrite -and_assoc.
Time rewrite !persistent_and_affinely_sep_l /=.
Time rewrite -sep_assoc.
Time (<ssreflect_plugin::ssrtclintros@0> apply sep_proper =>//).
Time rewrite sep_assoc (sep_comm _ (<affine> _)%I) -sep_assoc.
Time (<ssreflect_plugin::ssrtclintros@0> apply sep_proper =>//).
Time (apply big_sepM_sep).
Time Qed.
Time
Lemma big_sepM2_and \206\166 \206\168 m1 m2 :
  ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2 \226\136\167 \206\168 k y1 y2)
  \226\138\162 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2)
    \226\136\167 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\168 k y1 y2).
Time Proof.
Time auto using and_intro, big_sepM2_mono, and_elim_l, and_elim_r.
Time Qed.
Time
Lemma big_sepM2_persistently `{BiAffine PROP} \206\166 m1 
  m2 :
  <pers> ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2)
  \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, <pers> \206\166 k y1 y2).
Time Proof.
Time
by rewrite /big_sepM2 persistently_and persistently_pure
 big_sepM_persistently.
Time Qed.
Time
Lemma big_sepM2_forall `{BiAffine PROP} \206\166 m1 m2 :
  (\226\136\128 k x1 x2, Persistent (\206\166 k x1 x2))
  \226\134\146 ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 m1;m2, \206\166 k x1 x2)
    \226\138\163\226\138\162 \226\140\156\226\136\128 k : K, is_Some (m1 !! k) \226\134\148 is_Some (m2 !! k)\226\140\157
       \226\136\167 (\226\136\128 k x1 x2, \226\140\156m1 !! k = Some x1\226\140\157 \226\134\146 \226\140\156m2 !! k = Some x2\226\140\157 \226\134\146 \206\166 k x1 x2).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /big_sepM2 =>?).
Time (<ssreflect_plugin::ssrtclintros@0> apply and_proper =>//).
Time rewrite big_sepM_forall.
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_proper =>k).
Time (apply (anti_symm _)).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x1).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x2).
Time rewrite (forall_elim (x1, x2)).
Time rewrite impl_curry -pure_and.
Time (<ssreflect_plugin::ssrtclintros@0> apply impl_mono =>//).
Time (apply pure_mono).
Time rewrite map_lookup_zip_with.
Time by intros [-> ->].
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>[[x1 x2]]).
Time rewrite (forall_elim x1) (forall_elim x2).
Time rewrite impl_curry -pure_and.
Time (<ssreflect_plugin::ssrtclintros@0> apply impl_mono =>//).
Time (apply pure_mono).
Time rewrite map_lookup_zip_with.
Time
by
 <ssreflect_plugin::ssrtclintros@0> destruct (m1 !! k), (m2 !! k) =>/= // ?;
  simplify_eq.
Time Qed.
Time
Lemma big_sepM2_impl \206\166 \206\168 m1 m2 :
  ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2)
  -\226\136\151 \226\150\161 (\226\136\128 k x1 x2,
          \226\140\156m1 !! k = Some x1\226\140\157 \226\134\146 \226\140\156m2 !! k = Some x2\226\140\157 \226\134\146 \206\166 k x1 x2 -\226\136\151 \206\168 k x1 x2)
     -\226\136\151 [\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\168 k y1 y2.
Time Proof.
Time (apply wand_intro_l).
Time rewrite /big_sepM2.
Time rewrite !persistent_and_affinely_sep_l /=.
Time rewrite sep_assoc.
Time rewrite (sep_comm (\226\150\161 _)%I) -sep_assoc.
Time (apply sep_mono_r).
Time (apply wand_elim_r').
Time rewrite (big_sepM_impl _ (\206\187 k xx, \206\168 k xx.1 xx.2)).
Time (<ssreflect_plugin::ssrtclintros@0> apply wand_mono =>//).
Time (apply intuitionistically_mono').
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_mono =>k).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>[[x y]]).
Time rewrite (forall_elim x) (forall_elim y).
Time rewrite impl_curry -pure_and.
Time (<ssreflect_plugin::ssrtclintros@0> apply impl_mono =>//).
Time (apply pure_mono).
Time rewrite map_lookup_zip_with.
Time (destruct (m1 !! k) as [x1| ], (m2 !! k) as [x2| ]; naive_solver).
Time Qed.
Time #[global]
Instance big_sepM2_empty_persistent  \206\166:
 (Persistent ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 \226\136\133;\226\136\133, \206\166 k y1 y2)).
Time Proof.
Time rewrite big_sepM2_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepM2_persistent  \206\166 m1 m2:
 ((\226\136\128 k x1 x2, Persistent (\206\166 k x1 x2))
  \226\134\146 Persistent ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2)).
Time Proof.
Time rewrite /big_sepM2.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepM2_empty_affine  \206\166:
 (Affine ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 \226\136\133;\226\136\133, \206\166 k y1 y2)).
Time Proof.
Time rewrite big_sepM2_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepM2_affine  \206\166 m1 m2:
 ((\226\136\128 k x1 x2, Affine (\206\166 k x1 x2))
  \226\134\146 Affine ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2)).
Time Proof.
Time rewrite /big_sepM2.
Time (apply _).
Time Qed.
Time End map2.
Time Section gset.
Time Context `{Countable A}.
Time Implicit Type X : gset A.
Time Implicit Type \206\166 : A \226\134\146 PROP.
Time
Lemma big_sepS_mono \206\166 \206\168 X :
  (\226\136\128 x, x \226\136\136 X \226\134\146 \206\166 x \226\138\162 \206\168 x) \226\134\146 ([\226\136\151 set] x \226\136\136 X, \206\166 x) \226\138\162 [\226\136\151 set] x \226\136\136 X, \206\168 x.
Time Proof.
Time (intros).
Time (apply big_opS_forall; apply _ || auto).
Time Qed.
Time
Lemma big_sepS_proper \206\166 \206\168 X :
  (\226\136\128 x, x \226\136\136 X \226\134\146 \206\166 x \226\138\163\226\138\162 \206\168 x) \226\134\146 ([\226\136\151 set] x \226\136\136 X, \206\166 x) \226\138\163\226\138\162 ([\226\136\151 set] x \226\136\136 X, \206\168 x).
Time Proof.
Time (apply big_opS_proper).
Time Qed.
Time
Lemma big_sepS_subseteq `{BiAffine PROP} \206\166 X Y :
  Y \226\138\134 X \226\134\146 ([\226\136\151 set] x \226\136\136 X, \206\166 x) \226\138\162 [\226\136\151 set] x \226\136\136 Y, \206\166 x.
Time Proof.
Time (intros).
Time by apply big_sepL_submseteq, elements_submseteq.
Time Qed.
Time #[global]
Instance big_sepS_mono' :
 (Proper (pointwise_relation _ (\226\138\162) ==> (=) ==> (\226\138\162))
    (big_opS (@bi_sep PROP) (A:=A))).
Time Proof.
Time (intros f g Hf m ? <-).
Time by apply big_sepS_mono.
Time Qed.
Time Lemma big_sepS_empty \206\166 : ([\226\136\151 set] x \226\136\136 \226\136\133, \206\166 x) \226\138\163\226\138\162 emp.
Time Proof.
Time by rewrite big_opS_empty.
Time Qed.
Time Lemma big_sepS_empty' `{!BiAffine PROP} P \206\166 : P \226\138\162 [\226\136\151 set] x \226\136\136 \226\136\133, \206\166 x.
Time Proof.
Time rewrite big_sepS_empty.
Time apply : {}affine {}.
Time Qed.
Time
Lemma big_sepS_insert \206\166 X x :
  x \226\136\137 X \226\134\146 ([\226\136\151 set] y \226\136\136 ({[x]} \226\136\170 X), \206\166 y) \226\138\163\226\138\162 \206\166 x \226\136\151 ([\226\136\151 set] y \226\136\136 X, \206\166 y).
Time Proof.
Time (apply big_opS_insert).
Time Qed.
Time
Lemma big_sepS_fn_insert {B} (\206\168 : A \226\134\146 B \226\134\146 PROP) f 
  X x b :
  x \226\136\137 X
  \226\134\146 ([\226\136\151 set] y \226\136\136 ({[x]} \226\136\170 X), \206\168 y (<[x:=b]> f y))
    \226\138\163\226\138\162 \206\168 x b \226\136\151 ([\226\136\151 set] y \226\136\136 X, \206\168 y (f y)).
Time Proof.
Time (apply big_opS_fn_insert).
Time Qed.
Time
Lemma big_sepS_fn_insert' \206\166 X x P :
  x \226\136\137 X \226\134\146 ([\226\136\151 set] y \226\136\136 ({[x]} \226\136\170 X), <[x:=P]> \206\166 y) \226\138\163\226\138\162 P \226\136\151 ([\226\136\151 set] y \226\136\136 X, \206\166 y).
Time Proof.
Time (apply big_opS_fn_insert').
Time Qed.
Time
Lemma big_sepS_union \206\166 X Y :
  X ## Y
  \226\134\146 ([\226\136\151 set] y \226\136\136 (X \226\136\170 Y), \206\166 y) \226\138\163\226\138\162 ([\226\136\151 set] y \226\136\136 X, \206\166 y) \226\136\151 ([\226\136\151 set] y \226\136\136 Y, \206\166 y).
Time Proof.
Time (apply big_opS_union).
Time Qed.
Time
Lemma big_sepS_delete \206\166 X x :
  x \226\136\136 X \226\134\146 ([\226\136\151 set] y \226\136\136 X, \206\166 y) \226\138\163\226\138\162 \206\166 x \226\136\151 ([\226\136\151 set] y \226\136\136 (X \226\136\150 {[x]}), \206\166 y).
Time Proof.
Time (apply big_opS_delete).
Time Qed.
Time
Lemma big_sepS_elem_of \206\166 X x `{!Absorbing (\206\166 x)} :
  x \226\136\136 X \226\134\146 ([\226\136\151 set] y \226\136\136 X, \206\166 y) \226\138\162 \206\166 x.
Time Proof.
Time (intros).
Time rewrite big_sepS_delete //.
Time by rewrite sep_elim_l.
Time Qed.
Time
Lemma big_sepS_elem_of_acc \206\166 X x :
  x \226\136\136 X \226\134\146 ([\226\136\151 set] y \226\136\136 X, \206\166 y) \226\138\162 \206\166 x \226\136\151 (\206\166 x -\226\136\151 [\226\136\151 set] y \226\136\136 X, \206\166 y).
Time Proof.
Time (intros).
Time rewrite big_sepS_delete //.
Time by apply sep_mono_r, wand_intro_l.
Time Qed.
Time Lemma big_sepS_singleton \206\166 x : ([\226\136\151 set] y \226\136\136 {[x]}, \206\166 y) \226\138\163\226\138\162 \206\166 x.
Time Proof.
Time (apply big_opS_singleton).
Time Qed.
Time
Lemma big_sepS_filter' (P : A \226\134\146 Prop) `{\226\136\128 x, Decision (P x)} 
  \206\166 X :
  ([\226\136\151 set] y \226\136\136 filter P X, \206\166 y)
  \226\138\163\226\138\162 ([\226\136\151 set] y \226\136\136 X, if decide (P y) then \206\166 y else emp).
Time Proof.
Time (induction X as [| x X ? IH] using set_ind_L).
Time {
Time by rewrite filter_empty_L !big_sepS_empty.
Time }
Time (destruct (decide (P x))).
Time -
Time rewrite filter_union_L filter_singleton_L //.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite !big_sepS_insert // ; last 
 set_solver).
Time by rewrite decide_True // IH.
Time -
Time rewrite filter_union_L filter_singleton_not_L // left_id_L.
Time by rewrite !big_sepS_insert // decide_False // IH left_id.
Time Qed.
Time
Lemma big_sepS_filter_acc' (P : A \226\134\146 Prop) `{\226\136\128 y, Decision (P y)} 
  \206\166 X Y :
  (\226\136\128 y, y \226\136\136 Y \226\134\146 P y \226\134\146 y \226\136\136 X)
  \226\134\146 ([\226\136\151 set] y \226\136\136 X, \206\166 y)
    -\226\136\151 ([\226\136\151 set] y \226\136\136 Y, if decide (P y) then \206\166 y else emp)
       \226\136\151 (([\226\136\151 set] y \226\136\136 Y, if decide (P y) then \206\166 y else emp)
          -\226\136\151 [\226\136\151 set] y \226\136\136 X, \206\166 y).
Time Proof.
Time (intros ?).
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (proj1 (subseteq_disjoint_union_L (filter P Y) X)) as (Z, (->, ?))
 ; first  set_solver).
Time rewrite big_sepS_union // big_sepS_filter'.
Time by apply sep_mono_r, wand_intro_l.
Time Qed.
Time
Lemma big_sepS_filter `{BiAffine PROP} (P : A \226\134\146 Prop) 
  `{\226\136\128 x, Decision (P x)} \206\166 X :
  ([\226\136\151 set] y \226\136\136 filter P X, \206\166 y) \226\138\163\226\138\162 ([\226\136\151 set] y \226\136\136 X, \226\140\156P y\226\140\157 \226\134\146 \206\166 y).
Time Proof.
Time setoid_rewrite  <- decide_emp.
Time (apply big_sepS_filter').
Time Qed.
Time
Lemma big_sepS_filter_acc `{BiAffine PROP} (P : A \226\134\146 Prop)
  `{\226\136\128 y, Decision (P y)} \206\166 X Y :
  (\226\136\128 y, y \226\136\136 Y \226\134\146 P y \226\134\146 y \226\136\136 X)
  \226\134\146 ([\226\136\151 set] y \226\136\136 X, \206\166 y)
    -\226\136\151 ([\226\136\151 set] y \226\136\136 Y, \226\140\156P y\226\140\157 \226\134\146 \206\166 y)
       \226\136\151 (([\226\136\151 set] y \226\136\136 Y, \226\140\156P y\226\140\157 \226\134\146 \206\166 y) -\226\136\151 [\226\136\151 set] y \226\136\136 X, \206\166 y).
Time Proof.
Time (intros).
Time setoid_rewrite  <- decide_emp.
Time by apply big_sepS_filter_acc'.
Time Qed.
Time
Lemma big_sepS_sep \206\166 \206\168 X :
  ([\226\136\151 set] y \226\136\136 X, \206\166 y \226\136\151 \206\168 y) \226\138\163\226\138\162 ([\226\136\151 set] y \226\136\136 X, \206\166 y) \226\136\151 ([\226\136\151 set] y \226\136\136 X, \206\168 y).
Time Proof.
Time (apply big_opS_op).
Time Qed.
Time
Lemma big_sepS_and \206\166 \206\168 X :
  ([\226\136\151 set] y \226\136\136 X, \206\166 y \226\136\167 \206\168 y) \226\138\162 ([\226\136\151 set] y \226\136\136 X, \206\166 y) \226\136\167 ([\226\136\151 set] y \226\136\136 X, \206\168 y).
Time Proof.
Time auto using and_intro, big_sepS_mono, and_elim_l, and_elim_r.
Time Qed.
Time
Lemma big_sepS_persistently `{BiAffine PROP} \206\166 X :
  <pers> ([\226\136\151 set] y \226\136\136 X, \206\166 y) \226\138\163\226\138\162 ([\226\136\151 set] y \226\136\136 X, <pers> \206\166 y).
Time Proof.
Time (apply (big_opS_commute _)).
Time Qed.
Time
Lemma big_sepS_forall `{BiAffine PROP} \206\166 X :
  (\226\136\128 x, Persistent (\206\166 x)) \226\134\146 ([\226\136\151 set] x \226\136\136 X, \206\166 x) \226\138\163\226\138\162 (\226\136\128 x, \226\140\156x \226\136\136 X\226\140\157 \226\134\146 \206\166 x).
Time Proof.
Time (intros).
Time (apply (anti_symm _)).
Time {
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply impl_intro_l, pure_elim_l =>?; by
  apply : {}big_sepS_elem_of {}).
Time }
Time
(induction X as [| x X ? IH] using set_ind_L; auto using big_sepS_empty').
Time rewrite big_sepS_insert // -persistent_and_sep.
Time (apply and_intro).
Time -
Time
by <ssreflect_plugin::ssrtclseq@0> rewrite (forall_elim x) pure_True
 ?True_impl ; last  set_solver.
Time -
Time rewrite -IH.
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_mono =>y).
Time
(<ssreflect_plugin::ssrtclintros@0> apply impl_intro_l, pure_elim_l =>?).
Time
by <ssreflect_plugin::ssrtclseq@0> rewrite pure_True ?True_impl ; last 
 set_solver.
Time Qed.
Time
Lemma big_sepS_impl \206\166 \206\168 X :
  ([\226\136\151 set] x \226\136\136 X, \206\166 x) -\226\136\151 \226\150\161 (\226\136\128 x, \226\140\156x \226\136\136 X\226\140\157 \226\134\146 \206\166 x -\226\136\151 \206\168 x) -\226\136\151 [\226\136\151 set] x \226\136\136 X, \206\168 x.
Time Proof.
Time (apply wand_intro_l).
Time (induction X as [| x X ? IH] using set_ind_L).
Time {
Time by rewrite sep_elim_r.
Time }
Time rewrite !big_sepS_insert // intuitionistically_sep_dup.
Time rewrite -assoc [(\226\150\161 _ \226\136\151 _)%I]comm -!assoc assoc.
Time (apply sep_mono).
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (forall_elim x) pure_True ; last 
 set_solver).
Time by rewrite True_impl intuitionistically_elim wand_elim_l.
Time -
Time rewrite comm -IH /=.
Time (apply sep_mono_l, affinely_mono, persistently_mono).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_mono =>y).
Time
(<ssreflect_plugin::ssrtclintros@0> apply impl_intro_l, pure_elim_l =>?).
Time
by <ssreflect_plugin::ssrtclseq@0> rewrite pure_True ?True_impl ; last 
 set_solver.
Time Qed.
Time #[global]
Instance big_sepS_empty_persistent  \206\166: (Persistent ([\226\136\151 set] x \226\136\136 \226\136\133, \206\166 x)).
Time Proof.
Time rewrite /big_opS elements_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepS_persistent  \206\166 X:
 ((\226\136\128 x, Persistent (\206\166 x)) \226\134\146 Persistent ([\226\136\151 set] x \226\136\136 X, \206\166 x)).
Time Proof.
Time rewrite /big_opS.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepS_empty_affine  \206\166: (Affine ([\226\136\151 set] x \226\136\136 \226\136\133, \206\166 x)).
Time Proof.
Time rewrite /big_opS elements_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepS_affine  \206\166 X:
 ((\226\136\128 x, Affine (\206\166 x)) \226\134\146 Affine ([\226\136\151 set] x \226\136\136 X, \206\166 x)).
Time Proof.
Time rewrite /big_opS.
Time (apply _).
Time Qed.
Time End gset.
Time
Lemma big_sepM_dom `{Countable K} {A} (\206\166 : K \226\134\146 PROP) 
  (m : gmap K A) : ([\226\136\151 map] k\226\134\166_ \226\136\136 m, \206\166 k) \226\138\163\226\138\162 ([\226\136\151 set] k \226\136\136 dom _ m, \206\166 k).
Time Proof.
Time (apply big_opM_dom).
Time Qed.
Time Section gmultiset.
Time Context `{Countable A}.
Time Implicit Type X : gmultiset A.
Time Implicit Type \206\166 : A \226\134\146 PROP.
Time
Lemma big_sepMS_mono \206\166 \206\168 X :
  (\226\136\128 x, x \226\136\136 X \226\134\146 \206\166 x \226\138\162 \206\168 x) \226\134\146 ([\226\136\151 mset] x \226\136\136 X, \206\166 x) \226\138\162 [\226\136\151 mset] x \226\136\136 X, \206\168 x.
Time Proof.
Time (intros).
Time (apply big_opMS_forall; apply _ || auto).
Time Qed.
Time
Lemma big_sepMS_proper \206\166 \206\168 X :
  (\226\136\128 x, x \226\136\136 X \226\134\146 \206\166 x \226\138\163\226\138\162 \206\168 x) \226\134\146 ([\226\136\151 mset] x \226\136\136 X, \206\166 x) \226\138\163\226\138\162 ([\226\136\151 mset] x \226\136\136 X, \206\168 x).
Time Proof.
Time (apply big_opMS_proper).
Time Qed.
Time
Lemma big_sepMS_subseteq `{BiAffine PROP} \206\166 X Y :
  Y \226\138\134 X \226\134\146 ([\226\136\151 mset] x \226\136\136 X, \206\166 x) \226\138\162 [\226\136\151 mset] x \226\136\136 Y, \206\166 x.
Time Proof.
Time (intros).
Time by apply big_sepL_submseteq, gmultiset_elements_submseteq.
Time Qed.
Time #[global]
Instance big_sepMS_mono' :
 (Proper (pointwise_relation _ (\226\138\162) ==> (=) ==> (\226\138\162))
    (big_opMS (@bi_sep PROP) (A:=A))).
Time Proof.
Time (intros f g Hf m ? <-).
Time by apply big_sepMS_mono.
Time Qed.
Time Lemma big_sepMS_empty \206\166 : ([\226\136\151 mset] x \226\136\136 \226\136\133, \206\166 x) \226\138\163\226\138\162 emp.
Time Proof.
Time by rewrite big_opMS_empty.
Time Qed.
Time Lemma big_sepMS_empty' `{!BiAffine PROP} P \206\166 : P \226\138\162 [\226\136\151 mset] x \226\136\136 \226\136\133, \206\166 x.
Time Proof.
Time rewrite big_sepMS_empty.
Time apply : {}affine {}.
Time Qed.
Time
Lemma big_sepMS_disj_union \206\166 X Y :
  ([\226\136\151 mset] y \226\136\136 (X \226\138\142 Y), \206\166 y)
  \226\138\163\226\138\162 ([\226\136\151 mset] y \226\136\136 X, \206\166 y) \226\136\151 ([\226\136\151 mset] y \226\136\136 Y, \206\166 y).
Time Proof.
Time (apply big_opMS_disj_union).
Time Qed.
Time
Lemma big_sepMS_delete \206\166 X x :
  x \226\136\136 X \226\134\146 ([\226\136\151 mset] y \226\136\136 X, \206\166 y) \226\138\163\226\138\162 \206\166 x \226\136\151 ([\226\136\151 mset] y \226\136\136 (X \226\136\150 {[x]}), \206\166 y).
Time Proof.
Time (apply big_opMS_delete).
Time Qed.
Time
Lemma big_sepMS_elem_of \206\166 X x `{!Absorbing (\206\166 x)} :
  x \226\136\136 X \226\134\146 ([\226\136\151 mset] y \226\136\136 X, \206\166 y) \226\138\162 \206\166 x.
Time Proof.
Time (intros).
Time rewrite big_sepMS_delete //.
Time by rewrite sep_elim_l.
Time Qed.
Time
Lemma big_sepMS_elem_of_acc \206\166 X x :
  x \226\136\136 X \226\134\146 ([\226\136\151 mset] y \226\136\136 X, \206\166 y) \226\138\162 \206\166 x \226\136\151 (\206\166 x -\226\136\151 [\226\136\151 mset] y \226\136\136 X, \206\166 y).
Time Proof.
Time (intros).
Time rewrite big_sepMS_delete //.
Time by apply sep_mono_r, wand_intro_l.
Time Qed.
Time Lemma big_sepMS_singleton \206\166 x : ([\226\136\151 mset] y \226\136\136 {[x]}, \206\166 y) \226\138\163\226\138\162 \206\166 x.
Time Proof.
Time (apply big_opMS_singleton).
Time Qed.
Time
Lemma big_sepMS_sep \206\166 \206\168 X :
  ([\226\136\151 mset] y \226\136\136 X, \206\166 y \226\136\151 \206\168 y)
  \226\138\163\226\138\162 ([\226\136\151 mset] y \226\136\136 X, \206\166 y) \226\136\151 ([\226\136\151 mset] y \226\136\136 X, \206\168 y).
Time Proof.
Time (apply big_opMS_op).
Time Qed.
Time
Lemma big_sepMS_and \206\166 \206\168 X :
  ([\226\136\151 mset] y \226\136\136 X, \206\166 y \226\136\167 \206\168 y) \226\138\162 ([\226\136\151 mset] y \226\136\136 X, \206\166 y) \226\136\167 ([\226\136\151 mset] y \226\136\136 X, \206\168 y).
Time Proof.
Time auto using and_intro, big_sepMS_mono, and_elim_l, and_elim_r.
Time Qed.
Time
Lemma big_sepMS_persistently `{BiAffine PROP} \206\166 X :
  <pers> ([\226\136\151 mset] y \226\136\136 X, \206\166 y) \226\138\163\226\138\162 ([\226\136\151 mset] y \226\136\136 X, <pers> \206\166 y).
Time Proof.
Time (apply (big_opMS_commute _)).
Time Qed.
Time #[global]
Instance big_sepMS_empty_persistent  \206\166: (Persistent ([\226\136\151 mset] x \226\136\136 \226\136\133, \206\166 x)).
Time Proof.
Time rewrite /big_opMS gmultiset_elements_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepMS_persistent  \206\166 X:
 ((\226\136\128 x, Persistent (\206\166 x)) \226\134\146 Persistent ([\226\136\151 mset] x \226\136\136 X, \206\166 x)).
Time Proof.
Time rewrite /big_opMS.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepMS_empty_affine  \206\166: (Affine ([\226\136\151 mset] x \226\136\136 \226\136\133, \206\166 x)).
Time Proof.
Time rewrite /big_opMS gmultiset_elements_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepMS_affine  \206\166 X:
 ((\226\136\128 x, Affine (\206\166 x)) \226\134\146 Affine ([\226\136\151 mset] x \226\136\136 X, \206\166 x)).
Time Proof.
Time rewrite /big_opMS.
Time (apply _).
Time Qed.
Time End gmultiset.
Time End bi_big_op.
Time Section sbi_big_op.
Time Context {PROP : sbi}.
Time Implicit Types Ps Qs : list PROP.
Time Implicit Type A : Type.
Time Section list.
Time Context {A : Type}.
Time Implicit Type l : list A.
Time Implicit Types \206\166 \206\168 : nat \226\134\146 A \226\134\146 PROP.
Time
Lemma big_sepL_later `{BiAffine PROP} \206\166 l :
  \226\150\183 ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166x \226\136\136 l, \226\150\183 \206\166 k x).
Time Proof.
Time (apply (big_opL_commute _)).
Time Qed.
Time
Lemma big_sepL_later_2 \206\166 l :
  ([\226\136\151 list] k\226\134\166x \226\136\136 l, \226\150\183 \206\166 k x) \226\138\162 \226\150\183 ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x).
Time Proof.
Time by rewrite (big_opL_commute _).
Time Qed.
Time
Lemma big_sepL_laterN `{BiAffine PROP} \206\166 n l :
  \226\150\183^n ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166x \226\136\136 l, \226\150\183^n \206\166 k x).
Time Proof.
Time (apply (big_opL_commute _)).
Time Qed.
Time
Lemma big_sepL_laterN_2 \206\166 n l :
  ([\226\136\151 list] k\226\134\166x \226\136\136 l, \226\150\183^n \206\166 k x) \226\138\162 \226\150\183^n ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x).
Time Proof.
Time by rewrite (big_opL_commute _).
Time Qed.
Time #[global]
Instance big_sepL_nil_timeless  `{!Timeless (emp%I : PROP)} 
 \206\166: (Timeless ([\226\136\151 list] k\226\134\166x \226\136\136 [], \206\166 k x)).
Time Proof.
Time (simpl; apply _).
Time Qed.
Time #[global]
Instance big_sepL_timeless  `{!Timeless (emp%I : PROP)} 
 \206\166 l: ((\226\136\128 k x, Timeless (\206\166 k x)) \226\134\146 Timeless ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x)).
Time Proof.
Time revert \206\166.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>\206\166 ? /=;
  apply _).
Time Qed.
Time #[global]
Instance big_sepL_timeless_id  `{!Timeless (emp%I : PROP)} 
 Ps: (TCForall Timeless Ps \226\134\146 Timeless ([\226\136\151] Ps)).
Time Proof.
Time (induction 1; simpl; apply _).
Time Qed.
Time End list.
Time Section list2.
Time Context {A B : Type}.
Time Implicit Types \206\166 \206\168 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP.
Time
Lemma big_sepL2_later_1 `{BiAffine PROP} \206\166 l1 l2 :
  \226\150\183 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)
  \226\138\162 \226\151\135 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \226\150\183 \206\166 k y1 y2).
Time Proof.
Time rewrite !big_sepL2_alt later_and big_sepL_later (timeless \226\140\156_\226\140\157%I).
Time rewrite except_0_and.
Time auto using and_mono, except_0_intro.
Time Qed.
Time
Lemma big_sepL2_later_2 \206\166 l1 l2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \226\150\183 \206\166 k y1 y2)
  \226\138\162 \226\150\183 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2).
Time Proof.
Time rewrite !big_sepL2_alt later_and big_sepL_later_2.
Time auto using and_mono, later_intro.
Time Qed.
Time
Lemma big_sepL2_laterN_2 \206\166 n l1 l2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \226\150\183^n \206\166 k y1 y2)
  \226\138\162 \226\150\183^n ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2).
Time Proof.
Time rewrite !big_sepL2_alt laterN_and big_sepL_laterN_2.
Time auto using and_mono, laterN_intro.
Time Qed.
Time
Lemma big_sepL2_flip \206\166 l1 l2 :
  ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l2;l1, \206\166 k y2 y1)
  \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2).
Time Proof.
Time revert \206\166 l2.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l1 as [| x1 l1 IH] =>\206\166 -
  [|x2 l2] //=; simplify_eq).
Time by rewrite IH.
Time Qed.
Time #[global]
Instance big_sepL2_nil_timeless  `{!Timeless (emp%I : PROP)} 
 \206\166: (Timeless ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 [];[], \206\166 k y1 y2)).
Time Proof.
Time (simpl; apply _).
Time Qed.
Time #[global]
Instance big_sepL2_timeless  `{!Timeless (emp%I : PROP)} 
 \206\166 l1 l2:
 ((\226\136\128 k x1 x2, Timeless (\206\166 k x1 x2))
  \226\134\146 Timeless ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)).
Time Proof.
Time rewrite big_sepL2_alt.
Time (apply _).
Time Qed.
Time End list2.
Time Section gmap.
Time Context `{Countable K} {A : Type}.
Time Implicit Type m : gmap K A.
Time Implicit Types \206\166 \206\168 : K \226\134\146 A \226\134\146 PROP.
Time
Lemma big_sepM_later `{BiAffine PROP} \206\166 m :
  \226\150\183 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x) \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \226\150\183 \206\166 k x).
Time Proof.
Time (apply (big_opM_commute _)).
Time Qed.
Time
Lemma big_sepM_later_2 \206\166 m :
  ([\226\136\151 map] k\226\134\166x \226\136\136 m, \226\150\183 \206\166 k x) \226\138\162 \226\150\183 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x).
Time Proof.
Time by rewrite big_opM_commute.
Time Qed.
Time
Lemma big_sepM_laterN `{BiAffine PROP} \206\166 n m :
  \226\150\183^n ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x) \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \226\150\183^n \206\166 k x).
Time Proof.
Time (apply (big_opM_commute _)).
Time Qed.
Time
Lemma big_sepM_laterN_2 \206\166 n m :
  ([\226\136\151 map] k\226\134\166x \226\136\136 m, \226\150\183^n \206\166 k x) \226\138\162 \226\150\183^n ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x).
Time Proof.
Time by rewrite big_opM_commute.
Time Qed.
Time #[global]
Instance big_sepM_empty_timeless  `{!Timeless (emp%I : PROP)} 
 \206\166: (Timeless ([\226\136\151 map] k\226\134\166x \226\136\136 \226\136\133, \206\166 k x)).
Time Proof.
Time rewrite /big_opM map_to_list_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepM_timeless  `{!Timeless (emp%I : PROP)} 
 \206\166 m: ((\226\136\128 k x, Timeless (\206\166 k x)) \226\134\146 Timeless ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x)).
Time Proof.
Time (intros).
Time
(<ssreflect_plugin::ssrtclintros@0> apply big_sepL_timeless =>_ 
  [? ?]; apply _).
Time Qed.
Time End gmap.
Time Section gmap2.
Time Context `{Countable K} {A B : Type}.
Time Implicit Types \206\166 \206\168 : K \226\134\146 A \226\134\146 B \226\134\146 PROP.
Time
Lemma big_sepM2_later_1 `{BiAffine PROP} \206\166 m1 m2 :
  \226\150\183 ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 m1;m2, \206\166 k x1 x2)
  \226\138\162 \226\151\135 ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 m1;m2, \226\150\183 \206\166 k x1 x2).
Time Proof.
Time rewrite /big_sepM2 later_and (timeless \226\140\156_\226\140\157%I).
Time rewrite big_sepM_later except_0_and.
Time auto using and_mono_r, except_0_intro.
Time Qed.
Time
Lemma big_sepM2_later_2 \206\166 m1 m2 :
  ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 m1;m2, \226\150\183 \206\166 k x1 x2)
  \226\138\162 \226\150\183 ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 m1;m2, \206\166 k x1 x2).
Time Proof.
Time rewrite /big_sepM2 later_and -(later_intro \226\140\156_\226\140\157%I).
Time (apply and_mono_r).
Time by rewrite big_opM_commute.
Time Qed.
Time
Lemma big_sepM2_laterN_2 \206\166 n m1 m2 :
  ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 m1;m2, \226\150\183^n \206\166 k x1 x2)
  \226\138\162 \226\150\183^n ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 m1;m2, \206\166 k x1 x2).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> induction n as [| n IHn] ; first  done).
Time rewrite later_laterN -IHn -big_sepM2_later_2.
Time (apply big_sepM2_mono).
Time eauto.
Time Qed.
Time
Lemma big_sepM2_flip \206\166 m1 m2 :
  ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m2;m1, \206\166 k y2 y1)
  \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166y1;y2 \226\136\136 m1;m2, \206\166 k y1 y2).
Time Proof.
Time rewrite /big_sepM2.
Time (apply and_proper; [ apply pure_proper; naive_solver |  ]).
Time rewrite -map_zip_with_flip map_zip_with_map_zip big_sepM_fmap.
Time (apply big_sepM_proper).
Time by intros k [b a].
Time Qed.
Time #[global]
Instance big_sepM2_empty_timeless  `{!Timeless (emp%I : PROP)} 
 \206\166: (Timeless ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 \226\136\133;\226\136\133, \206\166 k x1 x2)).
Time Proof.
Time rewrite /big_sepM2 map_zip_with_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepM2_timeless  `{!Timeless (emp%I : PROP)} 
 \206\166 m1 m2:
 ((\226\136\128 k x1 x2, Timeless (\206\166 k x1 x2))
  \226\134\146 Timeless ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 m1;m2, \206\166 k x1 x2)).
Time Proof.
Time (intros).
Time rewrite /big_sepM2.
Time (apply _).
Time Qed.
Time End gmap2.
Time Section gset.
Time Context `{Countable A}.
Time Implicit Type X : gset A.
Time Implicit Type \206\166 : A \226\134\146 PROP.
Time
Lemma big_sepS_later `{BiAffine PROP} \206\166 X :
  \226\150\183 ([\226\136\151 set] y \226\136\136 X, \206\166 y) \226\138\163\226\138\162 ([\226\136\151 set] y \226\136\136 X, \226\150\183 \206\166 y).
Time Proof.
Time (apply (big_opS_commute _)).
Time Qed.
Time
Lemma big_sepS_later_2 \206\166 X : ([\226\136\151 set] y \226\136\136 X, \226\150\183 \206\166 y) \226\138\162 \226\150\183 ([\226\136\151 set] y \226\136\136 X, \206\166 y).
Time Proof.
Time by rewrite big_opS_commute.
Time Qed.
Time
Lemma big_sepS_laterN `{BiAffine PROP} \206\166 n X :
  \226\150\183^n ([\226\136\151 set] y \226\136\136 X, \206\166 y) \226\138\163\226\138\162 ([\226\136\151 set] y \226\136\136 X, \226\150\183^n \206\166 y).
Time Proof.
Time (apply (big_opS_commute _)).
Time Qed.
Time
Lemma big_sepS_laterN_2 \206\166 n X :
  ([\226\136\151 set] y \226\136\136 X, \226\150\183^n \206\166 y) \226\138\162 \226\150\183^n ([\226\136\151 set] y \226\136\136 X, \206\166 y).
Time Proof.
Time by rewrite big_opS_commute.
Time Qed.
Time #[global]
Instance big_sepS_empty_timeless  `{!Timeless (emp%I : PROP)} 
 \206\166: (Timeless ([\226\136\151 set] x \226\136\136 \226\136\133, \206\166 x)).
Time Proof.
Time rewrite /big_opS elements_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepS_timeless  `{!Timeless (emp%I : PROP)} 
 \206\166 X: ((\226\136\128 x, Timeless (\206\166 x)) \226\134\146 Timeless ([\226\136\151 set] x \226\136\136 X, \206\166 x)).
Time Proof.
Time rewrite /big_opS.
Time (apply _).
Time Qed.
Time End gset.
Time Section gmultiset.
Time Context `{Countable A}.
Time Implicit Type X : gmultiset A.
Time Implicit Type \206\166 : A \226\134\146 PROP.
Time
Lemma big_sepMS_later `{BiAffine PROP} \206\166 X :
  \226\150\183 ([\226\136\151 mset] y \226\136\136 X, \206\166 y) \226\138\163\226\138\162 ([\226\136\151 mset] y \226\136\136 X, \226\150\183 \206\166 y).
Time Proof.
Time (apply (big_opMS_commute _)).
Time Qed.
Time
Lemma big_sepMS_later_2 \206\166 X :
  ([\226\136\151 mset] y \226\136\136 X, \226\150\183 \206\166 y) \226\138\162 \226\150\183 ([\226\136\151 mset] y \226\136\136 X, \206\166 y).
Time Proof.
Time by rewrite big_opMS_commute.
Time Qed.
Time
Lemma big_sepMS_laterN `{BiAffine PROP} \206\166 n X :
  \226\150\183^n ([\226\136\151 mset] y \226\136\136 X, \206\166 y) \226\138\163\226\138\162 ([\226\136\151 mset] y \226\136\136 X, \226\150\183^n \206\166 y).
Time Proof.
Time (apply (big_opMS_commute _)).
Time Qed.
Time
Lemma big_sepMS_laterN_2 \206\166 n X :
  ([\226\136\151 mset] y \226\136\136 X, \226\150\183^n \206\166 y) \226\138\162 \226\150\183^n ([\226\136\151 mset] y \226\136\136 X, \206\166 y).
Time Proof.
Time by rewrite big_opMS_commute.
Time Qed.
Time #[global]
Instance big_sepMS_empty_timeless  `{!Timeless (emp%I : PROP)} 
 \206\166: (Timeless ([\226\136\151 mset] x \226\136\136 \226\136\133, \206\166 x)).
Time Proof.
Time rewrite /big_opMS gmultiset_elements_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepMS_timeless  `{!Timeless (emp%I : PROP)} 
 \206\166 X: ((\226\136\128 x, Timeless (\206\166 x)) \226\134\146 Timeless ([\226\136\151 mset] x \226\136\136 X, \206\166 x)).
Time Proof.
Time rewrite /big_opMS.
Time (apply _).
Time Qed.
Time End gmultiset.
Time End sbi_big_op.

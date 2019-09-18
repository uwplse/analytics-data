Time From iris.algebra Require Export cmra.
Time Set Default Proof Using "Type".
Time
Definition local_update {A : cmraT} (x y : A * A) :=
  \226\136\128 n mz, \226\156\147{n} x.1 \226\134\146 x.1 \226\137\161{n}\226\137\161 x.2 \226\139\133? mz \226\134\146 \226\156\147{n} y.1 \226\136\167 y.1 \226\137\161{n}\226\137\161 y.2 \226\139\133? mz.
Time Instance: (Params (@local_update) 1) := { }.
Time Infix "~l~>" := local_update (at level 70).
Time Section updates.
Time Context {A : cmraT}.
Time Implicit Types x y : A.
Time #[global]
Instance local_update_proper :
 (Proper ((\226\137\161) ==> (\226\137\161) ==> iff) (@local_update A)).
Time Proof.
Time (unfold local_update).
Time by repeat intro; setoid_subst.
Time Qed.
Time #[global]Instance local_update_preorder : (PreOrder (@local_update A)).
Time Proof.
Time (split; unfold local_update; red; naive_solver).
Time Qed.
Time
Lemma exclusive_local_update `{!Exclusive y} x x' :
  \226\156\147 x' \226\134\146 (x, y) ~l~> (x', x').
Time Proof.
Time (intros ? n mz Hxv Hx; simpl in *).
Time
(move : {}Hxv {}; rewrite Hx; <ssreflect_plugin::ssrtclintros@0> move
   {}=>/exclusiveN_opM =>{+}->; split; auto).
Time by apply cmra_valid_validN.
Time Qed.
Time
Lemma op_local_update x y z :
  (\226\136\128 n, \226\156\147{n} x \226\134\146 \226\156\147{n} (z \226\139\133 x)) \226\134\146 (x, y) ~l~> (z \226\139\133 x, z \226\139\133 y).
Time Proof.
Time (intros Hv n mz Hxv Hx; simpl in *; split; [ by auto |  ]).
Time by rewrite Hx -cmra_op_opM_assoc.
Time Qed.
Time
Lemma op_local_update_discrete `{!CmraDiscrete A} 
  x y z : (\226\156\147 x \226\134\146 \226\156\147 (z \226\139\133 x)) \226\134\146 (x, y) ~l~> (z \226\139\133 x, z \226\139\133 y).
Time Proof.
Time (intros; <ssreflect_plugin::ssrtclintros@0> apply op_local_update =>n).
Time by rewrite -!(cmra_discrete_valid_iff n).
Time Qed.
Time
Lemma op_local_update_frame x y x' y' yf :
  (x, y) ~l~> (x', y') \226\134\146 (x, y \226\139\133 yf) ~l~> (x', y' \226\139\133 yf).
Time Proof.
Time (intros Hup n mz Hxv Hx; simpl in *).
Time
(destruct (Hup n (Some (yf \226\139\133? mz)));
  [ done | by rewrite /= -cmra_op_opM_assoc |  ]).
Time by rewrite cmra_op_opM_assoc.
Time Qed.
Time
Lemma cancel_local_update x y z `{!Cancelable x} : (x \226\139\133 y, x \226\139\133 z) ~l~> (y, z).
Time Proof.
Time (intros n f ? Heq).
Time
(<ssreflect_plugin::ssrtclseq@0> split ; first  by eapply cmra_validN_op_r).
Time (<ssreflect_plugin::ssrtclseq@0> apply (cancelableN x) ; first  done).
Time by rewrite -cmra_op_opM_assoc.
Time Qed.
Time Lemma replace_local_update x y `{!IdFree x} : \226\156\147 y \226\134\146 (x, x) ~l~> (y, y).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> intros ? n mz ? Heq; simpl in *; split ;
 first  by apply cmra_valid_validN).
Time (destruct mz as [z| ]; [  | done ]).
Time by destruct (id_freeN_r n n x z).
Time Qed.
Time
Lemma core_id_local_update x y z `{!CoreId y} :
  y \226\137\188 x \226\134\146 (x, z) ~l~> (x, z \226\139\133 y).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> intros Hincl n mf ? Heq; simpl in *; split ;
 first  done).
Time rewrite [x]core_id_extract // Heq.
Time (<ssreflect_plugin::ssrtclseq@0> destruct mf as [f| ] ; last  done).
Time (simpl).
Time rewrite -assoc [f \226\139\133 y]comm assoc //.
Time Qed.
Time
Lemma local_update_discrete `{!CmraDiscrete A} (x y x' y' : A) :
  (x, y) ~l~> (x', y') \226\134\148 (\226\136\128 mz, \226\156\147 x \226\134\146 x \226\137\161 y \226\139\133? mz \226\134\146 \226\156\147 x' \226\136\167 x' \226\137\161 y' \226\139\133? mz).
Time Proof.
Time rewrite /local_update /=.
Time setoid_rewrite  <- cmra_discrete_valid_iff.
Time setoid_rewrite  <- (\206\187 n, discrete_iff n x).
Time setoid_rewrite  <- (\206\187 n, discrete_iff n x').
Time naive_solver eauto using 0.
Time Qed.
Time
Lemma local_update_valid0 x y x' y' :
  (\226\156\147{0} x \226\134\146 \226\156\147{0} y \226\134\146 x \226\137\161{0}\226\137\161 y \226\136\168 y \226\137\188{0} x \226\134\146 (x, y) ~l~> (x', y'))
  \226\134\146 (x, y) ~l~> (x', y').
Time Proof.
Time (intros Hup n mz Hmz Hz; simpl in *).
Time (apply Hup; auto).
Time -
Time by <ssreflect_plugin::ssrtclseq@0> apply (cmra_validN_le n) ; last  lia.
Time -
Time (<ssreflect_plugin::ssrtclseq@0> apply (cmra_validN_le n) ; last  lia).
Time (move : {}Hmz {}; rewrite Hz).
Time (destruct mz; simpl; eauto using cmra_validN_op_l).
Time -
Time (destruct mz as [z| ]).
Time +
Time right.
Time exists z.
Time (apply dist_le with n; auto with lia).
Time +
Time left.
Time (apply dist_le with n; auto with lia).
Time Qed.
Time
Lemma local_update_valid `{!CmraDiscrete A} x y x' 
  y' :
  (\226\156\147 x \226\134\146 \226\156\147 y \226\134\146 x \226\137\161 y \226\136\168 y \226\137\188 x \226\134\146 (x, y) ~l~> (x', y')) \226\134\146 (x, y) ~l~> (x', y').
Time Proof.
Time
rewrite !(cmra_discrete_valid_iff 0) (cmra_discrete_included_iff 0)
 (discrete_iff 0).
Time (apply local_update_valid0).
Time Qed.
Time
Lemma local_update_total_valid0 `{!CmraTotal A} x 
  y x' y' :
  (\226\156\147{0} x \226\134\146 \226\156\147{0} y \226\134\146 y \226\137\188{0} x \226\134\146 (x, y) ~l~> (x', y')) \226\134\146 (x, y) ~l~> (x', y').
Time Proof.
Time (intros Hup).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_valid0 =>? ? 
  [Hx|?]; apply Hup; auto).
Time by rewrite Hx.
Time Qed.
Time
Lemma local_update_total_valid `{!CmraTotal A} `{!CmraDiscrete A} 
  x y x' y' :
  (\226\156\147 x \226\134\146 \226\156\147 y \226\134\146 y \226\137\188 x \226\134\146 (x, y) ~l~> (x', y')) \226\134\146 (x, y) ~l~> (x', y').
Time Proof.
Time rewrite !(cmra_discrete_valid_iff 0) (cmra_discrete_included_iff 0).
Time (apply local_update_total_valid0).
Time Qed.
Time End updates.
Time Section updates_unital.
Time Context {A : ucmraT}.
Time Implicit Types x y : A.
Time
Lemma local_update_unital x y x' y' :
  (x, y) ~l~> (x', y')
  \226\134\148 (\226\136\128 n z, \226\156\147{n} x \226\134\146 x \226\137\161{n}\226\137\161 y \226\139\133 z \226\134\146 \226\156\147{n} x' \226\136\167 x' \226\137\161{n}\226\137\161 y' \226\139\133 z).
Time Proof.
Time split.
Time -
Time (intros Hup n z).
Time (apply (Hup _ (Some z))).
Time -
Time (intros Hup n [z| ]; simpl; [ by auto |  ]).
Time rewrite -(right_id \206\181 op y) -(right_id \206\181 op y').
Time auto.
Time Qed.
Time
Lemma local_update_unital_discrete `{!CmraDiscrete A} 
  (x y x' y' : A) :
  (x, y) ~l~> (x', y') \226\134\148 (\226\136\128 z, \226\156\147 x \226\134\146 x \226\137\161 y \226\139\133 z \226\134\146 \226\156\147 x' \226\136\167 x' \226\137\161 y' \226\139\133 z).
Time Proof.
Time rewrite local_update_discrete.
Time split.
Time -
Time (intros Hup z).
Time (apply (Hup (Some z))).
Time -
Time (intros Hup [z| ]; simpl; [ by auto |  ]).
Time rewrite -(right_id \206\181 op y) -(right_id \206\181 op y').
Time auto.
Time Qed.
Time
Lemma cancel_local_update_unit x y `{!Cancelable x} : (x \226\139\133 y, x) ~l~> (y, \206\181).
Time Proof.
Time rewrite -{+2}(right_id \206\181 op x).
Time by apply cancel_local_update.
Time Qed.
Time End updates_unital.
Time
Lemma prod_local_update {A B : cmraT} (x y x' y' : A * B) :
  (x.1, y.1) ~l~> (x'.1, y'.1)
  \226\134\146 (x.2, y.2) ~l~> (x'.2, y'.2) \226\134\146 (x, y) ~l~> (x', y').
Time Proof.
Time (intros Hup1 Hup2 n mz [? ?] [? ?]; simpl in *).
Time (destruct (Hup1 n (fst <$> mz)); [ done | by destruct mz |  ]).
Time (destruct (Hup2 n (snd <$> mz)); [ done | by destruct mz |  ]).
Time by destruct mz.
Time Qed.
Time
Lemma prod_local_update' {A B : cmraT} (x1 y1 x1' y1' : A)
  (x2 y2 x2' y2' : B) :
  (x1, y1) ~l~> (x1', y1')
  \226\134\146 (x2, y2) ~l~> (x2', y2')
    \226\134\146 ((x1, x2), (y1, y2)) ~l~> ((x1', x2'), (y1', y2')).
Time Proof.
Time (intros).
Time by apply prod_local_update.
Time Qed.
Time
Lemma prod_local_update_1 {A B : cmraT} (x1 y1 x1' y1' : A) 
  (x2 y2 : B) :
  (x1, y1) ~l~> (x1', y1') \226\134\146 ((x1, x2), (y1, y2)) ~l~> ((x1', x2), (y1', y2)).
Time Proof.
Time (intros).
Time by apply prod_local_update.
Time Qed.
Time
Lemma prod_local_update_2 {A B : cmraT} (x1 y1 : A) 
  (x2 y2 x2' y2' : B) :
  (x2, y2) ~l~> (x2', y2') \226\134\146 ((x1, x2), (y1, y2)) ~l~> ((x1, x2'), (y1, y2')).
Time Proof.
Time (intros).
Time by apply prod_local_update.
Time Qed.
Time
Lemma option_local_update {A : cmraT} (x y x' y' : A) :
  (x, y) ~l~> (x', y') \226\134\146 (Some x, Some y) ~l~> (Some x', Some y').
Time Proof.
Time (intros Hup).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mz Hxv Hx;
  simpl in *).
Time (<ssreflect_plugin::ssrtclseq@0> destruct (Hup n mz) ; first  done).
Time {
Time (destruct mz as [?| ]; inversion_clear Hx; auto).
Time }
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  done).
Time (destruct mz as [?| ]; constructor; auto).
Time Qed.
Time
Lemma alloc_option_local_update {A : cmraT} (x : A) 
  y : \226\156\147 x \226\134\146 (None, y) ~l~> (Some x, Some x).
Time Proof.
Time move  {}=>Hx.
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n z _ /= Heq).
Time split.
Time {
Time rewrite Some_validN.
Time (apply cmra_valid_validN).
Time done.
Time }
Time (<ssreflect_plugin::ssrtclseq@0> destruct z as [z| ] ; last  done).
Time (destruct y; inversion Heq).
Time Qed.
Time
Lemma delete_option_local_update {A : cmraT} (x : option A) 
  (y : A) : Exclusive y \226\134\146 (x, Some y) ~l~> (None, None).
Time Proof.
Time move  {}=>Hex.
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n z /= Hy
 Heq).
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  done).
Time (<ssreflect_plugin::ssrtclseq@0> destruct z as [z| ] ; last  done).
Time exfalso.
Time move : {}Hy {}.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite Heq /= -Some_op =>Hy).
Time (eapply Hex).
Time (eapply cmra_validN_le).
Time (eapply Hy).
Time lia.
Time Qed.
Time
Lemma nat_local_update (x y x' y' : nat) :
  x + y' = x' + y \226\134\146 (x, y) ~l~> (x', y').
Time Proof.
Time
(intros ? ?; <ssreflect_plugin::ssrtclintros@0>
  apply local_update_unital_discrete =>z _).
Time (cbv-[minus plus]; lia).
Time Qed.
Time
Lemma mnat_local_update (x y x' : mnatUR) : x \226\137\164 x' \226\134\146 (x, y) ~l~> (x', x').
Time Proof.
Time
(intros ? ?; <ssreflect_plugin::ssrtclintros@0>
  apply local_update_unital_discrete =>z _).
Time (cbv-[max]; lia).
Time Qed.

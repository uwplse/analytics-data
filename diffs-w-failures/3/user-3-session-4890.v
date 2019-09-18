Time From iris.algebra Require Export cmra updates.
Time From iris.bi Require Import notation.
Time From stdpp Require Import finite.
Time From Coq.Init Require Import Nat.
Time Set Default Proof Using "Type".
Time #[local]Hint Extern 1 (_ \226\137\188 _) => (etrans; [ eassumption |  ]): core.
Time #[local]Hint Extern 1 (_ \226\137\188 _) => (etrans; [  | eassumption ]): core.
Time #[local]Hint Extern 10 (_ \226\137\164 _) => lia: core.
Time
Record uPred (M : ucmraT) : Type :=
 UPred {uPred_holds :> nat \226\134\146 M \226\134\146 Prop;
        uPred_mono :
         forall n1 n2 x1 x2,
         uPred_holds n1 x1 \226\134\146 x1 \226\137\188{n1} x2 \226\134\146 n2 \226\137\164 n1 \226\134\146 uPred_holds n2 x2}.
Time Bind Scope bi_scope with uPred.
Time Arguments uPred_holds {_} _%I _ _ : simpl never.
Time Add Printing Constructor uPred.
Time Instance: (Params (@uPred_holds) 3) := { }.
Time Section cofe.
Time Context {M : ucmraT}.
Time
Inductive uPred_equiv' (P Q : uPred M) : Prop :={uPred_in_equiv :
                                                 \226\136\128 n x,
                                                 \226\156\147{n} x \226\134\146 P n x \226\134\148 Q n x}.
Time Instance uPred_equiv : (Equiv (uPred M)) := uPred_equiv'.
Time
Inductive uPred_dist' (n : nat) (P Q : uPred M) : Prop :={
 uPred_in_dist : \226\136\128 n' x, n' \226\137\164 n \226\134\146 \226\156\147{n'} x \226\134\146 P n' x \226\134\148 Q n' x}.
Time Instance uPred_dist : (Dist (uPred M)) := uPred_dist'.
Time Definition uPred_ofe_mixin : OfeMixin (uPred M).
Time Proof.
Time split.
Time -
Time (intros P Q; split).
Time +
Time
by
 intros HPQ n; <ssreflect_plugin::ssrtclintros@0> split =>i x ? ?; apply HPQ.
Time +
Time
(intros HPQ; <ssreflect_plugin::ssrtclintros@0> split =>n x ?;
  apply HPQ with n; auto).
Time -
Time (intros n; split).
Time +
Time by intros P; <ssreflect_plugin::ssrtclintros@0> split =>x i.
Time +
Time
by
 intros P Q HPQ; <ssreflect_plugin::ssrtclintros@0> split =>x i ? ?; symmetry;
  apply HPQ.
Time +
Time
(intros P Q Q' HP HQ; <ssreflect_plugin::ssrtclintros@0> split =>i x ? ?).
Time by trans Q i x; [ apply HP | apply HQ ].
Time -
Time
(intros n P Q HPQ; <ssreflect_plugin::ssrtclintros@0> split =>i x ? ?;
  apply HPQ; auto).
Time Qed.
Time Canonical Structure uPredO : ofeT := OfeT (uPred M) uPred_ofe_mixin.
Time #[program]
Definition uPred_compl : Compl uPredO :=
  \206\187 c, {| uPred_holds := fun n x => \226\136\128 n', n' \226\137\164 n \226\134\146 \226\156\147{n'} x \226\134\146 c n' n' x |}.
Time Next Obligation.
Time move  {}=>/= c n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv.
Time (eapply uPred_mono).
Time
(<ssreflect_plugin::ssrtclintros@0>
  eapply HP, cmra_validN_includedN, cmra_includedN_le =>//; lia).
Time (<ssreflect_plugin::ssrtclintros@0> eapply cmra_includedN_le =>//; lia).
Time done.
Time Qed.
Time #[global, program]
Instance uPred_cofe : (Cofe uPredO) := {| compl := uPred_compl |}.
Time Next Obligation.
Time (intros n c; <ssreflect_plugin::ssrtclintros@0> split =>i x Hin Hv).
Time (etrans; [  | by symmetry; apply (chain_cauchy c i n) ]).
Time (<ssreflect_plugin::ssrtclintros@0> split =>H; [ by apply H |  ]).
Time (repeat intro).
Time (<ssreflect_plugin::ssrtclintros@0> apply (chain_cauchy c n' i) =>//).
Time by eapply uPred_mono.
Time Qed.
Time End cofe.
Time Arguments uPredO : clear implicits.
Time Instance uPred_ne  {M} (P : uPred M) n: (Proper (dist n ==> iff) (P n)).
Time Proof.
Time
(intros x1 x2 Hx; <ssreflect_plugin::ssrtclintros@0> split =>?;
  eapply uPred_mono; eauto; by rewrite Hx).
Time Qed.
Time
Instance uPred_proper  {M} (P : uPred M) n: (Proper ((\226\137\161) ==> iff) (P n)).
Time Proof.
Time by intros x1 x2 Hx; apply uPred_ne, equiv_dist.
Time Qed.
Time
Lemma uPred_holds_ne {M} (P Q : uPred M) n1 n2 x :
  P \226\137\161{n2}\226\137\161 Q \226\134\146 n2 \226\137\164 n1 \226\134\146 \226\156\147{n2} x \226\134\146 Q n1 x \226\134\146 P n2 x.
Time Proof.
Time (intros [Hne] ? ? ?).
Time (eapply Hne; try done).
Time eauto using uPred_mono, cmra_validN_le.
Time Qed.
Time
Lemma uPred_alt {M : ucmraT} (P : nat \226\134\146 M \226\134\146 Prop) :
  (\226\136\128 n1 n2 x1 x2, P n1 x1 \226\134\146 x1 \226\137\188{n1} x2 \226\134\146 n2 \226\137\164 n1 \226\134\146 P n2 x2)
  \226\134\148 (\226\136\128 x n1 n2, n2 \226\137\164 n1 \226\134\146 P n1 x \226\134\146 P n2 x)
    \226\136\167 (\226\136\128 n x1 x2, x1 \226\137\161{n}\226\137\161 x2 \226\134\146 \226\136\128 m, m \226\137\164 n \226\134\146 P m x1 \226\134\148 P m x2)
      \226\136\167 (\226\136\128 n x1 x2, x1 \226\137\188{n} x2 \226\134\146 \226\136\128 m, m \226\137\164 n \226\134\146 P m x1 \226\134\146 P m x2).
Time Proof.
Time (assert (\226\136\128 n1 n2 (x1 x2 : M), n2 \226\137\164 n1 \226\134\146 x1 \226\137\161{n1}\226\137\161 x2 \226\134\146 x1 \226\137\188{n2} x2)).
Time {
Time (intros ? ? ? ? ? H).
Time (<ssreflect_plugin::ssrtclseq@0> eapply cmra_includedN_le ; last  done).
Time by rewrite H.
Time }
Time split.
Time -
Time (intros Hupred).
Time (repeat split; eauto using cmra_includedN_le).
Time -
Time (intros (Hdown, (_, Hmono)) **).
Time (eapply Hmono; [ done.. | idtac ]).
Time (eapply Hdown; done).
Time Qed.
Time #[program]
Definition uPred_map {M1 M2 : ucmraT} (f : M2 -n> M1) 
  `{!CmraMorphism f} (P : uPred M1) : uPred M2 :=
  {| uPred_holds := fun n x => P n (f x) |}.
Time Next Obligation.
Time naive_solver eauto using uPred_mono, cmra_morphism_monotoneN.
Time Qed.
Time
Instance uPred_map_ne  {M1 M2 : ucmraT} (f : M2 -n> M1) 
 `{!CmraMorphism f} n: (Proper (dist n ==> dist n) (uPred_map f)).
Time Proof.
Time (intros x1 x2 Hx; <ssreflect_plugin::ssrtclintros@0> split =>n' y ? ?).
Time (split; apply Hx; auto using cmra_morphism_validN).
Time Qed.
Time Lemma uPred_map_id {M : ucmraT} (P : uPred M) : uPred_map cid P \226\137\161 P.
Time Proof.
Time by <ssreflect_plugin::ssrtclintros@0> split =>n x ?.
Time Qed.
Time
Lemma uPred_map_compose {M1 M2 M3 : ucmraT} (f : M1 -n> M2) 
  (g : M2 -n> M3) `{!CmraMorphism f} `{!CmraMorphism g} 
  (P : uPred M3) : uPred_map (g \226\151\142 f) P \226\137\161 uPred_map f (uPred_map g P).
Time Proof.
Time by <ssreflect_plugin::ssrtclintros@0> split =>n x Hx.
Time Qed.
Time
Lemma uPred_map_ext {M1 M2 : ucmraT} (f g : M1 -n> M2) 
  `{!CmraMorphism f} `{!CmraMorphism g} :
  (\226\136\128 x, f x \226\137\161 g x) \226\134\146 \226\136\128 x, uPred_map f x \226\137\161 uPred_map g x.
Time Proof.
Time
(intros Hf P; <ssreflect_plugin::ssrtclintros@0> split =>n x Hx /=; by
  rewrite /uPred_holds /= Hf).
Time Qed.
Time
Definition uPredO_map {M1 M2 : ucmraT} (f : M2 -n> M1) 
  `{!CmraMorphism f} : uPredO M1 -n> uPredO M2 :=
  OfeMor (uPred_map f : uPredO M1 \226\134\146 uPredO M2).
Time
Lemma uPredO_map_ne {M1 M2 : ucmraT} (f g : M2 -n> M1) 
  `{!CmraMorphism f} `{!CmraMorphism g} n :
  f \226\137\161{n}\226\137\161 g \226\134\146 uPredO_map f \226\137\161{n}\226\137\161 uPredO_map g.
Time Proof.
Time
by <ssreflect_plugin::ssrtclseq@0>
 intros Hfg P; <ssreflect_plugin::ssrtclintros@0> split =>n' y ? ?; rewrite
  /uPred_holds /= (dist_le _ _ _ _ (Hfg y)) ; last  lia.
Time Qed.
Time #[program]
Definition uPredOF (F : urFunctor) : oFunctor :=
  {|
  oFunctor_car := fun A _ B _ => uPredO (urFunctor_car F B A);
  oFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  uPredO_map (urFunctor_map F (fg.2, fg.1)) |}.
Time Next Obligation.
Time (intros F A1 ? A2 ? B1 ? B2 ? n P Q HPQ).
Time (apply uPredO_map_ne, urFunctor_ne; split; by apply HPQ).
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? P; simpl).
Time rewrite -{+2}(uPred_map_id P).
Time (<ssreflect_plugin::ssrtclintros@0> apply uPred_map_ext =>y).
Time by rewrite urFunctor_id.
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' P; simpl).
Time rewrite -uPred_map_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply uPred_map_ext =>y;
  apply urFunctor_compose).
Time Qed.
Time
Instance uPredOF_contractive  F:
 (urFunctorContractive F \226\134\146 oFunctorContractive (uPredOF F)).
Time Proof.
Time (intros ? A1 ? A2 ? B1 ? B2 ? n P Q HPQ).
Time (apply uPredO_map_ne, urFunctor_contractive).
Time (destruct n; split; by apply HPQ).
Time Qed.
Time
Inductive uPred_entails {M} (P Q : uPred M) : Prop :={
 uPred_in_entails : \226\136\128 n x, \226\156\147{n} x \226\134\146 P n x \226\134\146 Q n x}.
Time Hint Resolve uPred_mono: uPred_def.
Time #[program]
Definition uPred_pure_def {M} (\207\134 : Prop) : uPred M :=
  {| uPred_holds := fun n x => \207\134 |}.
Time Solve Obligations with done.
Time Definition uPred_pure_aux : seal (@uPred_pure_def).
Time by eexists.
Time Qed.
Time Definition uPred_pure {M} := uPred_pure_aux.(unseal) M.
Time
Definition uPred_pure_eq : @uPred_pure = @uPred_pure_def :=
  uPred_pure_aux.(seal_eq).
Time #[program]
Definition uPred_and_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds := fun n x => P n x \226\136\167 Q n x |}.
Time Solve Obligations with naive_solver eauto  2 with uPred_def.
Time Definition uPred_and_aux : seal (@uPred_and_def).
Time by eexists.
Time Qed.
Time Definition uPred_and {M} := uPred_and_aux.(unseal) M.
Time
Definition uPred_and_eq : @uPred_and = @uPred_and_def :=
  uPred_and_aux.(seal_eq).
Time #[program]
Definition uPred_or_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds := fun n x => P n x \226\136\168 Q n x |}.
Time Solve Obligations with naive_solver eauto  2 with uPred_def.
Time Definition uPred_or_aux : seal (@uPred_or_def).
Time by eexists.
Time Qed.
Time Definition uPred_or {M} := uPred_or_aux.(unseal) M.
Time
Definition uPred_or_eq : @uPred_or = @uPred_or_def := uPred_or_aux.(seal_eq).
Time #[program]
Definition uPred_impl_def {M} (P Q : uPred M) : uPred M :=
  {|
  uPred_holds := fun n x =>
                 \226\136\128 n' x', x \226\137\188 x' \226\134\146 n' \226\137\164 n \226\134\146 \226\156\147{n'} x' \226\134\146 P n' x' \226\134\146 Q n' x' |}.
Time Next Obligation.
Time
(intros M P Q n1 n1' x1 x1' HPQ [x2 Hx1'] Hn1 n2 x3 [x4 Hx3] ?; simpl in *).
Time (rewrite Hx3 (dist_le _ _ _ _ Hx1'); auto).
Time (intros ? ?).
Time (eapply HPQ; auto).
Time (exists (x2 \226\139\133 x4); by rewrite assoc).
Time Qed.
Time Definition uPred_impl_aux : seal (@uPred_impl_def).
Time by eexists.
Time Qed.
Time Definition uPred_impl {M} := uPred_impl_aux.(unseal) M.
Time
Definition uPred_impl_eq : @uPred_impl = @uPred_impl_def :=
  uPred_impl_aux.(seal_eq).
Time #[program]
Definition uPred_forall_def {M} {A} (\206\168 : A \226\134\146 uPred M) : 
  uPred M := {| uPred_holds := fun n x => \226\136\128 a, \206\168 a n x |}.
Time Solve Obligations with naive_solver eauto  2 with uPred_def.
Time Definition uPred_forall_aux : seal (@uPred_forall_def).
Time by eexists.
Time Qed.
Time Definition uPred_forall {M} {A} := uPred_forall_aux.(unseal) M A.
Time
Definition uPred_forall_eq : @uPred_forall = @uPred_forall_def :=
  uPred_forall_aux.(seal_eq).
Time #[program]
Definition uPred_exist_def {M} {A} (\206\168 : A \226\134\146 uPred M) : 
  uPred M := {| uPred_holds := fun n x => \226\136\131 a, \206\168 a n x |}.
Time Solve Obligations with naive_solver eauto  2 with uPred_def.
Time Definition uPred_exist_aux : seal (@uPred_exist_def).
Time by eexists.
Time Qed.
Time Definition uPred_exist {M} {A} := uPred_exist_aux.(unseal) M A.
Time
Definition uPred_exist_eq : @uPred_exist = @uPred_exist_def :=
  uPred_exist_aux.(seal_eq).
Time #[program]
Definition uPred_internal_eq_def {M} {A : ofeT} (a1 a2 : A) : 
  uPred M := {| uPred_holds := fun n x => a1 \226\137\161{n}\226\137\161 a2 |}.
Time Solve Obligations with naive_solver eauto  2 using (dist_le (A:=A)).
Time Definition uPred_internal_eq_aux : seal (@uPred_internal_eq_def).
Time by eexists.
Time Qed.
Time
Definition uPred_internal_eq {M} {A} := uPred_internal_eq_aux.(unseal) M A.
Time
Definition uPred_internal_eq_eq :
  @uPred_internal_eq = @uPred_internal_eq_def :=
  uPred_internal_eq_aux.(seal_eq).
Time #[program]
Definition uPred_sep_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds := fun n x => \226\136\131 x1 x2, x \226\137\161{n}\226\137\161 x1 \226\139\133 x2 \226\136\167 P n x1 \226\136\167 Q n x2 |}.
Time Next Obligation.
Time (intros M P Q n1 n2 x y (x1, (x2, (Hx, (?, ?)))) [z Hy] Hn).
Time
(exists x1,(x2 \226\139\133 z); split_and ?; eauto using uPred_mono, cmra_includedN_l).
Time (eapply dist_le, Hn).
Time by rewrite Hy Hx assoc.
Time Qed.
Time Definition uPred_sep_aux : seal (@uPred_sep_def).
Time by eexists.
Time Qed.
Time Definition uPred_sep {M} := uPred_sep_aux.(unseal) M.
Time
Definition uPred_sep_eq : @uPred_sep = @uPred_sep_def :=
  uPred_sep_aux.(seal_eq).
Time #[program]
Definition uPred_wand_def {M} (P Q : uPred M) : uPred M :=
  {|
  uPred_holds := fun n x =>
                 \226\136\128 n' x', n' \226\137\164 n \226\134\146 \226\156\147{n'} (x \226\139\133 x') \226\134\146 P n' x' \226\134\146 Q n' (x \226\139\133 x') |}.
Time Next Obligation.
Time (intros M P Q n1 n1' x1 x1' HPQ ? Hn n3 x3 ? ? ?; simpl in *).
Time
(eapply uPred_mono with n3 (x1 \226\139\133 x3); eauto
  using cmra_validN_includedN, cmra_monoN_r, cmra_includedN_le).
Time Qed.
Time Definition uPred_wand_aux : seal (@uPred_wand_def).
Time by eexists.
Time Qed.
Time Definition uPred_wand {M} := uPred_wand_aux.(unseal) M.
Time
Definition uPred_wand_eq : @uPred_wand = @uPred_wand_def :=
  uPred_wand_aux.(seal_eq).
Time #[program]
Definition uPred_plainly_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds := fun n x => P n \206\181 |}.
Time
Solve Obligations with naive_solver eauto using uPred_mono, ucmra_unit_validN.
Time Definition uPred_plainly_aux : seal (@uPred_plainly_def).
Time by eexists.
Time Qed.
Time Definition uPred_plainly {M} := uPred_plainly_aux.(unseal) M.
Time
Definition uPred_plainly_eq : @uPred_plainly = @uPred_plainly_def :=
  uPred_plainly_aux.(seal_eq).
Time #[program]
Definition uPred_persistently_def {M} (P : uPred M) : 
  uPred M := {| uPred_holds := fun n x => P n (core x) |}.
Time Next Obligation.
Time (intros M; naive_solver eauto using uPred_mono, @cmra_core_monoN).
Time Qed.
Time Definition uPred_persistently_aux : seal (@uPred_persistently_def).
Time by eexists.
Time Qed.
Time Definition uPred_persistently {M} := uPred_persistently_aux.(unseal) M.
Time
Definition uPred_persistently_eq :
  @uPred_persistently = @uPred_persistently_def :=
  uPred_persistently_aux.(seal_eq).
Time #[program]
Definition uPred_later_def {M} (P : uPred M) : uPred M :=
  {|
  uPred_holds := fun n x => match n with
                            | 0 => True
                            | S n' => P n' x
                            end |}.
Time Next Obligation.
Time
(intros M P [| n1] [| n2] x1 x2; eauto using uPred_mono, cmra_includedN_S
  with lia).
Time Qed.
Time Definition uPred_later_aux : seal (@uPred_later_def).
Time by eexists.
Time Qed.
Time Definition uPred_later {M} := uPred_later_aux.(unseal) M.
Time
Definition uPred_later_eq : @uPred_later = @uPred_later_def :=
  uPred_later_aux.(seal_eq).
Time #[program]
Definition uPred_ownM_def {M : ucmraT} (a : M) : uPred M :=
  {| uPred_holds := fun n x => a \226\137\188{n} x |}.
Time Next Obligation.
Time (intros M a n1 n2 x1 x [a' Hx1] [x2 Hx] Hn).
Time (<ssreflect_plugin::ssrtclintros@0> eapply cmra_includedN_le =>//).
Time exists (a' \226\139\133 x2).
Time by rewrite Hx (assoc op) Hx1.
Time Qed.
Time Definition uPred_ownM_aux : seal (@uPred_ownM_def).
Time by eexists.
Time Qed.
Time Definition uPred_ownM {M} := uPred_ownM_aux.(unseal) M.
Time
Definition uPred_ownM_eq : @uPred_ownM = @uPred_ownM_def :=
  uPred_ownM_aux.(seal_eq).
Time #[program]
Definition uPred_cmra_valid_def {M} {A : cmraT} (a : A) : 
  uPred M := {| uPred_holds := fun n x => \226\156\147{n} a |}.
Time Solve Obligations with naive_solver eauto  2 using cmra_validN_le.
Time Definition uPred_cmra_valid_aux : seal (@uPred_cmra_valid_def).
Time by eexists.
Time Qed.
Time
Definition uPred_cmra_valid {M} {A} := uPred_cmra_valid_aux.(unseal) M A.
Time
Definition uPred_cmra_valid_eq : @uPred_cmra_valid = @uPred_cmra_valid_def :=
  uPred_cmra_valid_aux.(seal_eq).
Time #[program]
Definition uPred_bupd_def {M} (Q : uPred M) : uPred M :=
  {|
  uPred_holds := fun n x =>
                 \226\136\128 k yf,
                   k \226\137\164 n \226\134\146 \226\156\147{k} (x \226\139\133 yf) \226\134\146 \226\136\131 x', \226\156\147{k} (x' \226\139\133 yf) \226\136\167 Q k x' |}.
Time Next Obligation.
Time (intros M Q n1 n2 x1 x2 HQ [x3 Hx] Hn k yf Hk).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (dist_le _ _ _ _ Hx) ; last  lia).
Time (intros Hxy).
Time
(destruct (HQ k (x3 \226\139\133 yf)) as (x', (?, ?)); [ auto | by rewrite assoc |  ]).
Time
(<ssreflect_plugin::ssrtclseq@0> exists (x' \226\139\133 x3); split ; first  by rewrite
 -assoc).
Time eauto using uPred_mono, cmra_includedN_l.
Time Qed.
Time Definition uPred_bupd_aux : seal (@uPred_bupd_def).
Time by eexists.
Time Qed.
Time Definition uPred_bupd {M} := uPred_bupd_aux.(unseal) M.
Time
Definition uPred_bupd_eq : @uPred_bupd = @uPred_bupd_def :=
  uPred_bupd_aux.(seal_eq).
Time Notation "\226\156\147 x" := (uPred_cmra_valid x) (at level 20) : bi_scope.
Time Module uPred_primitive.
Time
Definition unseal_eqs :=
  (uPred_pure_eq, uPred_and_eq, uPred_or_eq, uPred_impl_eq, uPred_forall_eq,
  uPred_exist_eq, uPred_internal_eq_eq, uPred_sep_eq, uPred_wand_eq,
  uPred_plainly_eq, uPred_persistently_eq, uPred_later_eq, uPred_ownM_eq,
  uPred_cmra_valid_eq, @uPred_bupd_eq).
Time Ltac unseal := rewrite !unseal_eqs /=.
Time Section primitive.
Time Context {M : ucmraT}.
Time Implicit Type \207\134 : Prop.
Time Implicit Types P Q : uPred M.
Time Implicit Type A : Type.
Time Arguments uPred_holds {_} !_ _ _ /.
Time Hint Immediate uPred_in_entails: core.
Time Notation "P \226\138\162 Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
Time Notation "(\226\138\162)" := (@uPred_entails M) (only parsing) : stdpp_scope.
Time Notation "P \226\138\163\226\138\162 Q" := (@uPred_equiv M P%I Q%I) : stdpp_scope.
Time Notation "(\226\138\163\226\138\162)" := (@uPred_equiv M) (only parsing) : stdpp_scope.
Time Notation "'True'" := (uPred_pure True) : bi_scope.
Time Notation "'False'" := (uPred_pure False) : bi_scope.
Time Notation "'\226\140\156' \207\134 '\226\140\157'" := (uPred_pure \207\134%type%stdpp) : bi_scope.
Time Infix "\226\136\167" := uPred_and : bi_scope.
Time Infix "\226\136\168" := uPred_or : bi_scope.
Time Infix "\226\134\146" := uPred_impl : bi_scope.
Time
Notation "\226\136\128 x .. y , P" :=
  (uPred_forall (\206\187 x, .. (uPred_forall (\206\187 y, P)) ..)) : bi_scope.
Time
Notation "\226\136\131 x .. y , P" :=
  (uPred_exist (\206\187 x, .. (uPred_exist (\206\187 y, P)) ..)) : bi_scope.
Time Infix "\226\136\151" := uPred_sep : bi_scope.
Time Infix "-\226\136\151" := uPred_wand : bi_scope.
Time Notation "\226\150\161 P" := (uPred_persistently P) : bi_scope.
Time Notation "\226\150\160 P" := (uPred_plainly P) : bi_scope.
Time Notation "x \226\137\161 y" := (uPred_internal_eq x y) : bi_scope.
Time Notation "\226\150\183 P" := (uPred_later P) : bi_scope.
Time Notation "|==> P" := (uPred_bupd P) : bi_scope.
Time Lemma entails_po : PreOrder (\226\138\162).
Time Proof.
Time split.
Time -
Time by intros P; <ssreflect_plugin::ssrtclintros@0> split =>x i.
Time -
Time
by
 intros P Q Q' HP HQ; <ssreflect_plugin::ssrtclintros@0> split =>x i ? ?;
  apply HQ, HP.
Time Qed.
Time Lemma entails_anti_sym : AntiSymm (\226\138\163\226\138\162) (\226\138\162).
Time Proof.
Time
(intros P Q HPQ HQP; <ssreflect_plugin::ssrtclintros@0> split =>x n; by
  split; [ apply HPQ | apply HQP ]).
Time Qed.
Time Lemma equiv_spec P Q : (P \226\138\163\226\138\162 Q) \226\134\148 (P \226\138\162 Q) \226\136\167 (Q \226\138\162 P).
Time Proof.
Time split.
Time -
Time
(intros HPQ; split; <ssreflect_plugin::ssrtclintros@0> split =>x i; apply HPQ).
Time -
Time (intros [? ?]).
Time exact : {}entails_anti_sym {}.
Time Qed.
Time
Lemma entails_lim (cP cQ : chain (uPredO M)) :
  (\226\136\128 n, cP n \226\138\162 cQ n) \226\134\146 compl cP \226\138\162 compl cQ.
Time Proof.
Time (intros Hlim; <ssreflect_plugin::ssrtclintros@0> split =>n m ? HP).
Time (eapply uPred_holds_ne, Hlim, HP; rewrite ?conv_compl; eauto).
Time Qed.
Time Lemma pure_ne n : Proper (iff ==> dist n) (@uPred_pure M).
Time Proof.
Time (intros \207\1341 \207\1342 H\207\134).
Time
by unseal; <ssreflect_plugin::ssrtclintros@0> split =>- [|m] ?; try apply H\207\134.
Time Qed.
Time Lemma and_ne : NonExpansive2 (@uPred_and M).
Time Proof.
Time
(intros n P P' HP Q Q' HQ; unseal; <ssreflect_plugin::ssrtclintros@0> split
  =>x n' ? ?).
Time (split; (intros [? ?]; split; [ by apply HP | by apply HQ ])).
Time Qed.
Time Lemma or_ne : NonExpansive2 (@uPred_or M).
Time Proof.
Time
(intros n P P' HP Q Q' HQ; <ssreflect_plugin::ssrtclintros@0> split =>x n' ?
  ?).
Time
(unseal; split; (intros [?| ?]; [ left; by apply HP | right; by apply HQ ])).
Time Qed.
Time Lemma impl_ne : NonExpansive2 (@uPred_impl M).
Time Proof.
Time
(intros n P P' HP Q Q' HQ; <ssreflect_plugin::ssrtclintros@0> split =>x n' ?
  ?).
Time (unseal; split; intros HPQ x' n'' ? ? ? ?; apply HQ, HPQ, HP; auto).
Time Qed.
Time Lemma sep_ne : NonExpansive2 (@uPred_sep M).
Time Proof.
Time
(intros n P P' HP Q Q' HQ; <ssreflect_plugin::ssrtclintros@0> split =>n' x ?
  ?).
Time
(unseal; split; intros (x1, (x2, (?, (?, ?)))); ofe_subst x; exists x1,x2;
  split_and !; try apply HP || apply HQ; eauto
  using cmra_validN_op_l, cmra_validN_op_r).
Time Qed.
Time Lemma wand_ne : NonExpansive2 (@uPred_wand M).
Time Proof.
Time
(intros n P P' HP Q Q' HQ; <ssreflect_plugin::ssrtclintros@0> split =>n' x ?
  ?; unseal; split; intros HPQ x' n'' ? ? ?; apply HQ, HPQ, HP; eauto
  using cmra_validN_op_r).
Time Qed.
Time
Lemma internal_eq_ne (A : ofeT) : NonExpansive2 (@uPred_internal_eq M A).
Time Proof.
Time
(intros n x x' Hx y y' Hy; <ssreflect_plugin::ssrtclintros@0> split =>n' z;
  unseal; split; intros; simpl in *).
Time -
Time by rewrite -(dist_le _ _ _ _ Hx) -?(dist_le _ _ _ _ Hy); auto.
Time -
Time by rewrite (dist_le _ _ _ _ Hx) ?(dist_le _ _ _ _ Hy); auto.
Time Qed.
Time
Lemma forall_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_forall M A).
Time Proof.
Time
by
 intros \206\1681 \206\1682 H\206\168; unseal; <ssreflect_plugin::ssrtclintros@0> split =>n' x;
  split; intros HP a; apply H\206\168.
Time Qed.
Time
Lemma exist_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_exist M A).
Time Proof.
Time (intros \206\1681 \206\1682 H\206\168).
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>n' x ? ?; split;
  intros [a ?]; exists a; by apply H\206\168).
Time Qed.
Time Lemma later_contractive : Contractive (@uPred_later M).
Time Proof.
Time
(unseal; intros [| n] P Q HPQ; <ssreflect_plugin::ssrtclintros@0> split =>-
  [|n'] x ? ? //=; try lia).
Time (apply HPQ; eauto using cmra_validN_S).
Time Qed.
Time Lemma plainly_ne : NonExpansive (@uPred_plainly M).
Time Proof.
Time (intros n P1 P2 HP).
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>n' x; split; apply HP;
  eauto using @ucmra_unit_validN).
Time Qed.
Time Lemma persistently_ne : NonExpansive (@uPred_persistently M).
Time Proof.
Time (intros n P1 P2 HP).
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>n' x; split; apply HP;
  eauto using @cmra_core_validN).
Time Qed.
Time Lemma ownM_ne : NonExpansive (@uPred_ownM M).
Time Proof.
Time (intros n a b Ha).
Time (unseal; <ssreflect_plugin::ssrtclintros@0> split =>n' x ? /=).
Time
by <ssreflect_plugin::ssrtclseq@0> rewrite (dist_le _ _ _ _ Ha) ; last  lia.
Time Qed.
Time Lemma cmra_valid_ne {A : cmraT} : NonExpansive (@uPred_cmra_valid M A).
Time Proof.
Time
(intros n a b Ha; unseal; <ssreflect_plugin::ssrtclintros@0> split =>n' x ?
  /=).
Time
by <ssreflect_plugin::ssrtclseq@0> rewrite (dist_le _ _ _ _ Ha) ; last  lia.
Time Qed.
Time Lemma bupd_ne : NonExpansive (@uPred_bupd M).
Time Proof.
Time (intros n P Q HPQ).
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>n' x; split;
  intros HP k yf ? ?; destruct (HP k yf) as (x', (?, ?)); auto; exists x';
  split; auto; apply HPQ; eauto using cmra_validN_op_l).
Time Qed.
Time Lemma pure_intro \207\134 P : \207\134 \226\134\146 P \226\138\162 \226\140\156\207\134\226\140\157.
Time Proof.
Time by intros ?; unseal; split.
Time Qed.
Time Lemma pure_elim' \207\134 P : (\207\134 \226\134\146 True \226\138\162 P) \226\134\146 \226\140\156\207\134\226\140\157 \226\138\162 P.
Time Proof.
Time (unseal; intros HP; <ssreflect_plugin::ssrtclintros@0> split =>n x ? ?).
Time by apply HP.
Time Qed.
Time
Lemma pure_forall_2 {A} (\207\134 : A \226\134\146 Prop) : (\226\136\128 x : A, \226\140\156\207\134 x\226\140\157) \226\138\162 \226\140\156\226\136\128 x : A, \207\134 x\226\140\157.
Time Proof.
Time by unseal.
Time Qed.
Time Lemma and_elim_l P Q : P \226\136\167 Q \226\138\162 P.
Time Proof.
Time by unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? [? ?].
Time Qed.
Time Lemma and_elim_r P Q : P \226\136\167 Q \226\138\162 Q.
Time Proof.
Time by unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? [? ?].
Time Qed.
Time Lemma and_intro P Q R : (P \226\138\162 Q) \226\134\146 (P \226\138\162 R) \226\134\146 P \226\138\162 Q \226\136\167 R.
Time Proof.
Time
(intros HQ HR; unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? ?; by
  split; [ apply HQ | apply HR ]).
Time Qed.
Time Lemma or_intro_l P Q : P \226\138\162 P \226\136\168 Q.
Time Proof.
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? ?; left; auto).
Time Qed.
Time Lemma or_intro_r P Q : Q \226\138\162 P \226\136\168 Q.
Time Proof.
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? ?; right; auto).
Time Qed.
Time Lemma or_elim P Q R : (P \226\138\162 R) \226\134\146 (Q \226\138\162 R) \226\134\146 P \226\136\168 Q \226\138\162 R.
Time Proof.
Time
(intros HP HQ; unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? [?|?]).
Time by apply HP.
Time by apply HQ.
Time Qed.
Time Lemma impl_intro_r P Q R : (P \226\136\167 Q \226\138\162 R) \226\134\146 P \226\138\162 Q \226\134\146 R.
Time Proof.
Time
(unseal; intros HQ; <ssreflect_plugin::ssrtclintros@0> split =>n x ? ? n' x'
  ? ? ? ?).
Time
(apply HQ; naive_solver eauto using uPred_mono, cmra_included_includedN).
Time Qed.
Time Lemma impl_elim_l' P Q R : (P \226\138\162 Q \226\134\146 R) \226\134\146 P \226\136\167 Q \226\138\162 R.
Time Proof.
Time
(unseal; intros HP; <ssreflect_plugin::ssrtclintros@0> split =>n x ? [? ?];
  apply HP with n x; auto).
Time Qed.
Time
Lemma forall_intro {A} P (\206\168 : A \226\134\146 uPred M) : (\226\136\128 a, P \226\138\162 \206\168 a) \226\134\146 P \226\138\162 \226\136\128 a, \206\168 a.
Time Proof.
Time
(unseal; intros HP\206\168; <ssreflect_plugin::ssrtclintros@0> split =>n x ? ? a; by
  apply HP\206\168).
Time Qed.
Time Lemma forall_elim {A} {\206\168 : A \226\134\146 uPred M} a : (\226\136\128 a, \206\168 a) \226\138\162 \206\168 a.
Time Proof.
Time (unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? HP; apply HP).
Time Qed.
Time Lemma exist_intro {A} {\206\168 : A \226\134\146 uPred M} a : \206\168 a \226\138\162 \226\136\131 a, \206\168 a.
Time Proof.
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? ?; by exists a).
Time Qed.
Time
Lemma exist_elim {A} (\206\166 : A \226\134\146 uPred M) Q : (\226\136\128 a, \206\166 a \226\138\162 Q) \226\134\146 (\226\136\131 a, \206\166 a) \226\138\162 Q.
Time Proof.
Time
(unseal; intros H\206\166\206\168; <ssreflect_plugin::ssrtclintros@0> split =>n x ? [a ?];
  by apply H\206\166\206\168 with a).
Time Qed.
Time Lemma sep_mono P P' Q Q' : (P \226\138\162 Q) \226\134\146 (P' \226\138\162 Q') \226\134\146 P \226\136\151 P' \226\138\162 Q \226\136\151 Q'.
Time Proof.
Time (intros HQ HQ'; unseal).
Time
(split; intros n' x ? (x1, (x2, (?, (?, ?)))); exists x1,x2; ofe_subst x;
  eauto  7 using cmra_validN_op_l, cmra_validN_op_r, uPred_in_entails).
Time Qed.
Time Lemma True_sep_1 P : P \226\138\162 True \226\136\151 P.
Time Proof.
Time (unseal; split; intros n x ? ?).
Time exists (core x),x.
Time by rewrite cmra_core_l.
Time Qed.
Time Lemma True_sep_2 P : True \226\136\151 P \226\138\162 P.
Time Proof.
Time
(unseal; split; intros n x ? (x1, (x2, (?, (_, ?)))); ofe_subst; eauto
  using uPred_mono, cmra_includedN_r).
Time Qed.
Time Lemma sep_comm' P Q : P \226\136\151 Q \226\138\162 Q \226\136\151 P.
Time Proof.
Time
(unseal; split; intros n x ? (x1, (x2, (?, (?, ?)))); exists x2,x1; by
  rewrite (comm op)).
Time Qed.
Time Lemma sep_assoc' P Q R : (P \226\136\151 Q) \226\136\151 R \226\138\162 P \226\136\151 Q \226\136\151 R.
Time Proof.
Time
(unseal; split; intros n x ? (x1, (x2, (Hx, ((y1, (y2, (Hy, (?, ?)))), ?))))).
Time (exists y1,(y2 \226\139\133 x2); split_and ?; auto).
Time +
Time by rewrite (assoc op) -Hy -Hx.
Time +
Time by exists y2,x2.
Time Qed.
Time Lemma wand_intro_r P Q R : (P \226\136\151 Q \226\138\162 R) \226\134\146 P \226\138\162 Q -\226\136\151 R.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> unseal =>HPQR;
  <ssreflect_plugin::ssrtclintros@0> split =>n x ? ? n' x' ? ? ?; 
  apply HPQR; auto).
Time (exists x,x'; split_and ?; auto).
Time (eapply uPred_mono with n x; eauto using cmra_validN_op_l).
Time Qed.
Time Lemma wand_elim_l' P Q R : (P \226\138\162 Q -\226\136\151 R) \226\134\146 P \226\136\151 Q \226\138\162 R.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> unseal =>HPQR).
Time (split; intros n x ? (?, (?, (?, (?, ?))))).
Time ofe_subst.
Time (eapply HPQR; eauto using cmra_validN_op_l).
Time Qed.
Time Lemma persistently_mono P Q : (P \226\138\162 Q) \226\134\146 \226\150\161 P \226\138\162 \226\150\161 Q.
Time Proof.
Time
(intros HP; unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? /=).
Time by apply HP, cmra_core_validN.
Time Qed.
Time Lemma persistently_elim P : \226\150\161 P \226\138\162 P.
Time Proof.
Time (unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? /=).
Time eauto using uPred_mono, @cmra_included_core, cmra_included_includedN.
Time Qed.
Time Lemma persistently_idemp_2 P : \226\150\161 P \226\138\162 \226\150\161 \226\150\161 P.
Time Proof.
Time (unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? ? /=).
Time by rewrite cmra_core_idemp.
Time Qed.
Time
Lemma persistently_forall_2 {A} (\206\168 : A \226\134\146 uPred M) :
  (\226\136\128 a, \226\150\161 \206\168 a) \226\138\162 \226\150\161 (\226\136\128 a, \206\168 a).
Time Proof.
Time by unseal.
Time Qed.
Time
Lemma persistently_exist_1 {A} (\206\168 : A \226\134\146 uPred M) : \226\150\161 (\226\136\131 a, \206\168 a) \226\138\162 \226\136\131 a, \226\150\161 \206\168 a.
Time Proof.
Time by unseal.
Time Qed.
Time Lemma persistently_and_sep_l_1 P Q : \226\150\161 P \226\136\167 Q \226\138\162 P \226\136\151 Q.
Time Proof.
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? [? ?]; exists 
   (core x),x; simpl in *).
Time by rewrite cmra_core_l.
Time Qed.
Time Lemma plainly_mono P Q : (P \226\138\162 Q) \226\134\146 \226\150\160 P \226\138\162 \226\150\160 Q.
Time Proof.
Time
(intros HP; unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? /=).
Time (apply HP, ucmra_unit_validN).
Time Qed.
Time Lemma plainly_elim_persistently P : \226\150\160 P \226\138\162 \226\150\161 P.
Time Proof.
Time (unseal; split; simpl; eauto using uPred_mono, @ucmra_unit_leastN).
Time Qed.
Time Lemma plainly_idemp_2 P : \226\150\160 P \226\138\162 \226\150\160 \226\150\160 P.
Time Proof.
Time (unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? ? //).
Time Qed.
Time
Lemma plainly_forall_2 {A} (\206\168 : A \226\134\146 uPred M) : (\226\136\128 a, \226\150\160 \206\168 a) \226\138\162 \226\150\160 (\226\136\128 a, \206\168 a).
Time Proof.
Time by unseal.
Time Qed.
Time Lemma plainly_exist_1 {A} (\206\168 : A \226\134\146 uPred M) : \226\150\160 (\226\136\131 a, \206\168 a) \226\138\162 \226\136\131 a, \226\150\160 \206\168 a.
Time Proof.
Time by unseal.
Time Qed.
Time Lemma prop_ext_2 P Q : \226\150\160 ((P -\226\136\151 Q) \226\136\167 (Q -\226\136\151 P)) \226\138\162 P \226\137\161 Q.
Time Proof.
Time (unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? /= HPQ).
Time (<ssreflect_plugin::ssrtclintros@0> split =>n' x' ? ?).
Time
(move : {}HPQ {} =>[] /(_ n' x'); <ssreflect_plugin::ssrtclintros@0> rewrite
  !left_id =>?).
Time
(move  {}=>/(_ n' x'); <ssreflect_plugin::ssrtclintros@0> rewrite !left_id
  =>?).
Time naive_solver.
Time Qed.
Time Lemma persistently_impl_plainly P Q : (\226\150\160 P \226\134\146 \226\150\161 Q) \226\138\162 \226\150\161 (\226\150\160 P \226\134\146 Q).
Time Proof.
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>/= n x ? HPQ n' x' ? ? ?
  ?).
Time
(<ssreflect_plugin::ssrtclintros@0> eapply uPred_mono with n' (core x) =>//;
  [  | by apply cmra_included_includedN ]).
Time (apply (HPQ n' x); eauto using cmra_validN_le).
Time Qed.
Time Lemma plainly_impl_plainly P Q : (\226\150\160 P \226\134\146 \226\150\160 Q) \226\138\162 \226\150\160 (\226\150\160 P \226\134\146 Q).
Time Proof.
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>/= n x ? HPQ n' x' ? ? ?
  ?).
Time
(<ssreflect_plugin::ssrtclintros@0> eapply uPred_mono with n' \206\181 =>//;
  [  | by apply cmra_included_includedN ]).
Time (apply (HPQ n' x); eauto using cmra_validN_le).
Time Qed.
Time Lemma later_mono P Q : (P \226\138\162 Q) \226\134\146 \226\150\183 P \226\138\162 \226\150\183 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> unseal =>HP;
  <ssreflect_plugin::ssrtclintros@0> split =>- [|n] x ? ?;
  [ done | apply HP; eauto using cmra_validN_S ]).
Time Qed.
Time Lemma later_intro P : P \226\138\162 \226\150\183 P.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0>
 unseal; <ssreflect_plugin::ssrtclintros@0> split =>- [|n] /= x ? HP ; first 
 done).
Time (apply uPred_mono with (S n) x; eauto using cmra_validN_S).
Time Qed.
Time
Lemma later_forall_2 {A} (\206\166 : A \226\134\146 uPred M) : (\226\136\128 a, \226\150\183 \206\166 a) \226\138\162 \226\150\183 (\226\136\128 a, \206\166 a).
Time Proof.
Time (unseal; by <ssreflect_plugin::ssrtclintros@0> split =>- [|n] x).
Time Qed.
Time
Lemma later_exist_false {A} (\206\166 : A \226\134\146 uPred M) :
  \226\150\183 (\226\136\131 a, \206\166 a) \226\138\162 \226\150\183 False \226\136\168 (\226\136\131 a, \226\150\183 \206\166 a).
Time Proof.
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>- [|[|n]] x /=; eauto).
Time Qed.
Time Lemma later_sep_1 P Q : \226\150\183 (P \226\136\151 Q) \226\138\162 \226\150\183 P \226\136\151 \226\150\183 Q.
Time Proof.
Time (unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ?).
Time (destruct n as [| n]; simpl).
Time {
Time by exists x,(core x); rewrite cmra_core_r.
Time }
Time
(intros (x1, (x2, (Hx, (?, ?))));
  destruct (cmra_extend n x x1 x2) as (y1, (y2, (Hx', (Hy1, Hy2)))); eauto
  using cmra_validN_S; simpl in *).
Time (exists y1,y2; split; [ by rewrite Hx' | by rewrite Hy1 Hy2 ]).
Time Qed.
Time Lemma later_sep_2 P Q : \226\150\183 P \226\136\151 \226\150\183 Q \226\138\162 \226\150\183 (P \226\136\151 Q).
Time Proof.
Time (unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ?).
Time
(destruct n as [| n]; simpl; [ done | intros (x1, (x2, (Hx, (?, ?)))) ]).
Time (exists x1,x2; eauto using dist_S).
Time Qed.
Time Lemma later_false_em P : \226\150\183 P \226\138\162 \226\150\183 False \226\136\168 (\226\150\183 False \226\134\146 P).
Time Proof.
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>- [|n] x ? /= HP;
  [ by left | right ]).
Time
(intros [| n'] x' ? ? ? ?; eauto using uPred_mono, cmra_included_includedN).
Time Qed.
Time Lemma later_persistently_1 P : \226\150\183 \226\150\161 P \226\138\162 \226\150\161 \226\150\183 P.
Time Proof.
Time by unseal.
Time Qed.
Time Lemma later_persistently_2 P : \226\150\161 \226\150\183 P \226\138\162 \226\150\183 \226\150\161 P.
Time Proof.
Time by unseal.
Time Qed.
Time Lemma later_plainly_1 P : \226\150\183 \226\150\160 P \226\138\162 \226\150\160 \226\150\183 P.
Time Proof.
Time by unseal.
Time Qed.
Time Lemma later_plainly_2 P : \226\150\160 \226\150\183 P \226\138\162 \226\150\183 \226\150\160 P.
Time Proof.
Time by unseal.
Time Qed.
Time Lemma internal_eq_refl {A : ofeT} P (a : A) : P \226\138\162 a \226\137\161 a.
Time Proof.
Time (unseal; by <ssreflect_plugin::ssrtclintros@0> split =>n x ? ?; simpl).
Time Qed.
Time
Lemma internal_eq_rewrite {A : ofeT} a b (\206\168 : A \226\134\146 uPred M) :
  NonExpansive \206\168 \226\134\146 a \226\137\161 b \226\138\162 \206\168 a \226\134\146 \206\168 b.
Time Proof.
Time (intros H\206\168).
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? ? n' x' ? ? ? Ha).
Time by apply H\206\168 with n a.
Time Qed.
Time
Lemma fun_ext {A} {B : A \226\134\146 ofeT} (g1 g2 : discrete_fun B) :
  (\226\136\128 i, g1 i \226\137\161 g2 i) \226\138\162 g1 \226\137\161 g2.
Time Proof.
Time by unseal.
Time Qed.
Time
Lemma sig_eq {A : ofeT} (P : A \226\134\146 Prop) (x y : sigO P) :
  proj1_sig x \226\137\161 proj1_sig y \226\138\162 x \226\137\161 y.
Time Proof.
Time by unseal.
Time Qed.
Time Lemma later_eq_1 {A : ofeT} (x y : A) : Next x \226\137\161 Next y \226\138\162 \226\150\183 (x \226\137\161 y).
Time Proof.
Time by unseal.
Time Qed.
Time Lemma later_eq_2 {A : ofeT} (x y : A) : \226\150\183 (x \226\137\161 y) \226\138\162 Next x \226\137\161 Next y.
Time Proof.
Time by unseal.
Time Qed.
Time Lemma discrete_eq_1 {A : ofeT} (a b : A) : Discrete a \226\134\146 a \226\137\161 b \226\138\162 \226\140\156a \226\137\161 b\226\140\157.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> unseal =>?).
Time (<ssreflect_plugin::ssrtclintros@0> split =>n x ?).
Time by apply (discrete_iff n).
Time Qed.
Time Lemma bupd_intro P : P \226\138\162 |==> P.
Time Proof.
Time unseal.
Time
(<ssreflect_plugin::ssrtclseq@0>
 <ssreflect_plugin::ssrtclintros@0> split =>n x ? HP k yf ?; exists x; split
 ; first  done).
Time (apply uPred_mono with n x; eauto using cmra_validN_op_l).
Time Qed.
Time Lemma bupd_mono P Q : (P \226\138\162 Q) \226\134\146 (|==> P) \226\138\162 |==> Q.
Time Proof.
Time unseal.
Time
(intros HPQ; <ssreflect_plugin::ssrtclintros@0> split =>n x ? HP k yf ? ?).
Time (destruct (HP k yf) as (x', (?, ?)); eauto).
Time (exists x'; split; eauto using uPred_in_entails, cmra_validN_op_l).
Time Qed.
Time Lemma bupd_trans P : (|==> |==> P) \226\138\162 |==> P.
Time Proof.
Time (unseal; split; naive_solver).
Time Qed.
Time Lemma bupd_frame_r P R : (|==> P) \226\136\151 R \226\138\162 |==> P \226\136\151 R.
Time Proof.
Time (unseal; split; intros n x ? (x1, (x2, (Hx, (HP, ?)))) k yf ? ?).
Time (destruct (HP k (x2 \226\139\133 yf)) as (x', (?, ?)); eauto).
Time {
Time
by <ssreflect_plugin::ssrtclseq@0> rewrite assoc -
 (dist_le _ _ _ _ Hx) ; last  lia.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> exists (x' \226\139\133 x2); split ; first  by rewrite
 -assoc).
Time exists x',x2.
Time eauto using uPred_mono, cmra_validN_op_l, cmra_validN_op_r.
Time Qed.
Time Lemma bupd_plainly P : (|==> \226\150\160 P) \226\138\162 P.
Time Proof.
Time (unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x Hnx /= Hng).
Time (destruct (Hng n \206\181) as [? [_ Hng']]; try rewrite right_id; auto).
Time (eapply uPred_mono; eauto using ucmra_unit_leastN).
Time Qed.
Time
Lemma ownM_op (a1 a2 : M) :
  uPred_ownM (a1 \226\139\133 a2) \226\138\163\226\138\162 uPred_ownM a1 \226\136\151 uPred_ownM a2.
Time Proof.
Time (unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ?; split).
Time -
Time (intros [z ?]; exists a1,(a2 \226\139\133 z); split; [ by rewrite (assoc op) |  ]).
Time split.
Time by exists (core a1); rewrite cmra_core_r.
Time by exists z.
Time -
Time (intros (y1, (y2, (Hx, ([z1 Hy1], [z2 Hy2])))); exists (z1 \226\139\133 z2)).
Time
by rewrite (assoc op _ z1) -(comm op z1) (assoc op z1) -
 (assoc op _ a2) (comm op z1) -Hy1 -Hy2.
Time Qed.
Time
Lemma persistently_ownM_core (a : M) : uPred_ownM a \226\138\162 \226\150\161 uPred_ownM (core a).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> split =>n x /=; unseal; intros Hx).
Time (simpl).
Time by apply cmra_core_monoN.
Time Qed.
Time Lemma ownM_unit P : P \226\138\162 uPred_ownM \206\181.
Time Proof.
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x ? ?; by
  exists x; rewrite left_id).
Time Qed.
Time Lemma later_ownM a : \226\150\183 uPred_ownM a \226\138\162 \226\136\131 b, uPred_ownM b \226\136\167 \226\150\183 (a \226\137\161 b).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0>
 unseal; <ssreflect_plugin::ssrtclintros@0> split =>- [|n] x /= ? Hax ;
 first  by eauto using ucmra_unit_leastN).
Time (destruct Hax as [y ?]).
Time
(destruct (cmra_extend n x a y) as (a', (y', (Hx, (?, ?)))); auto
  using cmra_validN_S).
Time exists a'.
Time rewrite Hx.
Time eauto using cmra_includedN_l.
Time Qed.
Time
Lemma bupd_ownM_updateP x (\206\166 : M \226\134\146 Prop) :
  x ~~>: \206\166 \226\134\146 uPred_ownM x \226\138\162 |==> \226\136\131 y, \226\140\156\206\166 y\226\140\157 \226\136\167 uPred_ownM y.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> unseal =>Hup;
  <ssreflect_plugin::ssrtclintros@0> split =>n x2 ? 
  [x3 Hx] k yf ? ?).
Time (destruct (Hup k (Some (x3 \226\139\133 yf))) as (y, (?, ?)); simpl in *).
Time {
Time (rewrite /= assoc -(dist_le _ _ _ _ Hx); auto).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> exists (y \226\139\133 x3); split ; first  by rewrite
 -assoc).
Time (exists y; eauto using cmra_includedN_l).
Time Qed.
Time Lemma ownM_valid (a : M) : uPred_ownM a \226\138\162 \226\156\147 a.
Time Proof.
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x Hv [a' ?]; ofe_subst;
  eauto using cmra_validN_op_l).
Time Qed.
Time Lemma cmra_valid_intro {A : cmraT} P (a : A) : \226\156\147 a \226\134\146 P \226\138\162 \226\156\147 a.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> unseal =>?;
  <ssreflect_plugin::ssrtclintros@0> split =>n x ? _ /=; by
  apply cmra_valid_validN).
Time Qed.
Time Lemma cmra_valid_elim {A : cmraT} (a : A) : \194\172 \226\156\147{0} a \226\134\146 \226\156\147 a \226\138\162 False.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> unseal =>Ha;
  <ssreflect_plugin::ssrtclintros@0> split =>n x ? ?;
  apply Ha, cmra_validN_le with n; auto).
Time Qed.
Time Lemma plainly_cmra_valid_1 {A : cmraT} (a : A) : \226\156\147 a \226\138\162 \226\150\160 \226\156\147 a.
Time Proof.
Time by unseal.
Time Qed.
Time Lemma cmra_valid_weaken {A : cmraT} (a b : A) : \226\156\147 (a \226\139\133 b) \226\138\162 \226\156\147 a.
Time Proof.
Time
(unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x _;
  apply cmra_validN_op_l).
Time Qed.
Time Lemma prod_validI {A B : cmraT} (x : A * B) : \226\156\147 x \226\138\163\226\138\162 \226\156\147 x.1 \226\136\167 \226\156\147 x.2.
Time Proof.
Time by unseal.
Time Qed.
Time
Lemma option_validI {A : cmraT} (mx : option A) :
  \226\156\147 mx \226\138\163\226\138\162 match mx with
          | Some x => \226\156\147 x
          | None => True : uPred M
          end.
Time Proof.
Time unseal.
Time by destruct mx.
Time Qed.
Time
Lemma discrete_valid {A : cmraT} `{!CmraDiscrete A} (a : A) : \226\156\147 a \226\138\163\226\138\162 \226\140\156\226\156\147 a\226\140\157.
Time Proof.
Time (unseal; <ssreflect_plugin::ssrtclintros@0> split =>n x _).
Time by rewrite /= -cmra_discrete_valid_iff.
Time Qed.
Time
Lemma discrete_fun_validI {A} {B : A \226\134\146 ucmraT} (g : discrete_fun B) :
  \226\156\147 g \226\138\163\226\138\162 (\226\136\128 i, \226\156\147 g i).
Time Proof.
Time by unseal.
Time Qed.
Time Lemma pure_soundness \207\134 : (True \226\138\162 \226\140\156\207\134\226\140\157) \226\134\146 \207\134.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> unseal =>- [H]).
Time by apply (H 0 \206\181); eauto using ucmra_unit_validN.
Time Qed.
Time Lemma later_soundness P : (True \226\138\162 \226\150\183 P) \226\134\146 True \226\138\162 P.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> unseal =>- [HP];
  <ssreflect_plugin::ssrtclintros@0> split =>n x Hx _).
Time (apply uPred_mono with n \206\181; eauto using ucmra_unit_leastN).
Time by apply (HP (S n)); eauto using ucmra_unit_validN.
Time Qed.
Time End primitive.
Time End uPred_primitive.

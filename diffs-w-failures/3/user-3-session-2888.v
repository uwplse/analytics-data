Time From iris.algebra Require Export ofe.
Time Set Default Proof Using "Type".
Time
Record solution (F : cFunctor) :=
 Solution {solution_car :> ofeT;
           solution_cofe : Cofe solution_car;
           solution_unfold : solution_car -n> F solution_car _;
           solution_fold : F solution_car _ -n> solution_car;
           solution_fold_unfold :
            forall X, solution_fold (solution_unfold X) \226\137\161 X;
           solution_unfold_fold :
            forall X, solution_unfold (solution_fold X) \226\137\161 X}.
Time Arguments solution_unfold {_} _.
Time Arguments solution_fold {_} _.
Time Existing Instance solution_cofe.
Time Module solver.
Time Section solver.
Time Context (F : cFunctor) `{Fcontr : cFunctorContractive F}.
Time Context `{Fcofe : \226\136\128 (T : ofeT) `{!Cofe T}, Cofe (F T _)}.
Time Context `{Finh : Inhabited (F unitC _)}.
Time Notation map := (cFunctor_map F).
Time
Fixpoint A' (k : nat) : {C : ofeT & Cofe C} :=
  match k with
  | 0 => existT (P:=Cofe) unitC _
  | S k => existT (P:=Cofe) (F (projT1 (A' k)) (projT2 (A' k))) _
  end.
Time Notation A k:= (projT1 (A' k)).
Time #[local]Instance A_cofe  k: (Cofe (A k)) := (projT2 (A' k)).
Time
Fixpoint f (k : nat) : A k -n> A (S k) :=
  match k with
  | 0 => CofeMor (\206\187 _, inhabitant)
  | S k => map (g k, f k)
  end
with g (k : nat) : A (S k) -n> A k :=
  match k with
  | 0 => CofeMor (\206\187 _, ())
  | S k => map (f k, g k)
  end.
Time
Definition f_S k (x : A (S k)) : f (S k) x = map (g k, f k) x := eq_refl.
Time
Definition g_S k (x : A (S (S k))) : g (S k) x = map (f k, g k) x := eq_refl.
Time Arguments f : simpl never.
Time Arguments g : simpl never.
Time Lemma gf {k} (x : A k) : g k (f k x) \226\137\161 x.
Time Proof  using (Fcontr).
Time (induction k as [| k IH]; simpl in *; [ by destruct x |  ]).
Time rewrite -cFunctor_compose -{+2}[x]cFunctor_id.
Time by apply (contractive_proper map).
Time Qed.
Time Lemma fg {k} (x : A (S (S k))) : f (S k) (g (S k) x) \226\137\161{k}\226\137\161 x.
Time Proof  using (Fcontr).
Time (induction k as [| k IH]; simpl).
Time -
Time rewrite f_S g_S -{+2}[x]cFunctor_id -cFunctor_compose.
Time (apply (contractive_0 map)).
Time -
Time rewrite f_S g_S -{+2}[x]cFunctor_id -cFunctor_compose.
Time by apply (contractive_S map).
Time Qed.
Time
Record tower :={tower_car :> forall k, A k;
                g_tower : forall k, g k (tower_car (S k)) \226\137\161 tower_car k}.
Time Instance tower_equiv : (Equiv tower) := (\206\187 X Y, \226\136\128 k, X k \226\137\161 Y k).
Time Instance tower_dist : (Dist tower) := (\206\187 n X Y, \226\136\128 k, X k \226\137\161{n}\226\137\161 Y k).
Time Definition tower_ofe_mixin : OfeMixin tower.
Time Proof.
Time split.
Time -
Time (intros X Y; split; [ by intros HXY n k; apply equiv_dist |  ]).
Time (intros HXY k; apply equiv_dist; intros n; apply HXY).
Time -
Time (intros k; split).
Time +
Time by intros X n.
Time +
Time by intros X Y ? n.
Time +
Time by intros X Y Z ? ? n; trans Y n.
Time -
Time (intros k X Y HXY n; apply dist_S).
Time by rewrite -(g_tower X) (HXY (S n)) g_tower.
Time Qed.
Time Definition T : ofeT := OfeT tower tower_ofe_mixin.
Time #[program]
Definition tower_chain (c : chain T) (k : nat) : chain (A k) :=
  {| chain_car := fun i => c i k |}.
Time Next Obligation.
Time (intros c k n i ?; apply (chain_cauchy c n); lia).
Time Qed.
Time #[program]
Definition tower_compl : Compl T :=
  \206\187 c, {| tower_car := fun n => compl (tower_chain c n) |}.
Time Next Obligation.
Time (intros c k; <ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n).
Time
by rewrite (conv_compl n (tower_chain c k))
 (conv_compl n (tower_chain c (S k))) /= (g_tower (c _) k).
Time Qed.
Time #[global, program]
Instance tower_cofe : (Cofe T) := { compl :=tower_compl}.
Time Next Obligation.
Time (intros n c k; rewrite /= (conv_compl n (tower_chain c k))).
Time (apply (chain_cauchy c); lia).
Time Qed.
Time
Fixpoint ff {k} (i : nat) : A k -n> A (i + k) :=
  match i with
  | 0 => cid
  | S i => f (i + k) \226\151\142 ff i
  end.
Time
Fixpoint gg {k} (i : nat) : A (i + k) -n> A k :=
  match i with
  | 0 => cid
  | S i => gg i \226\151\142 g (i + k)
  end.
Time Lemma ggff {k} {i} (x : A k) : gg i (ff i x) \226\137\161 x.
Time Proof  using (Fcontr).
Time
(induction i as [| i IH]; simpl; [ done | by rewrite (gf (ff i x)) IH ]).
Time Qed.
Time Lemma f_tower k (X : tower) : f (S k) (X (S k)) \226\137\161{k}\226\137\161 X (S (S k)).
Time Proof  using (Fcontr).
Time (intros).
Time by rewrite -(fg (X (S (S k)))) -(g_tower X).
Time Qed.
Time Lemma ff_tower k i (X : tower) : ff i (X (S k)) \226\137\161{k}\226\137\161 X (i + S k).
Time Proof  using (Fcontr).
Time (intros; induction i as [| i IH]; simpl; [ done |  ]).
Time
by <ssreflect_plugin::ssrtclseq@0> rewrite IH Nat.add_succ_r
 (dist_le _ _ _ _ (f_tower _ X)) ; last  lia.
Time Qed.
Time Lemma gg_tower k i (X : tower) : gg i (X (i + k)) \226\137\161 X k.
Time Proof.
Time by induction i as [| i IH]; simpl; [ done | rewrite g_tower IH ].
Time Qed.
Time Instance tower_car_ne  k: (NonExpansive (\206\187 X, tower_car X k)).
Time Proof.
Time by intros X Y HX.
Time Qed.
Time
Definition project (k : nat) : T -n> A k := CofeMor (\206\187 X : T, tower_car X k).
Time
Definition coerce {i} {j} (H : i = j) : A i -n> A j :=
  eq_rect _ (\206\187 i', A i -n> A i') cid _ H.
Time Lemma coerce_id {i} (H : i = i) (x : A i) : coerce H x = x.
Time Proof.
Time (unfold coerce).
Time by rewrite (proof_irrel H (eq_refl i)).
Time Qed.
Time
Lemma coerce_proper {i} {j} (x y : A i) (H1 H2 : i = j) :
  x = y \226\134\146 coerce H1 x = coerce H2 y.
Time Proof.
Time by destruct H1; rewrite !coerce_id.
Time Qed.
Time
Lemma g_coerce {k} {j} (H : S k = S j) (x : A (S k)) :
  g j (coerce H x) = coerce (Nat.succ_inj _ _ H) (g k x).
Time Proof.
Time by assert (k = j) by lia; subst; rewrite !coerce_id.
Time Qed.
Time
Lemma coerce_f {k} {j} (H : S k = S j) (x : A k) :
  coerce H (f k x) = f j (coerce (Nat.succ_inj _ _ H) x).
Time Proof.
Time by assert (k = j) by lia; subst; rewrite !coerce_id.
Time Qed.
Time
Lemma gg_gg {k} {i} {i1} {i2} {j} :
  \226\136\128 (H1 : k = i + j) (H2 : k = i2 + (i1 + j)) (x : A k),
    gg i (coerce H1 x) = gg i1 (gg i2 (coerce H2 x)).
Time Proof.
Time (intros ? -> x).
Time (assert (i = i2 + i1) as -> by lia).
Time revert j x H1.
Time
(induction i2 as [| i2 IH]; intros j X H1; simplify_eq /=;
  [ by rewrite coerce_id | by rewrite g_coerce IH ]).
Time Qed.
Time
Lemma ff_ff {k} {i} {i1} {i2} {j} :
  \226\136\128 (H1 : i + k = j) (H2 : i1 + (i2 + k) = j) (x : A k),
    coerce H1 (ff i x) = coerce H2 (ff i1 (ff i2 x)).
Time Proof.
Time (intros ? <- x).
Time (assert (i = i1 + i2) as -> by lia).
Time
(induction i1 as [| i1 IH]; simplify_eq /=;
  [ by rewrite coerce_id | by rewrite coerce_f IH ]).
Time Qed.
Time
Definition embed_coerce {k} (i : nat) : A k -n> A i :=
  match le_lt_dec i k with
  | left H => gg (k - i) \226\151\142 coerce (eq_sym (Nat.sub_add _ _ H))
  | right H => coerce (Nat.sub_add k i (Nat.lt_le_incl _ _ H)) \226\151\142 ff (i - k)
  end.
Time
Lemma g_embed_coerce {k} {i} (x : A k) :
  g i (embed_coerce (S i) x) \226\137\161 embed_coerce i x.
Time Proof  using (Fcontr).
Time
(unfold embed_coerce; destruct (le_lt_dec (S i) k), (le_lt_dec i k); simpl).
Time -
Time (symmetry; by erewrite (@gg_gg _ _ 1 (k - S i)); simpl).
Time -
Time (exfalso; lia).
Time -
Time (assert (i = k) by lia; subst).
Time rewrite (ff_ff _ (eq_refl (1 + (0 + k)))) /= gf.
Time by rewrite (gg_gg _ (eq_refl (0 + (0 + k)))).
Time -
Time (assert (H : 1 + (i - k + k) = S i) by lia).
Time rewrite (ff_ff _ H) /= -{+2}(gf (ff (i - k) x)) g_coerce.
Time by erewrite coerce_proper by done.
Time Qed.
Time #[program]
Definition embed (k : nat) (x : A k) : T :=
  {| tower_car := fun n => embed_coerce n x |}.
Time Next Obligation.
Time (intros k x i).
Time (apply g_embed_coerce).
Time Qed.
Time Instance: (Params (@embed) 1) := { }.
Time Instance embed_ne  k: (NonExpansive (embed k)).
Time Proof.
Time by intros n x y Hxy i; rewrite /= Hxy.
Time Qed.
Time Definition embed' (k : nat) : A k -n> T := CofeMor (embed k).
Time Lemma embed_f k (x : A k) : embed (S k) (f k x) \226\137\161 embed k x.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite equiv_dist =>n i; rewrite /embed
  /= /embed_coerce).
Time (destruct (le_lt_dec i (S k)), (le_lt_dec i k); simpl).
Time -
Time (assert (H : S k = S (k - i) + (0 + i)) by lia; rewrite (gg_gg _ H) /=).
Time by erewrite g_coerce, gf, coerce_proper by done.
Time -
Time (assert (H : S k = 0 + (0 + i)) by lia).
Time (rewrite (gg_gg _ H); simplify_eq /=).
Time by rewrite (ff_ff _ (eq_refl (1 + (0 + k)))).
Time -
Time (exfalso; lia).
Time -
Time (assert (H : i - S k + (1 + k) = i) by lia; rewrite (ff_ff _ H) /=).
Time by erewrite coerce_proper by done.
Time Qed.
Time Lemma embed_tower k (X : T) : embed (S k) (X (S k)) \226\137\161{k}\226\137\161 X.
Time Proof.
Time (intros i; rewrite /= /embed_coerce).
Time (destruct (le_lt_dec i (S k)) as [H| H]; simpl).
Time -
Time rewrite -(gg_tower i (S k - i) X).
Time (apply (_ : Proper (_ ==> _) (gg _)); by destruct (eq_sym _)).
Time -
Time rewrite (ff_tower k (i - S k) X).
Time by destruct (Nat.sub_add _ _ _).
Time Qed.
Time #[program]
Definition unfold_chain (X : T) : chain (F T _) :=
  {| chain_car := fun n => map (project n, embed' n) (X (S n)) |}.
Time Next Obligation.
Time (intros X n i Hi).
Time
(assert (\226\136\131 k, i = k + n) as [k ?] by (exists (i - n); lia); subst; clear Hi).
Time
(<ssreflect_plugin::ssrtclseq@0> induction k as [| k IH]; simpl ; first 
 done).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite -IH
 -(dist_le _ _ _ _ (f_tower (k + n) _)) ; last  lia).
Time rewrite f_S -cFunctor_compose.
Time
by
 apply (contractive_ne map); <ssreflect_plugin::ssrtclintros@0> split =>Y /=;
  rewrite ?g_tower ?embed_f.
Time Qed.
Time Definition unfold (X : T) : F T _ := compl (unfold_chain X).
Time Instance unfold_ne : (NonExpansive unfold).
Time Proof.
Time (intros n X Y HXY).
Time
by rewrite /unfold (conv_compl n (unfold_chain X))
 (conv_compl n (unfold_chain Y)) /= (HXY (S n)).
Time Qed.
Time #[program]
Definition fold (X : F T _) : T :=
  {| tower_car := fun n => g n (map (embed' n, project n) X) |}.
Time Next Obligation.
Time (intros X k).
Time (apply (_ : Proper ((\226\137\161) ==> (\226\137\161)) (g k))).
Time rewrite g_S -cFunctor_compose.
Time
(apply (contractive_proper map); <ssreflect_plugin::ssrtclintros@0> split =>Y;
  [ apply embed_f | apply g_tower ]).
Time Qed.
Time Instance fold_ne : (NonExpansive fold).
Time Proof.
Time by intros n X Y HXY k; rewrite /fold /= HXY.
Time Qed.
Time Theorem result : solution F.
Time Proof  using ((Type))*.
Time (apply (Solution F T _ (CofeMor unfold) (CofeMor fold))).
Time -
Time move  {}=>X /=.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite equiv_dist =>n k; rewrite /unfold
  /fold /=).
Time (rewrite -g_tower -(gg_tower _ n); apply (_ : Proper (_ ==> _) (g _))).
Time trans map (ff n, gg n) (X (S (n + k))).
Time {
Time rewrite /unfold (conv_compl n (unfold_chain X)).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite
 -(chain_cauchy (unfold_chain X) n (S (n + k))) /= ; last  lia).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite
 -(dist_le _ _ _ _ (f_tower (n + k) _)) ; last  lia).
Time
(rewrite f_S -!cFunctor_compose; apply (contractive_ne map);
  <ssreflect_plugin::ssrtclintros@0> split =>Y).
Time +
Time rewrite /embed' /= /embed_coerce.
Time (destruct (le_lt_dec _ _); simpl; [ exfalso; lia |  ]).
Time by rewrite (ff_ff _ (eq_refl (S n + (0 + k)))) /= gf.
Time +
Time rewrite /embed' /= /embed_coerce.
Time (destruct (le_lt_dec _ _); simpl; [  | exfalso; lia ]).
Time by rewrite (gg_gg _ (eq_refl (0 + (S n + k)))) /= gf.
Time }
Time
(assert
  (map_ff_gg :
   \226\136\128 i k (x : A (S i + k)) (H : S i + k = i + S k),
     map (ff i, gg i) x \226\137\161 gg i (coerce H x))).
Time {
Time (intros i; induction i as [| i IH]; intros k' x H; simpl).
Time {
Time by rewrite coerce_id cFunctor_id.
Time }
Time (rewrite cFunctor_compose g_coerce; apply IH).
Time }
Time (assert (H : S n + k = n + S k) by lia).
Time rewrite (map_ff_gg _ _ _ H).
Time (apply (_ : Proper (_ ==> _) (gg _)); by destruct H).
Time -
Time
(intros X; <ssreflect_plugin::ssrtclintros@0> rewrite equiv_dist =>n /=).
Time rewrite /unfold /= (conv_compl' n (unfold_chain (fold X))) /=.
Time rewrite g_S -!cFunctor_compose -{+2}[X]cFunctor_id.
Time
(apply (contractive_ne map); <ssreflect_plugin::ssrtclintros@0> split =>Y /=).
Time +
Time rewrite f_tower.
Time (apply dist_S).
Time by rewrite embed_tower.
Time +
Time (etrans; [ apply embed_ne, equiv_dist, g_tower | apply embed_tower ]).
Time Qed.
Time End solver.
Time End solver.

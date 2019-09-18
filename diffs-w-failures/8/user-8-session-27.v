Require Import Prelim.
Require Import Monad.
Require Import Contexts.
Require Import HOASCircuits.
Open Scope circ_scope.
Global Opaque merge.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Arguments db_output {w}.
Arguments db_gate {w} {w1} {w2}.
Arguments db_lift {w}.
Arguments db_box w1 {w2}.
Fixpoint get_fresh w (\206\147 : Ctx) : Pat w * Ctx :=
  match w with
  | One => (unit, [])
  | Bit => (bit (length \206\147), singleton (length \206\147) w)
  | Qubit => (qubit (length \206\147), singleton (length \206\147) w)
  | w1 \226\138\151 w2 =>
      let (p1, \206\1471) := get_fresh w1 \206\147 in
      match \206\147 \226\139\147 \206\1471 with
      | Invalid => (dummy_pat, dummy_ctx)
      | Valid \206\147' =>
          let (p2, \206\1472) := get_fresh w2 \206\147' in
          match \206\1471 \226\139\147 \206\1472 with
          | Invalid => (dummy_pat, dummy_ctx)
          | Valid \206\147'' => (pair p1 p2, \206\147'')
          end
      end
  end.
Definition get_fresh_pat w \206\147 : Pat w := fst (get_fresh w \206\147).
Definition get_fresh_state w \206\147 : Ctx := snd (get_fresh w \206\147).
Lemma get_fresh_split :
  forall w \206\147, get_fresh w \206\147 = (get_fresh_pat w \206\147, get_fresh_state w \206\147).
Proof.
(intros).
(rewrite (surjective_pairing (get_fresh w \206\147))).
easy.
Qed.
Lemma get_fresh_merge_valid :
  forall w \206\147 \206\1470 (p : Pat w), (p, \206\147) = get_fresh w \206\1470 -> is_valid (\206\1470 \226\139\147 \206\147).
Proof.
(induction w).
-
(intros \206\147 \206\1470 p H).
(simpl in H).
(inversion H).
(rewrite merge_singleton_append).
validate.
-
(intros \206\147 \206\1470 p H).
(simpl in H).
(inversion H).
(rewrite merge_singleton_append).
validate.
-
(intros \206\147 \206\1470 p H).
(simpl in H).
(inversion H).
(rewrite merge_nil_r).
validate.
-
(intros \206\147 \206\1470 p H).
(simpl in H).
(destruct (get_fresh w1 \206\1470) as [p1 \206\1471] eqn:E1).
symmetry in E1.
specialize (IHw1 _ _ _ E1).
(destruct (\206\1470 \226\139\147 \206\1471) as [| \206\14701] eqn:E\206\14701; try invalid_contradiction).
(destruct (get_fresh w2 \206\14701) as [p2 \206\1472] eqn:E2).
symmetry in E2.
specialize (IHw2 _ _ _ E2).
(rewrite <- E\206\14701 in IHw2).
(rewrite <- merge_assoc in IHw2).
(destruct (\206\1471 \226\139\147 \206\1472) as [| \206\14712] eqn:E\206\14712; try invalid_contradiction).
(inversion H; subst).
easy.
Qed.
Lemma get_fresh_typed :
  forall w \206\1470 p \206\147, (p, \206\147) = get_fresh w \206\1470 -> \206\147 \226\138\162 p :Pat.
Proof.
(induction w; intros \206\1470 p \206\147 E).
-
(simpl in E).
(inversion E).
econstructor.
(apply singleton_singleton).
-
(simpl in E).
(inversion E).
econstructor.
(apply singleton_singleton).
-
(simpl in E).
(inversion E).
constructor.
-
(simpl in E).
(destruct (get_fresh w1 \206\1470) as [p1 \206\1471] eqn:E1).
symmetry in E1.
specialize (get_fresh_merge_valid _ _ _ _ E1) as V1.
(destruct (\206\1470 \226\139\147 \206\1471) as [| \206\14701] eqn:E\206\14701; try invalid_contradiction).
(destruct (get_fresh w2 \206\14701) as [p2 \206\1472] eqn:E2).
symmetry in E2.
specialize (get_fresh_merge_valid _ _ _ _ E2) as V2.
(rewrite <- E\206\14701 in V2).
(rewrite <- merge_assoc in V2).
(destruct (\206\1471 \226\139\147 \206\1472) as [| \206\14712] eqn:E\206\14712; try invalid_contradiction).
(inversion E; subst).
(rewrite <- E\206\14712 in *).
(econstructor; try reflexivity).
validate.
(eapply IHw1).
(apply E1).
(eapply IHw2).
(apply E2).
Qed.
Fixpoint add_fresh w (\206\147 : Ctx) : Pat w * Ctx :=
  match w with
  | One => (unit, \206\147)
  | Bit => (bit (length \206\147), \206\147 ++ [Some Bit])
  | Qubit => (qubit (length \206\147), \206\147 ++ [Some Qubit])
  | w1 \226\138\151 w2 =>
      let (p1, \206\147') := add_fresh w1 \206\147 in
      let (p2, \206\147'') := add_fresh w2 \206\147' in (pair p1 p2, \206\147'')
  end.
Definition add_fresh_pat w (\206\147 : Ctx) : Pat w := fst (add_fresh w \206\147).
Definition add_fresh_state w (\206\147 : Ctx) : Ctx := snd (add_fresh w \206\147).
Lemma add_fresh_split :
  forall w \206\147, add_fresh w \206\147 = (add_fresh_pat w \206\147, add_fresh_state w \206\147).
Proof.
(intros).
(rewrite (surjective_pairing (add_fresh w \206\147))).
easy.
Qed.
Lemma add_fresh_state_merge :
  forall w (\206\147 \206\147' : Ctx),
  \206\147' = add_fresh_state w \206\147 -> Valid \206\147' = \206\147 \226\139\147 get_fresh_state w \206\147.
Proof.
(induction w; intros \206\147 \206\147' H).
-
(unfold add_fresh_state, get_fresh_state in *).
(unfold add_fresh, get_fresh in *).
(simpl in *).
(rewrite merge_singleton_append).
subst.
easy.
-
(unfold add_fresh_state, get_fresh_state in *).
(unfold add_fresh, get_fresh in *).
(simpl in *).
(rewrite merge_singleton_append).
subst.
easy.
-
(unfold add_fresh_state, get_fresh_state in *).
(unfold add_fresh, get_fresh in *).
(simpl in *).
(rewrite merge_nil_r).
(subst; easy).
-
(unfold add_fresh_state, get_fresh_state in *).
specialize (IHw1 \206\147 (snd (add_fresh w1 \206\147)) eq_refl).
(simpl in *).
(destruct (get_fresh w1 \206\147) as [p1 \206\1471] eqn:E1).
(simpl in *).
(destruct (\206\147 \226\139\147 \206\1471) as [| \206\1471'] eqn:E1').
invalid_contradiction.
specialize (IHw2 \206\1471' (snd (add_fresh w2 \206\1471')) eq_refl).
(simpl in *).
(destruct (get_fresh w2 \206\1471') as [p2 \206\1472] eqn:E2).
(simpl in *).
(rewrite <- E1' in IHw2).
(rewrite <- merge_assoc in IHw2).
(destruct (\206\1471 \226\139\147 \206\1472) as [| \206\1472'] eqn:E12).
invalid_contradiction.
(simpl in *).
(rewrite H).
(simpl in *).
(inversion IHw1).
subst.
(destruct (add_fresh w1 \206\147) as [p1' \206\1471''] eqn:A1).
(destruct (add_fresh w2 \206\1471'') as [p2' \206\1472''] eqn:A2).
(rewrite add_fresh_split in A2).
(inversion A2).
(simpl in *).
(rewrite <- IHw2).
easy.
Qed.
Lemma add_fresh_pat_eq : forall w \206\147, add_fresh_pat w \206\147 = get_fresh_pat w \206\147.
Proof.
(induction w; intros \206\147; trivial).
(unfold add_fresh_pat, get_fresh_pat in *; simpl).
(destruct (add_fresh w1 \206\147) as [pa1 \206\147a1] eqn:Ea1).
(destruct (add_fresh w2 \206\147a1) as [pa2 \206\147a2] eqn:Ea2).
(destruct (get_fresh w1 \206\147) as [pg1 \206\147g1] eqn:Eg1).
specialize (get_fresh_merge_valid _ _ _ _ (eq_sym Eg1)) as V1.
(destruct V1 as [\206\1471' M1]).
(rewrite M1).
(destruct (get_fresh w2 \206\1471') as [pg2 \206\147g2] eqn:Eg2).
specialize (get_fresh_merge_valid _ _ _ _ (eq_sym Eg2)) as V2.
(rewrite <- M1 in V2).
(rewrite <- merge_assoc in V2).
(destruct (\206\147g1 \226\139\147 \206\147g2) as [| \206\1472']; try invalid_contradiction).
(simpl).
(rewrite add_fresh_split, get_fresh_split in *).
(inversion Ea1).
(inversion Ea2).
(inversion Eg1).
(inversion Eg2).
(unfold get_fresh_pat, add_fresh_pat in *).
(rewrite IHw1 in *).
(rewrite IHw2 in *).
(apply f_equal2; trivial).
symmetry in H1, H3.
(apply add_fresh_state_merge in H1).
(apply add_fresh_state_merge in H3).
congruence.
Qed.
Lemma add_fresh_typed :
  forall w w0 (p : Pat w) (p0 : Pat w0) \206\147 \206\1470,
  (p, \206\147) = add_fresh w \206\1470 -> \206\1470 \226\138\162 p0 :Pat -> \206\147 \226\138\162 pair p0 p :Pat.
Proof.
(intros w w0 p p0 \206\147 \206\1470 H H0).
(rewrite add_fresh_split in H).
(inversion H).
(erewrite add_fresh_state_merge; [  | reflexivity ]).
econstructor.
3: (apply H0).
2: reflexivity.
(eapply get_fresh_merge_valid).
(rewrite get_fresh_split).
reflexivity.
(rewrite add_fresh_pat_eq).
(eapply get_fresh_typed).
(rewrite get_fresh_split).
reflexivity.
Qed.
Lemma add_fresh_typed_empty :
  forall w (p : Pat w) \206\147, (p, \206\147) = add_fresh w [] -> \206\147 \226\138\162 p :Pat.
Proof.
(intros w p \206\147 H).
specialize (add_fresh_typed _ _ _ _ _ _ H types_unit) as TP.
dependent destruction TP.
(inversion TP1; subst).
(rewrite merge_nil_l in e).
subst.
easy.
Qed.
Definition remove_var (v : Var) (\206\147 : Ctx) : Ctx := trim (update_at \206\147 v None).
Definition change_type (v : Var) (w : WType) (\206\147 : Ctx) :=
  update_at \206\147 v (Some w).
Fixpoint ctx_dom (\206\147 : Ctx) :=
  match \206\147 with
  | [] => []
  | Some w :: \206\147' => 0 :: fmap S (ctx_dom \206\147')
  | None :: \206\147' => fmap S (ctx_dom \206\147')
  end.
Definition remove_pat {w} (p : Pat w) (\206\147 : Ctx) : Ctx :=
  fold_left (fun a x => remove_var x a) (pat_to_list p) \206\147.
Definition process_gate {w1} {w2} (g : Gate w1 w2) :
  Pat w1 -> Ctx -> Pat w2 * Ctx :=
  match g with
  | U _ | BNOT | measQ => fun p st => (p, st)
  | init0 | init1 => fun _ st => add_fresh Qubit st
  | new0 | new1 => fun p st => add_fresh Bit st
  | meas =>
      fun p st => match p with
                  | qubit v => (bit v, change_type v Bit st)
                  end
  | discard | assert0 | assert1 => fun p st => (unit, remove_pat p st)
  end.
Definition process_gate_pat {w1} {w2} (g : Gate w1 w2) :
  Pat w1 -> Ctx -> Pat w2 := fun p st => fst (process_gate g p st).
Definition process_gate_state {w1} {w2} (g : Gate w1 w2) :
  Pat w1 -> Ctx -> Ctx := fun p st => snd (process_gate g p st).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Fixpoint lookup_maybe (x : nat) (ls : list nat) : 
option nat :=
  match ls with
  | [] => None
  | y :: ls' => if x =? y then Some 0 else fmap S (lookup_maybe x ls')
  end.
Fixpoint maps_to (x : nat) (\206\147 : Ctx) : option nat :=
  match x, \206\147 with
  | _, [] => None
  | 0, None :: _ => None
  | 0, Some _ :: _ => Some 0
  | S x', Some _ :: \206\147' => fmap S (maps_to x' \206\147')
  | S x', None :: \206\147' => maps_to x' \206\147'
  end.
Lemma maps_to_singleton : forall v W, maps_to v (singleton v W) = Some O.
Proof.
(induction v; auto).
Qed.
Definition subst_var (\206\147 : Ctx) (x : Var) : Var :=
  match maps_to x \206\147 with
  | Some y => y
  | None => 0
  end.
Fixpoint subst_pat (\206\147 : Ctx) {w} (p : Pat w) : Pat w :=
  match p with
  | unit => unit
  | qubit x => qubit (subst_var \206\147 x)
  | bit x => bit (subst_var \206\147 x)
  | pair p1 p2 => pair (subst_pat \206\147 p1) (subst_pat \206\147 p2)
  end.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Fixpoint flatten_ctx (\206\147 : Ctx) :=
  match \206\147 with
  | [] => []
  | Some w :: \206\147' => Some w :: flatten_ctx \206\147'
  | None :: \206\147' => flatten_ctx \206\147'
  end.
Definition flatten_octx \206\147 :=
  match \206\147 with
  | Valid \206\147' => Valid (flatten_ctx \206\147')
  | Invalid => Invalid
  end.
Lemma SingletonCtx_dom : forall x w \206\147, SingletonCtx x w \206\147 -> ctx_dom \206\147 = [x].
Proof.
(induction 1; simpl; auto).
(rewrite IHSingletonCtx).
auto.
Qed.
Lemma SingletonCtx_flatten :
  forall x w \206\147, SingletonCtx x w \206\147 -> flatten_ctx \206\147 = [Some w].
Proof.
(induction 1; auto).
Qed.
Fixpoint remove_indices (\206\147 : Ctx) (idxs : list nat) : Ctx :=
  match \206\147 with
  | [] => []
  | o :: \206\147' =>
      match idxs with
      | [] => \206\147
      | 0 :: idxs' => remove_indices \206\147' (map pred idxs')
      | S i :: idxs' => o :: remove_indices \206\147' (map pred idxs)
      end
  end.
Fixpoint get_nones (\206\147 : Ctx) : list nat :=
  match \206\147 with
  | [] => []
  | None :: \206\147' => 0 :: map S (get_nones \206\147')
  | Some w :: \206\147' => map S (get_nones \206\147')
  end.
Lemma remove_indices_empty : forall \206\147, remove_indices \206\147 [] = \206\147.
Proof.
(induction \206\147; auto).
Qed.
Lemma remove_indices_merge :
  forall (\206\147 \206\1471 \206\1472 : Ctx) idxs,
  \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472 ->
  remove_indices \206\147 idxs \226\169\181 remove_indices \206\1471 idxs \226\136\153 remove_indices \206\1472 idxs.
Proof.
(intros).
gen idxs.
(apply merge_fun_ind in H).
(dependent induction H; intros).
-
split.
validate.
(rewrite merge_nil_l).
easy.
-
split.
validate.
(rewrite merge_nil_r).
easy.
-
(simpl).
(destruct idxs; [  | destruct n ]).
+
(apply merge_ind_fun).
(constructor; easy).
+
(apply IHmerge_ind; easy).
+
(simpl).
(apply merge_ind_fun).
constructor.
easy.
(apply merge_fun_ind).
(apply IHmerge_ind; easy).
Qed.
Lemma map_unmap : forall l, map pred (map S l) = l.
Proof.
(induction l; intros; auto).
(simpl).
(rewrite IHl).
easy.
Qed.
Lemma remove_flatten :
  forall \206\147, remove_indices \206\147 (get_nones \206\147) = flatten_ctx \206\147.
Proof.
(induction \206\147; trivial).
(simpl).
(destruct a).
-
(destruct (get_nones \206\147) eqn:E).
+
(simpl).
(rewrite <- IH\206\147).
(rewrite remove_indices_empty).
easy.
+
(simpl).
(rewrite <- IH\206\147).
(rewrite map_unmap).
easy.
-
(rewrite map_unmap).
easy.
Qed.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Proposition hoas_to_db_typed :
  forall (\206\147 : Ctx) w (c : Circuit w),
  \206\147 \226\138\162 c :Circ -> Types_DB (flatten_ctx \206\147) (hoas_to_db \206\147 c).
Proof.
(induction 1).
*
(simpl).
constructor.
admit.
*
(simpl).
admit.
*
(simpl).
admit.
Abort.
Definition hoas_to_db_box {w1} {w2} (B : Box w1 w2) : 
  DeBruijn_Box w1 w2 :=
  match B with
  | box f => let (p, \206\147) := add_fresh w1 [] in db_box w1 (hoas_to_db \206\147 (f p))
  end.
Eval compute in hoas_to_db_box (box (fun p : Pat (Qubit \226\138\151 Bit) => output p)).
Lemma fmap_S_seq :
  forall len start, fmap S (seq start len) = seq (S start) len.
Proof.
(induction len as [| len]; intros start; simpl in *; auto).
f_equal.
(rewrite IHlen).
auto.
Qed.
Lemma seq_S :
  forall len start, seq start (S len) = seq start len ++ [start + len].
Proof.
(induction len; intros; simpl).
*
f_equal.
lia.
*
f_equal.
replace (start + S len) with (S start + len)%nat by lia.
(rewrite <- IHlen).
(simpl).
auto.
Qed.

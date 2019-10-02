Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqtgr7LY"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
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
Lemma get_fresh_typed : forall w \206\1470 p \206\147, (p, \206\147) = get_fresh w \206\1470 -> \206\147 \226\138\162 p :Pat.
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

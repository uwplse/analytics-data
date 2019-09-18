Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 71.
Set Silent.
Set Bullet Behavior "Strict Subproofs".
Require Import Coq.Sets.Powerset_facts.
Require Import library.
Definition set_map_fst {ST : Type} (e : Ensemble (ST * ST)%type) :=
  SetPMap e (fun x => Some (fst x)).
Definition set_map_snd {ST : Type} (e : Ensemble (ST * ST)%type) :=
  SetPMap e (fun x => Some (snd x)).
Theorem in_set_map_fst {ST : Type} :
  forall l x, In ST (set_map_fst l) x -> exists y, In _ l (x, y).
Proof.
(intros).
(unfold set_map_fst in *).
(inversion H).
(destruct x0).
(cbn in *).
(inversion H1).
subst.
eauto.
Qed.
Theorem in_set_map_snd {ST : Type} :
  forall l y, In ST (set_map_snd l) y -> exists x, In _ l (x, y).
Proof.
(intros).
(unfold set_map_snd in *).
(inversion H).
(destruct x).
(cbn in *).
(inversion H1).
subst.
eauto.
Qed.
Module AGT_Spec.
Parameter (ST : Type).
Parameter (GT : Type).
Definition SetST := Ensemble ST.
Parameter (Gamma : GT -> SetST).
Parameter (Alpha : SetST -> GT -> Prop).
Parameter
  (alpha_is_partial_function :
     forall S G G', Alpha S G -> Alpha S G' -> G = G').
Definition evidence := (GT * GT)%type.
Parameter (static_pred : ST -> ST -> Prop).
Definition SetST2 := Ensemble (ST * ST).
Definition R (e : evidence) : SetST2 :=
  fun pair =>
  let (T1, T2) := pair in
  static_pred T1 T2 /\
  In _ (Gamma (fst e)) T1 /\ In _ (Gamma (snd e)) T2.
Definition Gamma2 (e : evidence) : SetST2 :=
  fun pair =>
  let (T1, T2) := pair in
  In _ (Gamma (fst e)) T1 /\ In _ (Gamma (snd e)) T2.
Record Alpha2 (eta : SetST2) (e : evidence) : Prop :=
 alpha2_c {proj1 : Alpha (set_map_fst eta) (fst e);
           proj2 : Alpha (set_map_snd eta) (snd e)}.
Definition transitive_closure (left right : SetST2) : SetST2 :=
  fun pair : ST * ST =>
  let (T1, T3) := pair in
  exists T2, In _ left (T1, T2) /\ In _ right (T2, T3).
Definition evidence_composition (e1 e2 e3 : evidence) : Prop :=
  Alpha2 (transitive_closure (R e1) (R e2)) e3.
Parameter
  (gamma_completeness :
     forall e1 e2 e3,
     evidence_composition e1 e2 e3 ->
     transitive_closure (R e1) (R e2) = R e3).
Theorem tc_assoc :
  forall s1 s2 s3 : SetST2,
  transitive_closure (transitive_closure s1 s2) s3 =
  transitive_closure s1 (transitive_closure s2 s3).
Proof.
(intros).
(eapply Extensionality_Ensembles).
(split; unfold Included; intros).
-
(unfold transitive_closure in *).
(unfold In in *).
(cbn in *).
(destruct x).
(destruct H).
(destruct H).
(destruct H).
(destruct H).
eauto.
-
(unfold transitive_closure in *).
(unfold In in *).
(cbn in *).
(destruct x).
(destruct H).
(destruct H).
(destruct H0).
(destruct H0).
eauto.
Qed.
Hint Constructors Alpha2.
Transparent evidence_composition.
Theorem ec_assoc :
  forall e1 e2 e3 e12 e23 el er : evidence,
  evidence_composition e1 e2 e12 ->
  evidence_composition e2 e3 e23 ->
  evidence_composition e12 e3 el ->
  evidence_composition e1 e23 er -> el = er.
Proof.
(intros).
(inversion H).
(inversion H0).
(inversion H1).
(inversion H2).
subst.
(enough
  (transitive_closure (R e12) (R e3) =
   transitive_closure (R e1) (R e23))).
subst.
(rewrite surjective_pairing).
(rewrite surjective_pairing with (p := el)).
(f_equal; eapply alpha_is_partial_function; eauto; rewrite H3; eauto).
(eapply Extensionality_Ensembles).
(split; unfold Included; intros).
-
(eapply gamma_completeness in H).
(eapply gamma_completeness in H0).
(rewrite <- H in *).
(rewrite <- H0 in *).
(rewrite tc_assoc in H3).
eauto.
-
(eapply gamma_completeness in H).
(eapply gamma_completeness in H0).
(rewrite <- H in *).
(rewrite <- H0 in *).
(rewrite <- tc_assoc in H3).
eauto.
Qed.
Parameter
  (alpha_complete : forall S, Inhabited _ S -> exists G, Alpha S G).
Parameter
  (alpha_implies_inhabited : forall S G, Alpha S G -> Inhabited _ S).
Theorem tc_left :
  forall l r x,
  In _ (set_map_fst (transitive_closure l r)) x ->
  In _ (set_map_fst l) x.
Proof.
(intros).
(unfold set_map_fst in *).
(unfold transitive_closure in *).
(cbn in *).
(inversion H).
subst.
(destruct x0).
(cbn in *).
(destruct H0).
(destruct H0).
(econstructor; eauto).
Qed.
Theorem tc_right :
  forall l r x,
  In _ (set_map_snd (transitive_closure l r)) x ->
  In _ (set_map_snd r) x.
Proof.
(intros).
(unfold set_map_snd in *).
(unfold transitive_closure in *).
(cbn in *).
(inversion H).
subst.
(destruct x0).
(cbn in *).
(destruct H0).
(destruct H0).
(econstructor; eauto).
Qed.
Theorem ec_r_exists :
  forall e1 e2 e12 e3 e4,
  evidence_composition e1 e2 e12 ->
  evidence_composition e12 e3 e4 ->
  exists e5, evidence_composition e2 e3 e5.
Proof.
(intros).
(inversion H).
(inversion H0).
subst.
(enough (Inhabited _ (set_map_fst (transitive_closure (R e2) (R e3))))).
(enough (Inhabited _ (set_map_snd (transitive_closure (R e2) (R e3))))).
(eapply alpha_complete in H2).
(eapply alpha_complete in H1).
(destruct H1).
(destruct H2).
exists (x, x0).
(econstructor; cbn; eauto).
-
(unfold set_map_snd in *).
(unfold transitive_closure in *).
(cbn in *).
(inversion H1).
(inversion H2).
(destruct x0).
(inversion H4).
subst.
(unfold In in H3).
(destruct H3).
(cbn).
exists s0.
(unfold In).
(cbn).
(exists (x, s0); eauto).
(cbn).
(exists x0; eauto).
-
(eapply gamma_completeness in H0).
(eapply gamma_completeness in H).
(rewrite <- H in proj5).
(rewrite <- H in proj6).
(rewrite tc_assoc in proj6).
(rewrite tc_assoc in proj5).
(eapply alpha_implies_inhabited in proj6).
(inversion proj6).
(apply tc_right in H1).
(apply in_set_map_snd in H1).
(destruct H1).
(unfold set_map_fst).
econstructor.
(econstructor; eauto).
Qed.
Theorem ec_l_exists :
  forall e1 e2 e3 e23 e4,
  evidence_composition e2 e3 e23 ->
  evidence_composition e1 e23 e4 ->
  exists e5, evidence_composition e1 e2 e5.
Proof.
(intros).
(inversion H).
(inversion H0).
subst.
(enough (Inhabited _ (set_map_fst (transitive_closure (R e1) (R e2))))).
(enough (Inhabited _ (set_map_snd (transitive_closure (R e1) (R e2))))).
(eapply alpha_complete in H2).
(eapply alpha_complete in H1).
(destruct H1).
(destruct H2).
exists (x, x0).
(econstructor; eauto).
-
(unfold set_map_snd in *).
(unfold transitive_closure in *).
(cbn in *).
(inversion H1).
(inversion H2).
(destruct x0).
(inversion H4).
subst.
(unfold In in H3).
(destruct H3).
(cbn).
exists s0.
(unfold In).
(cbn).
(exists (x, s0); eauto).
(cbn).
(exists x0; eauto).
-
(eapply gamma_completeness in H0).
(eapply gamma_completeness in H).
(rewrite <- H in proj5).
(rewrite <- H in proj6).
(rewrite <- tc_assoc in proj6).
(rewrite <- tc_assoc in proj5).
(eapply alpha_implies_inhabited in proj5).
(inversion proj5).
(apply tc_left in H1).
(apply in_set_map_fst in H1).
(destruct H1).
(unfold set_map_snd).
econstructor.
(econstructor; eauto).
Qed.
End AGT_Spec.
Require Import Coq.Lists.List.
Unset Silent.
Set Diffs "off".
Import Coq.Lists.List.ListNotations.
Unset Silent.
Set Diffs "off".
Set Printing Width 66.
Require Export Setoid.
Require Export Relation_Definitions.
Unset Silent.
Set Diffs "off".
Set Printing Width 66.
Set Silent.
Require Import FunInd.
Unset Silent.
Require Import Recdef.
Unset Silent.
Set Diffs "off".
Set Printing Width 66.
Unset Silent.
Set Diffs "off".
Set Printing Width 66.
Set Silent.
Require Import Arith.
Require Import Lia.
Create HintDb math discriminated.
Hint Resolve le_lt_n_Sm: math.
Hint Extern 100  => lia: math.
Unset Silent.
Hint Extern 100  => congruence: math.
Set Silent.
Module AGT_Bounded_Rows_Details.
Definition label := nat.
Inductive ST : Type :=
  | SInt : ST
  | SBool : ST
  | SFun : ST -> ST -> ST
  | SRec : list (option ST) -> ST.
Inductive Ann : Type :=
  | R : Ann
  | O : Ann.
Unset Silent.
Set Diffs "off".
Set Printing Width 66.
Unset Silent.
Set Diffs "off".
Set Printing Width 66.
Unset Silent.
Set Diffs "off".
Set Printing Width 66.
Unset Silent.
Set Diffs "off".
Set Printing Width 66.
Unset Silent.
Set Diffs "off".
Set Printing Width 66.
Set Silent.
Definition FromRow : option (option (Ann * GT)) := None.
Definition AbsentLabel : option (option (Ann * GT)) := Some None.
Unset Silent.
Fixpoint size_gt (G : GT) : nat :=
  match G with
  | GFun G_1 G_2 => 1 + size_gt G_1 + size_gt G_2
  | GRec l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (_, G) => 1 + size_gt G
         | _ => 1
         end + acc) 1 l
  | GRow l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (Some (_, G)) => 1 + size_gt G
         | _ => 1
         end + acc) 1 l
  | _ => 0
  end.
Module GTeq.
Unset Silent.
Set Diffs "off".
Set Printing Width 66.
Unset Silent.
Set Diffs "off".
Set Printing Width 66.
Unset Silent.
Unset Silent.
Set Diffs "off".
Set Printing Width 66.
Unset Silent.
Set Diffs "off".
Set Printing Width 66.
Function
 eq_fn (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GDyn, GDyn) => True
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq_fn (G_11, G_21) /\ eq_fn (G_12, G22)
   | (GRec [], GRec []) => True
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq_fn (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq_fn (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq_fn (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec []) => eq_fn (GRec tl1, GRec [])
   | (GRec [], GRec (None :: tl1)) => eq_fn (GRec [], GRec tl1)
   | (GRow [], GRow []) => True
   | (GRow (Some (Some hd1) :: tl1), GRow
     (Some (Some hd2) :: tl2)) =>
       eq_fn (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq_fn (GRow tl1, GRow tl2)
   | (GRow (None :: tl1), GRow (None :: tl2)) =>
       eq_fn (GRow tl1, GRow tl2)
   | (GRow (Some None :: tl1), GRow (Some None :: tl2)) =>
       eq_fn (GRow tl1, GRow tl2)
   | (GRow (None :: tl1), GRow []) => eq_fn (GRow tl1, GRow [])
   | (GRow [], GRow (None :: tl1)) => eq_fn (GRow [], GRow tl1)
   | _ => False
   end.
all: (intros; subst; simpl; eauto with math).
Set Silent.
all: (try destruct hd1; try destruct hd2; simpl; eauto with math).
Unset Silent.
Defined.
Set Silent.
Definition eq (G_1 G_2 : GT) := eq_fn (G_1, G_2).
Unset Silent.
Unset Silent.
Set Diffs "off".
Set Printing Width 66.
Notation "G_1 === G_2" := (eq G_1 G_2) (at level 100).

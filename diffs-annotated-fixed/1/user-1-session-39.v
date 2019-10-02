Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Bullet Behavior
  "Strict Subproofs".
Require Import
  Coq.Sets.Powerset_facts.
Require Import library.
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
Theorem in_set_map_snd
  {ST : Type} :
  forall l y,
  In ST (set_map_snd l) y ->
  exists x, In _ l (x, y).
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
Variable (ST : Type).
Variable (GT : Type).
Definition SetST := Ensemble ST.
Variable (Gamma : GT -> SetST).
Variable
  (Alpha : SetST -> GT -> Prop).
Variable
  (alpha_is_partial_function :
     forall S G G',
     Alpha S G ->
     Alpha S G' -> G = G').
Definition evidence :=
  (GT * GT)%type.
Variable
  (static_pred :
     ST -> ST -> Prop).
Definition SetST2 :=
  Ensemble (ST * ST).
Definition R (e : evidence) :
  SetST2 :=
  fun pair =>
  let (T1, T2) := pair in
  static_pred T1 T2 /\
  In _ (Gamma (fst e)) T1 /\
  In _ (Gamma (snd e)) T2.
Definition Gamma2 (e : evidence)
  : SetST2 :=
  fun pair =>
  let (T1, T2) := pair in
  In _ (Gamma (fst e)) T1 /\
  In _ (Gamma (snd e)) T2.
Record Alpha2 (eta : SetST2)
(e : evidence) : Prop :=
 alpha2_c {proj1 :
            Alpha
              (set_map_fst eta)
              (fst e);
           proj2 :
            Alpha
              (set_map_snd eta)
              (snd e)}.
Definition transitive_closure
  (left right : SetST2) :
  SetST2 :=
  fun pair : ST * ST =>
  let (T1, T3) := pair in
  exists T2,
    In _ left (T1, T2) /\
    In _ right (T2, T3).
Definition evidence_composition
  (e1 e2 e3 : evidence) :
  Prop :=
  Alpha2
    (transitive_closure 
       (R e1) (R e2)) e3.
Variable
  (gamma_completeness :
     forall e1 e2 e3,
     evidence_composition e1 e2
       e3 ->
     transitive_closure 
       (R e1) (R e2) = 
     R e3).
Theorem tc_assoc :
  forall s1 s2 s3 : SetST2,
  transitive_closure
    (transitive_closure s1 s2)
    s3 =
  transitive_closure s1
    (transitive_closure s2 s3).
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
  forall
    e1 e2 e3 e12 e23 el
     er : evidence,
  evidence_composition e1 e2 e12 ->
  evidence_composition e2 e3 e23 ->
  evidence_composition e12 e3 el ->
  evidence_composition e1 e23 er ->
  el = er.
Proof.
(intros).
(inversion H).
(inversion H0).
(inversion H1).
(inversion H2).
subst.
(enough
  (transitive_closure 
     (R e12) (R e3) =
   transitive_closure 
     (R e1) (R e23))).
subst.
(rewrite surjective_pairing).
(rewrite surjective_pairing with
   (p := el)).
(f_equal;
  eapply
   alpha_is_partial_function;
  eauto; rewrite H3; eauto).
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
Variable
  (alpha_complete :
     forall S,
     Inhabited _ S ->
     exists G, Alpha S G).
Variable
  (alpha_implies_inhabited :
     forall S G,
     Alpha S G -> Inhabited _ S).
Theorem tc_left :
  forall l r x,
  In _
    (set_map_fst
       (transitive_closure l r))
    x -> In _ (set_map_fst l) x.
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
  In _
    (set_map_snd
       (transitive_closure l r))
    x -> In _ (set_map_snd r) x.
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
  exists e5,
    evidence_composition e2 e3
      e5.
Proof.
(intros).
(inversion H).
(inversion H0).
subst.
(enough
  (Inhabited _
     (set_map_fst
        (transitive_closure
           (R e2) (R e3))))).
(enough
  (Inhabited _
     (set_map_snd
        (transitive_closure
           (R e2) (R e3))))).
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
(eapply alpha_implies_inhabited
  in proj6).
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
  exists e5,
    evidence_composition e1 e2
      e5.
Proof.
(intros).
(inversion H).
(inversion H0).
subst.
(enough
  (Inhabited _
     (set_map_fst
        (transitive_closure
           (R e1) (R e2))))).
(enough
  (Inhabited _
     (set_map_snd
        (transitive_closure
           (R e1) (R e2))))).
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
(eapply alpha_implies_inhabited
  in proj5).
(inversion proj5).
(apply tc_left in H1).
(apply in_set_map_fst in H1).
(destruct H1).
(unfold set_map_snd).
econstructor.
(econstructor; eauto).
Qed.
End AGT_Spec.
Require Import Lists.List.
Require Import
  Coq.Lists.ListTactics.
Import
Coq.Lists.List.ListNotations.
Import Coq.Sets.Powerset_facts.
Import library.
Module
  Bounded_Rows_without_ghosts_parameters.
Definition In := Ensembles.In.
Inductive ST : Type :=
  | SInt : ST
  | SBool : ST
  | SFun : ST -> ST -> ST
  | SRec :
      list (option ST) -> ST.
Inductive GT : Type :=
  | GDyn : GT
  | GInt : GT
  | GBool : GT
  | GFun : GT -> GT -> GT
  | GMap :
      list (option Ann) ->
      bool -> GT
with Ann : Type :=
  | Opt : option GT -> Ann
  | Req : GT -> Ann.
Fixpoint size_g (G : GT) : nat
:=
  match G with
  | GFun G1 G2 =>
      1 + size_g G1 + size_g G2
  | GMap l b =>
      fold_right
        (fun x acc =>
         1 +
         match x with
         | Some
           (Opt (Some x)) =>
             size_g x
         | Some (Req x) =>
             size_g x
         | _ => 0
         end + acc) 1 l
  | _ => 1
  end.
Definition SetST := Ensemble ST.
Inductive ForallWR2 {A B : Type}
(R : A -> B -> Prop) :
A -> list A -> list B -> Prop :=
  | ForallWR2_nil :
      forall d,
      ForallWR2 R d [] []
  | ForallWR2_weak :
      forall d hd tl,
      R d hd ->
      ForallWR2 R d [] tl ->
      ForallWR2 R d []
        (hd :: tl)
  | ForallWR2_cons :
      forall d x y l l',
      R x y ->
      ForallWR2 R d l l' ->
      ForallWR2 R d (x :: l)
        (y :: l').
Fixpoint Gamma (S0 : GT) : SetST
:=
  match S0 with
  | GDyn => Full_set _
  | GInt => Singleton _ SInt
  | GBool => Singleton _ SBool
  | GFun S1 S2 =>
      zipWith_ensembles
        (fun T1 T2 => SFun T1 T2)
        (Gamma S1) (Gamma S2)
  | GMap Gmappings is_row =>
      fun T =>
      match T with
      | SRec Smappings =>
          ForallWR2
            (Ensembles.In _)
            (if is_row
             then Full_set _
             else
              Singleton _ None)
            (map
               (fun o =>
                match o with
                | Some
                  (Req S0) =>
                    SetPMap
                     (Gamma S0)
                     (fun X =>
                     Some
                     (Some X))
                | Some
                  (Opt
                   (Some S0)) =>
                    Union _
                     (SetPMap
                     (Gamma S0)
                     (fun X =>
                     Some
                     (Some X)))
                     (Singleton
                     _ None)
                | Some
                  (Opt None) =>
                    Singleton _
                     None
                | None =>
                    if is_row
                    then
                     Full_set _
                    else
                     Singleton _
                     None
                end) Gmappings)
            Smappings
      | _ => False
      end
  end.
Inductive Ensemble_Split
{A : Type} :
Ensemble (list A) ->
list (Ensemble A) -> Prop :=
    ensemble_split_intro :
      forall E1 E2,
      Forall (Inhabited _) E2 ->
      (forall l,
       Ensembles.In _ E1 l <->
       Forall2 (Ensembles.In _)
         E2 l) ->
      Ensemble_Split E1 E2.
Lemma Forall2_impl {A B : Type}
  :
  forall P Q : A -> B -> Prop,
  (forall l1 l2,
   P l1 l2 -> Q l1 l2) ->
  forall l1 l2,
  Forall2 P l1 l2 ->
  Forall2 Q l1 l2.
Proof.
(induction l1; intros;
  inversion H0; subst; eauto).
Qed.
Lemma Forall2_trans
  {A B C : Type} :
  forall (P : A -> B -> Prop)
    (Q : B -> C -> Prop)
    (R : A -> C -> Prop)
    (trans : forall a b c,
             P a b ->
             Q b c -> R a c) 
    l1 l2 l3
    (HP : Forall2 P l1 l2)
    (HQ : Forall2 Q l2 l3),
  Forall2 R l1 l3.
Proof.
(induction l1; intros;
  inversion HP; subst;
  inversion HQ; eauto).
Qed.
Lemma Forall2_trans_weird_P
  {A B C : Type} :
  forall (P : B -> A -> Prop)
    (Q : B -> C -> Prop)
    (R : A -> C -> Prop)
    (trans : forall a b c,
             P b a ->
             Q b c -> R a c) 
    l1 l2 l3
    (HP : Forall2 P l2 l1)
    (HQ : Forall2 Q l2 l3),
  Forall2 R l1 l3.
Proof.
(induction l1; intros;
  inversion HP; subst;
  inversion HQ; eauto).
Qed.
Theorem forall_iff_split
  {A : Type} :
  forall P Q : A -> Prop,
  (forall x, P x <-> Q x) ->
  (forall x, P x -> Q x) /\
  (forall x, Q x -> P x).
Proof.
(intros).
split.
(intros; eauto).
(apply H; auto).
(intros; eauto).
(apply H; auto).
Qed.
Theorem
  forall_inhabited_means_in
  {A : Type} :
  forall l,
  Forall (Inhabited A) l ->
  exists l',
    Forall2 (Ensembles.In _) l
      l'.
Proof.
(induction l; intros; eauto).
(inversion H; subst).
(destruct (IHl H3)).
(inversion H2).
exists (x0 :: x).
eauto.
Qed.
Lemma Ensemble_Split_same_set
  {A : Type} :
  forall l1 l2 S,
  @Ensemble_Split A S l1 ->
  Ensemble_Split S l2 ->
  Forall2 (Same_set _) l1 l2.
Proof.
(induction l1; intros;
  inversion H; inversion H0;
  subst).
(destruct (H2 [])).
(destruct (H6 [])).
specialize
 (H7 (H4 (Forall2_nil _))).
(inversion H7).
eauto.
(destruct l2).
(destruct (H2 [])).
(destruct (H6 [])).
specialize
 (H3 (H8 (Forall2_nil _))).
(inversion H3).
(econstructor; eauto).
(unfold Same_set).
(split; unfold Included; intros).
-
(inversion H1).
subst.
(apply forall_inhabited_means_in
  in H9).
(destruct H9).
(destruct (H2 (x :: x0))).
(destruct (H6 (x :: x0))).
(assert
  (Forall2 (Ensembles.In _)
     (a :: l1) (x :: x0)) by
  eauto).
specialize (H10 (H9 H12)).
(inversion H10).
(subst; eauto).
-
(inversion H5).
subst.
(apply forall_inhabited_means_in
  in H9).
(destruct H9).
(destruct (H2 (x :: x0))).
(destruct (H6 (x :: x0))).
(assert
  (Forall2 (Ensembles.In _)
     (e :: l2) (x :: x0)) by
  eauto).
specialize (H7 (H11 H12)).
(inversion H7).
(subst; eauto).
-
(apply forall_iff_split in H2).
(apply forall_iff_split in H6).
destruct_pairs.
(eapply IHl1 with
   (S := 
     fun tl =>
     exists hd,
       Ensembles.In _ S
         (hd :: tl))).
+
econstructor.
(inversion H1; eauto).
(intros).
(split; intros).
(inversion H7).
specialize (H2 _ H8).
(inversion H2; eauto).
(inversion H1; subst).
(inversion H10).
eexists x.
eauto.
+
econstructor.
(inversion H5; eauto).
(intros).
(split; intros).
(inversion H7).
specialize (H3 _ H8).
(inversion H3; eauto).
(inversion H5; subst).
(inversion H10).
eexists x.
eauto.
Qed.
Theorem Ensemble_Split_eq
  {A : Type} :
  forall l1 l2 S,
  @Ensemble_Split A S l1 ->
  Ensemble_Split S l2 -> l1 = l2.
Proof.
(intros).
(eapply Forall2_ind with
   (R := Same_set _)).
reflexivity.
(intros).
(f_equal;
  [ eapply
     Extensionality_Ensembles
  |  ]; eauto).
(eapply Ensemble_Split_same_set;
  eauto).
Qed.
Inductive Alpha :
SetST -> GT -> Prop :=
  | a_gint :
      Alpha (Singleton _ SInt)
        GInt
  | a_gbool :
      Alpha (Singleton _ SBool)
        GBool
  | a_fun :
      forall S G1 G2,
      Inhabited _ S ->
      (forall x,
       Ensembles.In _ S x ->
       exists T1,
         exists T2,
           x = SFun T1 T2) ->
      Alpha
        (SetPMap S
           (fun x =>
            match x with
            | SFun t1 t2 =>
                Some t1
            | _ => None
            end)) G1 ->
      Alpha
        (SetPMap S
           (fun x =>
            match x with
            | SFun t1 t2 =>
                Some t2
            | _ => None
            end)) G2 ->
      Alpha S (GFun G1 G2)
  | a_map :
      forall S S' r,
      Inhabited _ S ->
      (forall x,
       Ensembles.In _ S x ->
       exists l, x = SRec l) ->
      Ensemble_Split
        (SetPMap S
           (fun x =>
            match x with
            | SRec l => Some l
            | _ => None
            end)) S' ->
      Forall2 AlphaBoundMap S' r ->
      Alpha S (GMap r false)
  | a_dyn :
      forall S,
      Inhabited _ S ->
      S <> Singleton _ SInt ->
      S <> Singleton _ SBool ->
      ~
      (forall x,
       Ensembles.In _ S x ->
       exists T1,
         exists T2,
           x = SFun T1 T2) ->
      ~
      (forall x,
       Ensembles.In _ S x ->
       exists l, x = SRec l) ->
      Alpha S GDyn
with AlphaBoundMap :
Ensemble (option ST) ->
option Ann -> Prop :=
  | abm_none :
      AlphaBoundMap
        (Singleton _ None) None
  | abm_opt :
      forall S G,
      Ensembles.In _ S None ->
      Alpha
        (SetPMap S (fun x => x))
        G ->
      AlphaBoundMap S
        (Some (Opt (Some G)))
  | abm_req :
      forall S G,
      (forall x,
       Ensembles.In _ S x ->
       x <> None) ->
      Alpha
        (SetPMap S (fun x => x))
        G ->
      AlphaBoundMap S
        (Some (Req G)).
Theorem alpha_implies_inhabited
  :
  forall G S,
  Alpha S G -> Inhabited _ S.
Proof.
(intros).
(induction H; eauto).
all:
 (eapply Inhabited_singleton).
Qed.
Theorem
  singleton_none_empty_pmap
  {A : Type} :
  SetPMap
    (Singleton (option A) None)
    (fun x : option A => x) =
  Empty_set _.
Proof.
(apply Extensionality_Ensembles).
(unfold Same_set; split;
  unfold Included; intros).
(inversion H; subst).
(apply Singleton_inv in H0).
congruence.
(inversion H).
Qed.
Lemma inhabited_setpmap_src
  {A B : Type} :
  forall S f,
  Inhabited B (SetPMap S f) ->
  Inhabited A S.
Proof.
(intros).
(inversion H).
(inversion H0).
econstructor.
eauto.
Qed.
Theorem
  alpha_is_partial_function :
  forall G G' S,
  Alpha S G ->
  Alpha S G' -> G = G'.
Proof.
(intros G G').
dependent strong induction
 size_g G + size_g G'
 generalizing G G'.
(intros).
(inversion H; inversion H0;
  subst; try congruence; eauto).
all:
 (try
   match goal with
   | H:Singleton _ _ =
       Singleton _ _
     |- _ =>
         apply singleton_eq in H;
          congruence
   | H:forall x,
       Ensembles.In _
         (Singleton _ _) x -> _
     |- _ =>
         specialize
          (H _
             (In_singleton _ _));
          repeat
           match goal with
           | H:exists _, _
             |- _ => destruct H
           end; try congruence
   end).
-
(f_equal; eapply IH; cbn; eauto
  with math).
-
(inversion H1 as [x H']).
(repeat
  match goal with
  | H:forall x,
      Ensembles.In ?A ?B x -> _,
    H':Ensembles.In ?A ?B _
    |- _ => specialize (H _ H')
  | H:exists _, _
    |- _ => destruct H
  end; subst; congruence).
-
(inversion H1 as [x H']).
(repeat
  match goal with
  | H:forall x,
      Ensembles.In ?A ?B x -> _,
    H':Ensembles.In ?A ?B _
    |- _ => specialize (H _ H')
  | H:exists _, _
    |- _ => destruct H
  end; subst; congruence).
-
f_equal.
(inversion H4; inversion H10;
  clear H4; clear H10; subst;
  eauto;
  pose proof
   (Ensemble_Split_eq _ _ _ H3
      H9); try congruence).
(inversion H4; subst; clear H4).
f_equal.
+
(inversion H5; inversion H13;
  subst; eauto).
all: (try congruence).
*
(pose proof
  (alpha_implies_inhabited _ _
     H12)).
(rewrite
  singleton_none_empty_pmap
  in H4).
(inversion H4).
(inversion H10).
*
(pose proof
  (alpha_implies_inhabited _ _
     H12)).
(rewrite
  singleton_none_empty_pmap
  in H4).
(inversion H4).
(inversion H10).
*
(pose proof
  (alpha_implies_inhabited _ _
     H10)).
(rewrite
  singleton_none_empty_pmap
  in H11).
(inversion H11).
(inversion H12).
*
(repeat f_equal).
(eapply IH; cbn; eauto with math).
*
specialize (H15 _ H4).
congruence.
*
(pose proof
  (alpha_implies_inhabited _ _
     H10)).
(rewrite
  singleton_none_empty_pmap
  in H11).
(inversion H11).
(inversion H12).
*
specialize (H4 _ H15).
congruence.
*
(repeat f_equal).
(eapply IH; cbn; eauto with math).
+
(enough
  (GMap l' false =
   GMap l'0 false)).
(inversion H4; eauto).
(eapply IH with
   (S := 
     SetPMap S
       (fun x =>
        match x with
        | SRec (hd :: tl) =>
            Some (SRec tl)
        | _ => None
        end)); cbn; eauto
  with math).
*
(econstructor; eauto).
--
(eapply Inhabited_SetPMap).
(inversion H1).
specialize (H2 _ H4).
(destruct H2).
subst.
(inversion H3; subst).
(apply forall_iff_split in H10).
(destruct H10).
specialize (H10 x1).
(pose proof H4).
(eapply setpmap_intro in H4).
specialize (H10 H4).
(inversion H10; subst).
(eexists; split).
(eapply H12).
congruence.
auto.
--
(intros).
(inversion H4; subst).
(destruct x1; try congruence;
  destruct l; inversion H11;
  eauto).
--
econstructor.
++
(eapply Forall_impl with
   (P := 
     fun x =>
     exists y',
       AlphaBoundMap x y')).
**
(intros).
(destruct H4).
(inversion H4; subst).
(eapply Inhabited_singleton).
(eapply inhabited_setpmap_src;
  eapply alpha_implies_inhabited;
  eauto).
(eapply inhabited_setpmap_src;
  eapply alpha_implies_inhabited;
  eauto).
**
clear H3 H9 IH H0 H.
generalize dependent l'.
clear.
(induction l0; intros; eauto).
(inversion H6; subst; eauto).
++
(inversion H3).
subst.
(eapply forall_iff_split in H10).
(intros; destruct_pairs; split;
  intros; eauto).
(inversion H12).
subst.
(destruct x; try congruence).
(inversion H16).
subst.
(inversion H15).
(destruct x; try congruence).
(destruct l1; try congruence).
(inversion H18).
subst.
specialize (H10 (o :: l)).
(eapply setpmap_intro in H17).
specialize (H10 H17).
(inversion H10; eauto).
eauto.
(inversion H4).
subst.
(inversion H17).
(assert
  (Forall2 (Ensembles.In _)
     (x0 :: l0) (x :: l)) by
  eauto).
specialize (H11 _ H16).
(inversion H11).
(destruct x1; try congruence).
(inversion H20).
subst.
(repeat econstructor; eauto).
*
(econstructor; eauto).
--
(eapply Inhabited_SetPMap).
(inversion H1).
specialize (H2 _ H4).
(destruct H2).
subst.
(inversion H3; subst).
(apply forall_iff_split in H10).
(destruct H10).
specialize (H10 x1).
(pose proof H4).
(eapply setpmap_intro in H4).
specialize (H10 H4).
(inversion H10; subst).
(eexists; split).
(eapply H12).
congruence.
auto.
--
(intros).
(inversion H4; subst).
(destruct x1; try congruence;
  destruct l; inversion H11;
  eauto).
--
econstructor.
++
(eapply Forall_impl with
   (P := 
     fun x =>
     exists y',
       AlphaBoundMap x y')).
**
(intros).
(destruct H4).
(inversion H4; subst).
(eapply Inhabited_singleton).
(eapply inhabited_setpmap_src;
  eapply alpha_implies_inhabited;
  eauto).
(eapply inhabited_setpmap_src;
  eapply alpha_implies_inhabited;
  eauto).
**
clear H3 H9 IH H0 H.
generalize dependent l'.
clear.
(induction l0; intros; eauto).
(inversion H6; subst; eauto).
++
(inversion H3).
subst.
(eapply forall_iff_split in H10).
(intros; destruct_pairs; split;
  intros; eauto).
(inversion H12).
subst.
(destruct x; try congruence).
(inversion H16).
subst.
(inversion H15).
(destruct x; try congruence).
(destruct l1; try congruence).
(inversion H18).
subst.
specialize (H10 (o :: l)).
(eapply setpmap_intro in H17).
specialize (H10 H17).
(inversion H10; eauto).
eauto.
(inversion H4).
subst.
(inversion H17).
(assert
  (Forall2 (Ensembles.In _)
     (x0 :: l0) (x :: l)) by
  eauto).
specialize (H11 _ H16).
(inversion H11).
(destruct x1; try congruence).
(inversion H20).
subst.
(repeat econstructor; eauto).
Qed.
Reserved Notation "S <: T"
(at level 100).
Definition evidence :=
  (GT * GT)%type.
Inductive static_pred :
ST -> ST -> Prop :=
  | st_int : SInt <: SInt
  | st_bool : SBool <: SBool
  | st_fun :
      forall S_11 S_12 S_21 S_22,
      (S_21 <: S_11) ->
      (S_12 <: S_22) ->
      SFun S_11 S_12 <:
      SFun S_21 S_22
  | st_rec_nil :
      forall l,
      SRec l <: SRec []
  | st_rec_cons_width :
      forall hd1 tl1 tl2,
      (SRec tl1 <: SRec tl2) ->
      SRec (Some hd1 :: tl1) <:
      SRec (None :: tl2)
  | st_rec_cons_depth :
      forall hd1 hd2 tl1 tl2,
      (SRec tl1 <: SRec tl2) ->
      (hd1 <: hd2) ->
      SRec (Some hd1 :: tl1) <:
      SRec (Some hd2 :: tl2)
 where " S <: T" := (static_pred
                     S T).
Definition SetST2 :=
  Ensemble (ST * ST).
Definition R (e : evidence) :
  SetST2 :=
  fun pair =>
  let (T1, T2) := pair in
  static_pred T1 T2 /\
  In _ (Gamma (fst e)) T1 /\
  In _ (Gamma (snd e)) T2.
Definition Gamma2 (e : evidence)
  : SetST2 :=
  fun pair =>
  let (T1, T2) := pair in
  In _ (Gamma (fst e)) T1 /\
  In _ (Gamma (snd e)) T2.
Record Alpha2 (eta : SetST2)
(e : evidence) : Prop :=
 alpha2_c {proj1 :
            Alpha
              (set_map_fst eta)
              (fst e);
           proj2 :
            Alpha
              (set_map_snd eta)
              (snd e)}.
Definition transitive_closure
  (left right : SetST2) :
  SetST2 :=
  fun pair : ST * ST =>
  let (T1, T3) := pair in
  exists T2,
    In _ left (T1, T2) /\
    In _ right (T2, T3).
Definition evidence_composition
  (e1 e2 e3 : evidence) :
  Prop :=
  Alpha2
    (transitive_closure 
       (R e1) (R e2)) e3.
Parameter
  (static_pred_trans :
     forall S T U,
     (S <: T) ->
     (T <: U) -> S <: U).
Parameter
  (static_pred_refl :
     forall S, S <: S).
Variable
  (alpha_sound :
     forall S G,
     Inhabited _ S ->
     Alpha S G ->
     Included _ S (Gamma G)).
Definition less_imprecise
  (t1 t2 : GT) :=
  Included _ (Gamma t1)
    (Gamma t2).
Variable
  (alpha_optimal :
     forall G2 S G1,
     Inhabited _ S ->
     Included _ S (Gamma G2) ->
     Alpha S G1 ->
     less_imprecise G1 G2).
Theorem set_map_fst_in
  {A : Type} :
  forall S (s : A),
  (exists s', In _ S (s, s')) ->
  In _ (set_map_fst S) s.
Proof.
(intros).
(destruct H).
(cbn).
(econstructor; eauto).
Qed.
Theorem set_map_snd_in
  {A : Type} :
  forall S (s : A),
  (exists s', In _ S (s', s)) ->
  In _ (set_map_snd S) s.
Proof.
(intros).
(destruct H).
(cbn).
(econstructor; eauto).
Qed.
Theorem Forall2_impl_ForallWR2
  {A B : Type} :
  forall l1 l2 F d,
  @Forall2 A B F l1 l2 ->
  ForallWR2 F d l1 l2.
Proof.
(intros).
(induction H; econstructor;
  eauto).
Qed.
Theorem Forall2_map
  {A B C : Type} :
  forall (R : C -> B -> Prop)
    (f : A -> C) l1 l2,
  Forall2 (fun x y => R (f x) y)
    l1 l2 ->
  Forall2 R (map f l1) l2.
Proof.
(intros).
(induction H; econstructor;
  eauto).
Qed.
Lemma Included_trans {A : Type}
  :
  forall S1 S2 S3,
  Included A S1 S2 ->
  Included A S2 S3 ->
  Included A S1 S3.
Proof.
(intros).
(unfold Included).
(intros).
eauto.
Qed.
Lemma Included_SetPMap_deoption
  {A : Type} :
  forall S y,
  In A (SetPMap S (fun x => x))
    y -> In _ S (Some y).
Proof.
(intros).
(inversion H).
subst.
eauto.
Qed.
Lemma hyp_to_goal {A B : Prop} :
  forall H : A -> B, A -> B.
Proof.
eauto.
Qed.
Theorem gamma_completeness :
  forall e1 e2 e3,
  evidence_composition e1 e2 e3 ->
  transitive_closure (R e1)
    (R e2) = R e3.
Proof.
(intros e1 e2 e3).
(destruct e1).
(destruct e2).
(destruct e3).
dependent strong induction
 size_g g + size_g g0 +
 size_g g1 + size_g g2 +
 size_g g3 + size_g g4
 generalizing g g0 g1 g2 g3 g4.
(intros).
(apply Extensionality_Ensembles).
(inversion H).
clear H.
(unfold transitive_closure in *).
(unfold Same_set).
(split; unfold Included).
-
(intros).
(destruct x).
Opaque In.
(cbn in *).
(destruct H).
(split; [  | split ]).
+
Transparent In.
(cbn in *).
destruct_pairs.
(eapply static_pred_trans; eauto).
+
(inversion proj3; subst).
*
(cbn in *).
destruct_pairs.
(apply Extension in H1).
(inversion H1).
(unfold Included in *).
(eapply (H7 s)).
(eapply set_map_fst_in).
(cbn).
eexists.
exists x.
(repeat apply conj; eauto).
*
(cbn in *).
destruct_pairs.
(apply Extension in H1).
(inversion H1).
(unfold Included in *).
(eapply (H7 s)).
(change_no_check s with
  (fst (s, s0))).
(eapply set_map_fst_in).
(cbn).
eexists.
exists x.
(repeat apply conj; eauto).
*
(cbn in H).
destruct_pairs.
(assert
  (exists T1 T2, s = SFun T1 T2)).
(eapply H1).
(change_no_check s with
  (fst (s, s0))).
(eapply set_map_fst_in).
(cbn).
eexists.
exists x.
(repeat apply conj; eauto).
(destruct H9 as [T1 [T2 eq]]).
subst.
(eapply zipWith_ensembles_intro).
all: (fold Gamma).
--
(apply alpha_sound in H2).
(eapply H2).
(inversion H; inversion H4;
  subst; try congruence).
(inversion H16).
subst.
(eapply setpmap_intro with
   (x := SFun T1 T2)).
(eapply set_map_fst_in).
eexists.
(cbn).
eexists.
(repeat apply conj; eauto).
eauto.
(inversion H0).
(pose proof (H1 _ H9)).
(destruct H10 as [T1' [T2' eq']]).
econstructor.
(eapply setpmap_intro).
eauto.
(subst; eauto).
--
(apply alpha_sound in H3).
(eapply H3).
(inversion H; inversion H4;
  subst; try congruence).
(inversion H16).
subst.
(eapply setpmap_intro with
   (x := SFun T1 T2)).
(eapply set_map_fst_in).
eexists.
(cbn).
eexists.
(repeat apply conj; eauto).
eauto.
(inversion H0).
(pose proof (H1 _ H9)).
(destruct H10 as [T1' [T2' eq']]).
econstructor.
(eapply setpmap_intro).
eauto.
(subst; eauto).
*
(cbn in H).
destruct_pairs.
(assert (exists l, s = SRec l)).
(eapply H1).
(eapply set_map_fst_in).
(cbn).
eexists.
exists x.
(repeat apply conj; eauto).
(destruct H9 as [l eq]).
subst.
(cbn).
(inversion H2).
clear H2.
subst.
(eapply Forall2_impl_ForallWR2).
(eapply Forall2_map).
(eapply Forall2_trans_weird_P;
  [  | eapply H3 | eapply H10 ]).
2: {
(eapply setpmap_intro with
   (x0 := SRec l)).
(eapply set_map_fst_in).
(cbn).
eexists.
exists x.
(repeat apply conj; eauto).
eauto.
}
(intros).
(inversion H2; subst; eauto).
--
(eenough (Included _ _ _)).
(eapply H14).
eassumption.
(apply alpha_sound in H13).
(unfold Included in H13).
(unfold Included).
(intros).
(destruct x0).
++
(eapply Union_increases_l).
econstructor.
(eapply H13).
(econstructor; eauto).
reflexivity.
++
(eapply Union_increases_r).
(eapply In_singleton).
++
(eapply alpha_implies_inhabited).
eauto.
--
(destruct c).
(econstructor; try reflexivity).
(apply alpha_sound in H13).
(apply H13).
(econstructor; eauto).
(eapply alpha_implies_inhabited).
eauto.
specialize (H12 _ H11).
congruence.
*
(cbn).
econstructor.
+
(inversion proj4; subst).
*
(cbn in *).
destruct_pairs.
(apply Extension in H1).
(inversion H1).
(unfold Included in *).
(eapply (H7 s0)).
(eapply set_map_snd_in).
(cbn).
eexists.
exists x.
(repeat apply conj; eauto).
*
(cbn in *).
destruct_pairs.
(apply Extension in H1).
(inversion H1).
(unfold Included in *).
(eapply (H7 s0)).
(eapply set_map_snd_in).
(cbn).
eexists.
exists x.
(repeat apply conj; eauto).
*
(cbn in H).
destruct_pairs.
(assert
  (exists T1 T2, s0 = SFun T1 T2)).
(eapply H1).
(eapply set_map_snd_in).
(cbn).
eexists.
exists x.
(repeat apply conj; eauto).
(destruct H9 as [T1 [T2 eq]]).
subst.
(eapply zipWith_ensembles_intro).
all: (fold Gamma).
--
(apply alpha_sound in H2).
(eapply H2).
(inversion H4; inversion H;
  subst; try congruence).
(inversion H17).
subst.
(eapply setpmap_intro with
   (x := SFun T1 T2)).
(eapply set_map_snd_in).
eexists.
(cbn).
eexists.
(repeat apply conj;
  [  | eauto |  |  |  |  ];
  eauto).
eauto.
(inversion H0).
(pose proof (H1 _ H9)).
(destruct H10 as [T1' [T2' eq']]).
econstructor.
(eapply setpmap_intro).
eauto.
(subst; eauto).
--
(apply alpha_sound in H3).
(eapply H3).
(inversion H4; inversion H;
  subst; try congruence).
(inversion H17).
subst.
(eapply setpmap_intro with
   (x := SFun T1 T2)).
(eapply set_map_snd_in).
eexists.
(cbn).
eexists.
(repeat apply conj;
  [  | eauto |  |  |  |  ];
  eauto).
eauto.
(inversion H0).
(pose proof (H1 _ H9)).
(destruct H10 as [T1' [T2' eq']]).
econstructor.
(eapply setpmap_intro).
eauto.
(subst; eauto).
*
(cbn in H).
destruct_pairs.
(assert (exists l, s0 = SRec l)).
(eapply H1).
(eapply set_map_snd_in).
(cbn).
eexists.
exists x.
(repeat apply conj; eauto).
(destruct H9 as [l eq]).
subst.
(cbn).
(inversion H2).
clear H2.
subst.
(eapply Forall2_impl_ForallWR2).
(eapply Forall2_map).
(eapply Forall2_trans_weird_P;
  [  | eapply H3 | eapply H10 ]).
2: {
(eapply setpmap_intro with
   (x0 := SRec l)).
(eapply set_map_snd_in).
(cbn).
eexists.
exists x.
(repeat apply conj; eauto).
eauto.
}
(intros).
(inversion H2; subst; eauto).
--
(eenough (Included _ _ _)).
(eapply H14).
eassumption.
(apply alpha_sound in H13).
(unfold Included in H13).
(unfold Included).
(intros).
(destruct x0).
++
(eapply Union_increases_l).
econstructor.
(eapply H13).
(econstructor; eauto).
reflexivity.
++
(eapply Union_increases_r).
(eapply In_singleton).
++
(eapply alpha_implies_inhabited).
eauto.
--
(destruct c).
(econstructor; try reflexivity).
(apply alpha_sound in H13).
(apply H13).
(econstructor; eauto).
(eapply alpha_implies_inhabited).
eauto.
specialize (H12 _ H11).
congruence.
*
(cbn).
econstructor.
-
(intros).
(destruct x).
(simpl in *).
(unfold R in H).
(simpl in H).
(inversion H).
destruct_pairs.
clear H.
(inversion proj3; subst).
+
(apply Extension in H3).
(inversion H1).
subst.
(inversion H0).
subst.
(unfold Same_set in *).
destruct_pairs.
(apply H in H1).
(apply in_set_map_fst in H1).
(destruct H1).
(cbn in H1).
(destruct H1).
destruct_pairs.
eexists.
(inversion H1).
subst.
(inversion H4).
subst.
(repeat (apply conj; simpl);
  eauto).
+
(apply Extension in H3).
(inversion H1).
subst.
(inversion H0).
subst.
(unfold Same_set in *).
destruct_pairs.
(apply H in H1).
(apply in_set_map_fst in H1).
(destruct H1).
(cbn in H1).
(destruct H1).
destruct_pairs.
eexists.
(inversion H1).
subst.
(inversion H4).
subst.
(repeat (apply conj; simpl);
  eauto).
+
(inversion proj4; subst).
*
(inversion H1).
(inversion H2).
subst.
(inversion H0).
*
(inversion H1).
(inversion H2).
subst.
(inversion H0).
*
(inversion H1).
(inversion H2).
subst.
(inversion H0).
subst.
(destruct g).
--
(destruct g0).
(destruct g1).
(destruct g2).
++
specialize (H7 SInt).
(cbn in H7).
Ltac
 spurious_hyp H :=
  match type of H with
  | ?A -> ?B =>
      let H' := fresh "H" in
      enough (H' : B -> False);
       [ exfalso; apply H';
          apply H; clear H'
       | intros ]
  end.
(spurious_hyp H7).
(apply set_map_snd_in).
eexists.
eexists.
(repeat apply conj;
  [ 
  | 
  | 
  | econstructor
  | 
  |  ]).
econstructor.
all: (try eapply Full_intro).
(destruct H12 as [T1 [T2 H']]).
congruence.
++
specialize (H7 SInt).
(cbn in H7).
(spurious_hyp H7).
(apply set_map_snd_in).
eexists.
eexists.
(repeat apply conj;
  [ 
  | 
  | 
  | econstructor
  | 
  |  ]).
econstructor.
all: (try eapply Full_intro).
(eapply In_singleton).
(destruct H12 as [T1 [T2 H']]).
congruence.
++
specialize (H7 SBool).
(cbn in H7).
(spurious_hyp H7).
(apply set_map_snd_in).
eexists.
eexists.
(repeat apply conj;
  [ 
  | 
  | 
  | econstructor
  | 
  |  ]).
econstructor.
all: (try eapply Full_intro).
(eapply In_singleton).
(destruct H12 as [T1 [T2 H']]).
congruence.
++
(* Auto-generated comment: Succeeded. *)


Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
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
Import Coq.Lists.List.ListNotations.
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
Inductive GT : Type :=
  | GDyn : GT
  | GInt : GT
  | GBool : GT
  | GFun : GT -> GT -> GT
  | GRec : list (option (Ann * GT)) -> GT
  | GRow : list (option (option (Ann * GT))) -> GT.
Definition FromRow : option (option (Ann * GT)) := None.
Definition AbsentLabel : option (option (Ann * GT)) := Some None.
Definition SetST := Ensemble ST.
Fixpoint Gamma (G : GT) : SetST :=
  match G with
  | GDyn => Full_set _
  | GInt => Singleton _ SInt
  | GBool => Singleton _ SBool
  | GFun G_1 G_2 => zipWith_ensembles SFun (Gamma G_1) (Gamma G_2)
  | GRec l =>
      fun X =>
      exists l',
        X = SRec l' /\
        Forall2
          (fun (S' : option ST) (G' : option (Ensemble (option ST)))
           =>
           match S', G' with
           | None, None => True
           | S', Some G' => Ensembles.In _ G' S'
           | _, _ => False
           end) l'
          (map
             (option_map
                (fun pair =>
                 match pair return (Ensemble (option ST)) with
                 | (R, G) =>
                     fun OS =>
                     match OS with
                     | None => False
                     | Some T => Ensembles.In _ (Gamma G) T
                     end
                 | (O, G) =>
                     fun OS =>
                     match OS with
                     | None => True
                     | Some T => Ensembles.In _ (Gamma G) T
                     end
                 end)) l)
  | GRow l =>
      fun X =>
      exists l',
        X = SRec l' /\
        Forall2
          (fun (S' : option ST)
             (G' : option (option (Ensemble (option ST)))) =>
           match S', G' with
           | S', None => True
           | S', Some (Some G') => Ensembles.In _ G' S'
           | None, Some None => True
           | _, _ => False
           end) l'
          (map
             (option_map
                (option_map
                   (fun pair =>
                    match pair return (Ensemble (option ST)) with
                    | (R, G) =>
                        fun OS =>
                        match OS with
                        | None => False
                        | Some T => Ensembles.In _ (Gamma G) T
                        end
                    | (O, G) =>
                        fun OS =>
                        match OS with
                        | None => True
                        | Some T => Ensembles.In _ (Gamma G) T
                        end
                    end))) l)
  end.
Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X ->
       X = SRec [] \/ (exists tl, X = SRec (None :: tl))) ->
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) -> Alpha S (GRec (None :: tl))
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (R, hd) :: tl))
  | alpha_rec_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (O, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow [])
  | alpha_row_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X ->
       X = SRec [] \/ (exists tl, X = SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) -> Alpha S (GRow (AbsentLabel :: tl))
  | alpha_row_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRow (Some (Some (R, hd)) :: tl))
  | alpha_row_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd ->
      hd <> GDyn -> Alpha S (GRow (Some (Some (O, hd)) :: tl))
  | alpha_row_cons_row_skip_hd :
      forall S tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) GDyn -> Alpha S (GRow (FromRow :: tl))
  | alpha_gdyn :
      forall S,
      Inhabited _ S ->
      S <> Singleton _ SInt ->
      S <> Singleton _ SBool ->
      ~
      (forall x,
       Ensembles.In _ S x -> exists T1, exists T2, x = SFun T1 T2) ->
      ~ (forall x, Ensembles.In _ S x -> exists l, x = SRec l) ->
      Alpha S GDyn.
Theorem alpha_is_partial_function :
  forall S G G', Alpha S G -> Alpha S G' -> G = G'.
Create HintDb agt discriminated.
Hint Resolve singleton_eq: agt.
Theorem alpha_is_partial_function :
  forall S G G', Alpha S G -> Alpha S G' -> G = G'.
Lemma alpha_fun_inversion :
  forall S,
  (forall X, Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
  forall G, Alpha S G -> exists G_1 G_2, G = GFun G_1 G_2.
Proof.
(intros).
(inversion H0; subst).
-
specialize (H _ (In_singleton _ _)).
(repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end).
congruence.
-
specialize (H _ (In_singleton _ _)).
(repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end).
congruence.
-
eauto.
-
specialize (H _ (In_singleton _ _)).
(repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end).
congruence.
-
(destruct H3).
(apply H in H3).
(repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end).
congruence.
-
(inversion H1).
specialize (H _ H5).
specialize (H2 _ H5).
(repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end).
congruence.
-
(inversion H1).
(* Auto-generated comment: Succeeded. *)


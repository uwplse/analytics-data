Time From iris.algebra Require Export cmra.
Time From iris.base_logic Require Import base_logic.
Time Set Default Proof Using "Type".
Time #[local]Arguments validN _ _ _ !_ /.
Time #[local]Arguments valid _ _ !_ /.
Time Inductive excl (A : Type) :=
       | Excl : A \226\134\146 excl A
       | ExclBot : excl A.
Time Arguments Excl {_} _.
Time Arguments ExclBot {_}.
Time Instance: (Params (@Excl) 1) := { }.
Time Instance: (Params (@ExclBot) 1) := { }.
Time Notation excl' A:= (option (excl A)).
Time Notation Excl' x:= (Some (Excl x)).
Time Notation ExclBot' := (Some ExclBot).
Time
Instance maybe_Excl  {A}: (Maybe (@Excl A)) :=
 (\206\187 x, match x with
       | Excl a => Some a
       | _ => None
       end).
Time Section excl.
Time Context {A : ofeT}.
Time Implicit Types a b : A.
Time Implicit Types x y : excl A.
Time
Inductive excl_equiv : Equiv (excl A) :=
  | Excl_equiv : forall a b, a \226\137\161 b \226\134\146 Excl a \226\137\161 Excl b
  | ExclBot_equiv : ExclBot \226\137\161 ExclBot.
Time Existing Instance excl_equiv.
Time
Inductive excl_dist : Dist (excl A) :=
  | Excl_dist : forall a b n, a \226\137\161{n}\226\137\161 b \226\134\146 Excl a \226\137\161{n}\226\137\161 Excl b
  | ExclBot_dist : forall n, ExclBot \226\137\161{n}\226\137\161 ExclBot.
Time Existing Instance excl_dist.
Time #[global]Instance Excl_ne : (NonExpansive (@Excl A)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance Excl_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (@Excl A)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance Excl_inj : (Inj (\226\137\161) (\226\137\161) (@Excl A)).
Time Proof.
Time by inversion_clear 1.
Time Qed.
Time #[global]Instance Excl_dist_inj  n: (Inj (dist n) (dist n) (@Excl A)).
Time Proof.
Time by inversion_clear 1.
Time Qed.
Time Definition excl_ofe_mixin : OfeMixin (excl A).
Time Proof.
Time (apply (iso_ofe_mixin (maybe Excl))).
Time -
Time by intros [a| ] [b| ]; split; inversion_clear 1; constructor.
Time -
Time by intros n [a| ] [b| ]; split; inversion_clear 1; constructor.
Time Qed.
Time Canonical Structure exclO : ofeT := OfeT (excl A) excl_ofe_mixin.
Time #[global]Instance excl_cofe  `{!Cofe A}: (Cofe exclO).
Time Proof.
Time (apply (iso_cofe (from_option Excl ExclBot) (maybe Excl))).
Time -
Time by intros n [a| ] [b| ]; split; inversion_clear 1; constructor.
Time -
Time by intros []; constructor.
Time Qed.
Time #[global]
Instance excl_ofe_discrete : (OfeDiscrete A \226\134\146 OfeDiscrete exclO).
Time Proof.
Time by inversion_clear 2; constructor; apply (discrete _).
Time Qed.
Time #[global]
Instance excl_leibniz : (LeibnizEquiv A \226\134\146 LeibnizEquiv (excl A)).
Time Proof.
Time by destruct 2; f_equal; apply leibniz_equiv.
Time Qed.
Time #[global]Instance Excl_discrete  a: (Discrete a \226\134\146 Discrete (Excl a)).
Time Proof.
Time by inversion_clear 2; constructor; apply (discrete _).
Time Qed.
Time #[global]Instance ExclBot_discrete : (Discrete (@ExclBot A)).
Time Proof.
Time by inversion_clear 1; constructor.
Time Qed.
Time
Instance excl_valid : (Valid (excl A)) :=
 (\206\187 x, match x with
       | Excl _ => True
       | ExclBot => False
       end).
Time
Instance excl_validN : (ValidN (excl A)) :=
 (\206\187 n x, match x with
         | Excl _ => True
         | ExclBot => False
         end).
Time Instance excl_pcore : (PCore (excl A)) := (\206\187 _, None).
Time Instance excl_op : (Op (excl A)) := (\206\187 x y, ExclBot).
Time Lemma excl_cmra_mixin : CmraMixin (excl A).
Time Proof.
Time (split; try discriminate).
Time -
Time by intros n []; destruct 1; constructor.
Time -
Time by destruct 1; intros ?.
Time -
Time (intros x; split).
Time done.
Time by move  {}=>/(_ 0).
Time -
Time (intros n [?| ]; simpl; auto with lia).
Time -
Time by intros [?| ] [?| ] [?| ]; constructor.
Time -
Time by intros [?| ] [?| ]; constructor.
Time -
Time by intros n [?| ] [?| ].
Time -
Time (intros n x [?| ] [?| ] ? Hx; eexists _,_; inversion_clear Hx; eauto).
Time Qed.
Time Canonical Structure exclR := CmraT (excl A) excl_cmra_mixin.
Time #[global]
Instance excl_cmra_discrete : (OfeDiscrete A \226\134\146 CmraDiscrete exclR).
Time Proof.
Time split.
Time (apply _).
Time by intros [].
Time Qed.
Time
Lemma excl_equivI {M} x y :
  x \226\137\161 y
  \226\138\163\226\138\162@{ uPredI M} match x, y with
                 | Excl a, Excl b => a \226\137\161 b
                 | ExclBot, ExclBot => True
                 | _, _ => False
                 end.
Time Proof.
Time uPred.unseal.
Time (do 2 split).
Time by destruct 1.
Time by destruct x, y; try constructor.
Time Qed.
Time
Lemma excl_validI {M} x :
  \226\156\147 x \226\138\163\226\138\162@{ uPredI M} match x with
                     | ExclBot => False
                     | _ => True
                     end.
Time Proof.
Time uPred.unseal.
Time by destruct x.
Time Qed.
Time #[global]Instance excl_exclusive  x: (Exclusive x).
Time Proof.
Time by destruct x; intros n [].
Time Qed.
Time Lemma excl_validN_inv_l n mx a : \226\156\147{n} (Excl' a \226\139\133 mx) \226\134\146 mx = None.
Time Proof.
Time by destruct mx.
Time Qed.
Time Lemma excl_validN_inv_r n mx a : \226\156\147{n} (mx \226\139\133 Excl' a) \226\134\146 mx = None.
Time Proof.
Time by destruct mx.
Time Qed.
Time Lemma Excl_includedN n a b : Excl' a \226\137\188{n} Excl' b \226\134\146 a \226\137\161{n}\226\137\161 b.
Time Proof.
Time by intros [[c| ] Hb%(inj Some)]; inversion_clear Hb.
Time Qed.
Time Lemma Excl_included a b : Excl' a \226\137\188 Excl' b \226\134\146 a \226\137\161 b.
Time Proof.
Time by intros [[c| ] Hb%(inj Some)]; inversion_clear Hb.
Time Qed.
Time End excl.
Time Arguments exclO : clear implicits.
Time Arguments exclR : clear implicits.
Time
Definition excl_map {A} {B} (f : A \226\134\146 B) (x : excl A) : 
  excl B := match x with
            | Excl a => Excl (f a)
            | ExclBot => ExclBot
            end.
Time Lemma excl_map_id {A} (x : excl A) : excl_map id x = x.
Time Proof.
Time by destruct x.
Time Qed.
Time
Lemma excl_map_compose {A} {B} {C} (f : A \226\134\146 B) (g : B \226\134\146 C) 
  (x : excl A) : excl_map (g \226\136\152 f) x = excl_map g (excl_map f x).
Time Proof.
Time by destruct x.
Time Qed.
Time
Lemma excl_map_ext {A B : ofeT} (f g : A \226\134\146 B) x :
  (\226\136\128 x, f x \226\137\161 g x) \226\134\146 excl_map f x \226\137\161 excl_map g x.
Time Proof.
Time by destruct x; constructor.
Time Qed.
Time
Instance excl_map_ne  {A B : ofeT} n:
 (Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@excl_map A B)).
Time Proof.
Time by intros f f' Hf; destruct 1; constructor; apply Hf.
Time Qed.
Time
Instance excl_map_cmra_morphism  {A B : ofeT} (f : A \226\134\146 B):
 (NonExpansive f \226\134\146 CmraMorphism (excl_map f)).
Time Proof.
Time (split; try done; try apply _).
Time by intros n [a| ].
Time Qed.
Time
Definition exclO_map {A} {B} (f : A -n> B) : exclO A -n> exclO B :=
  OfeMor (excl_map f).
Time Instance exclO_map_ne  A B: (NonExpansive (@exclO_map A B)).
Time Proof.
Time by intros n f f' Hf []; constructor; apply Hf.
Time Qed.
Time #[program]
Definition exclRF (F : oFunctor) : rFunctor :=
  {|
  rFunctor_car := fun A _ B _ => exclR (oFunctor_car F A B);
  rFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg => exclO_map (oFunctor_map F fg) |}.
Time Next Obligation.
Time (intros F A1 ? A2 ? B1 ? B2 ? n x1 x2 ? ?).
Time by apply exclO_map_ne, oFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x; simpl).
Time rewrite -{+2}(excl_map_id x).
Time (<ssreflect_plugin::ssrtclintros@0> apply excl_map_ext =>y).
Time by rewrite oFunctor_id.
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl).
Time rewrite -excl_map_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply excl_map_ext =>y;
  apply oFunctor_compose).
Time Qed.
Time
Instance exclRF_contractive  F:
 (oFunctorContractive F \226\134\146 rFunctorContractive (exclRF F)).
Time Proof.
Time (intros A1 ? A2 ? B1 ? B2 ? n x1 x2 ? ?).
Time by apply exclO_map_ne, oFunctor_contractive.
Time Qed.

Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Lemma cname_eq__decidable :
  forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2;
  (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Open Scope btjnf_scope.
Lemma in_nf_pair__inv :
  forall t1 t2 : ty, InNF( TPair t1 t2) -> InNF( t1) /\ InNF( t2).
Proof.
(intros t1 t2 Hnf).
(inversion Hnf; subst).
(inversion H; subst).
(split; constructor; assumption).
Qed.
Lemma in_nf_union__inv :
  forall t1 t2 : ty, InNF( TUnion t1 t2) -> InNF( t1) /\ InNF( t2).
Proof.
(intros t1 t2 Hnf).
(inversion Hnf; subst).
(inversion H).
(split; assumption).
Qed.
Lemma in_nf_ref__inv : forall t : ty, InNF( TRef t) -> InNF( t).
Proof.
(intros t Hnf).
(inversion Hnf; subst).
(inversion H; subst).
assumption.
Qed.
Lemma unite_pairs__preserves_nf :
  forall t1 t2 : ty, InNF( t1) -> InNF( t2) -> InNF( unite_pairs t1 t2).
Proof.
(intros ta tb Hnfa).
generalize dependent tb.
generalize dependent Hnfa.
generalize dependent ta.
(apply
  (in_nf_mut
     (fun (t1 : ty) (Hat1 : atom_type t1) =>
      forall t2, in_nf t2 -> InNF( unite_pairs t1 t2))
     (fun (t1 : ty) (Hnf1 : in_nf t1) =>
      forall t2, in_nf t2 -> InNF( unite_pairs t1 t2)));
  try (solve
   [ intros;
      match goal with
      | |- InNF( unite_pairs ?tx _) =>
            remember tx as tz eqn:Heqtz ;
             apply
              (in_nf_mut
                 (fun (t2 : ty) (_ : atom_type t2) =>
                  InNF( unite_pairs tz t2))
                 (fun (t2 : ty) (_ : in_nf t2) => InNF( unite_pairs tz t2)));
             try (solve [ subst; intros; simpl; auto with DBBetaJulia ])
      end ])).
Qed.
Lemma unite_pairs_t_union :
  forall t t1 t2 : ty,
  ~ (exists ta tb, t = TUnion ta tb) ->
  unite_pairs t (TUnion t1 t2) = TUnion (unite_pairs t t1) (unite_pairs t t2).
Proof.
(intros t t1 t2 Hcontra).
(destruct t; try (solve [ simpl; reflexivity ])).
exfalso.
(apply Hcontra).
(do 2 eexists).
reflexivity.
Qed.
Ltac resolve_not_union := intros [tx [ty Hcontra]]; inversion Hcontra.
Lemma unite_pairs_union_t :
  forall t1 t2 t' : ty,
  unite_pairs (TUnion t1 t2) t' =
  TUnion (unite_pairs t1 t') (unite_pairs t2 t').
Proof.
(intros t1 t2 t').
(destruct t'; try (solve [ simpl; reflexivity ])).
Qed.
Lemma mk_nf_pair :
  forall t1 t2 : ty, MkNF( TPair t1 t2) = unite_pairs (MkNF( t1)) (MkNF( t2)).
Proof.
reflexivity.
Qed.
Lemma mk_nf_union :
  forall t1 t2 : ty, MkNF( TUnion t1 t2) = TUnion (MkNF( t1)) (MkNF( t2)).
Proof.
reflexivity.
Qed.
Lemma mk_nf_ref : forall t : ty, MkNF( TRef t) = TRef (MkNF( t)).
Proof.
reflexivity.
Qed.
Hint Resolve mk_nf_pair mk_nf_union mk_nf_ref: DBBetaJulia.
Theorem mk_nf__in_nf : forall t : ty, InNF( MkNF( t)).
Proof.
(intros t; induction t;
  try (solve
   [ simpl; auto using unite_pairs__preserves_nf with DBBetaJulia ])).
Qed.
Open Scope btjt.
Lemma inv_depth_pair :
  forall t1 t2 : ty, | TPair t1 t2 | = Nat.max (| t1 |) (| t2 |).
Proof.
reflexivity.
Qed.
Lemma inv_depth_union :
  forall t1 t2 : ty, | TUnion t1 t2 | = Nat.max (| t1 |) (| t2 |).
Proof.
reflexivity.
Qed.
Lemma inv_depth_ref : forall t : ty, | TRef t | = 1 + | t |.
Proof.
reflexivity.
Qed.
Hint Resolve inv_depth_pair inv_depth_union inv_depth_ref: DBBetaJulia.
Lemma max_abac_eq_abc :
  forall a b c : nat,
  Nat.max (Nat.max a b) (Nat.max a c) = Nat.max a (Nat.max b c).
Proof.
(intros a b c).
(rewrite (Nat.max_comm a)).
(rewrite Nat.max_assoc).
(rewrite <- (Nat.max_assoc b)).
(rewrite Nat.max_id).
(rewrite (Nat.max_comm b)).
(rewrite <- Nat.max_assoc).
reflexivity.
Qed.
Lemma max_baca_eq_bca :
  forall a b c : nat,
  Nat.max (Nat.max b a) (Nat.max c a) = Nat.max (Nat.max b c) a.
Proof.
(intros a b c).
(repeat rewrite (Nat.max_comm _ a)).
(apply max_abac_eq_abc).
Qed.
Lemma inv_depth_unite_pairs :
  forall t1 t2 : ty, | unite_pairs t1 t2 | = Nat.max (| t1 |) (| t2 |).
Proof.
(induction t1; induction t2;
  try (solve
   [ simpl; auto
   | rewrite unite_pairs_union_t; simpl; rewrite IHt1_1; rewrite IHt1_2;
      simpl; apply max_baca_eq_bca
   | rewrite unite_pairs_t_union; try resolve_not_union;
      repeat rewrite inv_depth_union; rewrite IHt2_1; 
      rewrite IHt2_2; apply max_abac_eq_abc ])).
Qed.
Lemma max_inv_depth_le__inv :
  forall (t1 t2 : ty) (k : nat),
  Nat.max (| t1 |) (| t2 |) <= k -> | t1 | <= k /\ | t2 | <= k.
Proof.
(intros t1 t2 k Hle).
(split; [ eapply Nat.max_lub_l | eapply Nat.max_lub_r ]; eassumption).
Qed.
Lemma inv_depth_mk_nf : forall t : ty, | MkNF( t) | = | t |.
Proof.
(induction t; simpl; auto).
(rewrite inv_depth_unite_pairs).
auto.
Qed.
Lemma atom_type__value_type : forall t : ty, atom_type t -> value_type t.
Proof.
(apply
  (atom_type_mut (fun (t : ty) (Hat : atom_type t) => value_type t)
     (fun (t : ty) (_ : in_nf t) => True));
  try (solve [ auto with DBBetaJulia ])).
Qed.
Lemma pair_in_nf__value_type :
  forall t1 t2 : ty, InNF( TPair t1 t2) -> value_type (TPair t1 t2).
Proof.
(intros t1 t2 Hnf).
(inversion Hnf; subst).
(apply atom_type__value_type; assumption).
Qed.
Lemma match_ty_pair :
  forall v1 v2 t1 t2 : ty,
  forall k : nat,
  |-[ k] v1 <$ t1 -> |-[ k] v2 <$ t2 -> |-[ k] TPair v1 v2 <$ TPair t1 t2.
Proof.
(intros v1 v2 t1 t2 k Hm1 Hm2).
(destruct k; split; assumption).
Qed.
Lemma match_ty_union_1 :
  forall v t1 t2 : ty,
  forall k : nat, |-[ k] v <$ t1 -> |-[ k] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; left; assumption).
Qed.
Lemma match_ty_union_2 :
  forall v t1 t2 : ty,
  forall k : nat, |-[ k] v <$ t2 -> |-[ k] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; right; assumption).
Qed.
Hint Resolve match_ty_pair: DBBetaJulia.
Hint Resolve match_ty_union_1 match_ty_union_2: DBBetaJulia.
Lemma sem_sub_k__refl : forall (t : ty) (k : nat), ||-[ k][t]<= [t].
Proof.
auto with DBBetaJulia.
Qed.
Lemma sem_sub_k__trans :
  forall (t1 t2 t3 : ty) (k : nat),
  ||-[ k][t1]<= [t2] -> ||-[ k][t2]<= [t3] -> ||-[ k][t1]<= [t3].
Proof.
auto with DBBetaJulia.
Qed.
Lemma sem_eq_k__refl : forall (t : ty) (k : nat), ||-[ k][t]= [t].
Proof.
(intros; split; tauto).
Qed.
Lemma sem_eq_k__comm :
  forall (t1 t2 : ty) (k : nat), ||-[ k][t1]= [t2] -> ||-[ k][t2]= [t1].
Proof.
auto with DBBetaJulia.
(* Auto-generated comment: Failed. *)

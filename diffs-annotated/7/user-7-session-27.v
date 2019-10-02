Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250b.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Open Scope btjnf_scope.
Lemma in_nf_pair__inv : forall t1 t2 : ty, InNF( TPair t1 t2) -> InNF( t1) /\ InNF( t2).
Proof.
(intros t1 t2 Hnf).
(inversion Hnf; subst).
(inversion H; subst).
(split; constructor; assumption).
Qed.
Lemma in_nf_union__inv : forall t1 t2 : ty, InNF( TUnion t1 t2) -> InNF( t1) /\ InNF( t2).
Proof.
(intros t1 t2 Hnf).
(inversion Hnf; subst).
(inversion H).
tauto.
Qed.
Lemma in_nf_ref__inv : forall t : ty, InNF( TRef t) -> InNF( t).
Proof.
(intros t Hnf).
(inversion Hnf; subst).
(inversion H; subst).
assumption.
Qed.
Lemma unite_pairs__preserves_nf : forall t1 t2 : ty, InNF( t1) -> InNF( t2) -> InNF( unite_pairs t1 t2).
Proof.
(intros ta tb Hnfa).
generalize dependent tb.
generalize dependent Hnfa.
generalize dependent ta.
(apply
  (in_nf_mut (fun (t1 : ty) (Hat1 : atom_type t1) => forall t2, in_nf t2 -> InNF( unite_pairs t1 t2))
     (fun (t1 : ty) (Hnf1 : in_nf t1) => forall t2, in_nf t2 -> InNF( unite_pairs t1 t2)));
  try (solve
   [ intros;
      match goal with
      | |- InNF( unite_pairs ?tx _) =>
            remember tx as tz eqn:Heqtz ;
             apply
              (in_nf_mut (fun (t2 : ty) (_ : atom_type t2) => InNF( unite_pairs tz t2))
                 (fun (t2 : ty) (_ : in_nf t2) => InNF( unite_pairs tz t2)));
             try (solve [ subst; intros; simpl; auto with DBBetaJulia ])
      end ])).
Qed.
Lemma unite_pairs_t_union :
  forall t t1 t2 : ty,
  ~ (exists ta tb, t = TUnion ta tb) -> unite_pairs t (TUnion t1 t2) = TUnion (unite_pairs t t1) (unite_pairs t t2).
Proof.
(intros t t1 t2 Hcontra).
(destruct t; try (solve [ simpl; reflexivity ])).
exfalso.
(apply Hcontra).
(do 2 eexists).
reflexivity.
Qed.
Ltac resolve_not_union := intros [tx [ty Hcontra]]; inversion Hcontra.
Lemma unite_pairs_union_t : forall t1 t2 t' : ty, unite_pairs (TUnion t1 t2) t' = TUnion (unite_pairs t1 t') (unite_pairs t2 t').
Proof.
(intros t1 t2 t').
(destruct t'; try (solve [ simpl; reflexivity ])).
Qed.
Lemma unite_pairs_atom_union :
  forall t t1 t2 : ty, atom_type t -> unite_pairs t (TUnion t1 t2) = TUnion (unite_pairs t t1) (unite_pairs t t2).
Proof.
(intros t t1 t2 Hat).
(induction Hat; reflexivity).
Qed.
Lemma unite_pairs_union_atom :
  forall t1 t2 t : ty, atom_type t -> unite_pairs (TUnion t1 t2) t = TUnion (unite_pairs t1 t) (unite_pairs t2 t).
Proof.
(intros t1 t2 t Hat).
(induction Hat; reflexivity).
Qed.
Lemma unite_pairs_of_atomtys : forall ta1 ta2 : ty, atom_type ta1 -> atom_type ta2 -> unite_pairs ta1 ta2 = TPair ta1 ta2.
Proof.
(intros ta1 ta2 Hat1; induction Hat1; intros Hat2; induction Hat2; try (solve [ simpl; reflexivity ])).
Qed.
Lemma mk_nf_pair : forall t1 t2 : ty, MkNF( TPair t1 t2) = unite_pairs (MkNF( t1)) (MkNF( t2)).
Proof.
reflexivity.
Qed.
Lemma mk_nf_union : forall t1 t2 : ty, MkNF( TUnion t1 t2) = TUnion (MkNF( t1)) (MkNF( t2)).
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
(intros t; induction t; try (solve [ simpl; auto using unite_pairs__preserves_nf with DBBetaJulia ])).
Qed.
Theorem mk_nf_nf__equal : forall t : ty, InNF( t) -> MkNF( t) = t.
Proof.
(apply (in_nf_mut (fun (t : ty) (Hat : atom_type t) => MkNF( t) = t) (fun (t : ty) (Hnf : in_nf t) => MkNF( t) = t))).
-
(intros; reflexivity).
-
(intros ta1 ta2 Hat1 IH1 Hat2 IH2).
(simpl).
(rewrite IH1, IH2).
(apply unite_pairs_of_atomtys; assumption).
-
(intros t Hnf IH).
(simpl).
(rewrite IH).
reflexivity.
-
tauto.
-
(intros t1 t2 Hnf1 IH1 Hnf2 IH2).
(simpl).
(rewrite IH1, IH2).
reflexivity.
Qed.
Theorem mk_nf__idempotent : forall t : ty, MkNF( MkNF( t)) = MkNF( t).
Proof.
(intros t).
(apply mk_nf_nf__equal).
(apply mk_nf__in_nf).
Qed.
(* Auto-generated comment: Failed. *)

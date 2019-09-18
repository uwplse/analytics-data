Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Set Printing Width 148.
Set Silent.
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
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
(split; assumption).
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
              (in_nf_mut (fun (t2 : ty) (_ : atom_type t2) => InNF( unite_pairs tz t2)) (fun (t2 : ty) (_ : in_nf t2) => InNF( unite_pairs tz t2)));
             try (solve [ subst; intros; simpl; auto with DBBetaJulia ])
      end ])).
Unset Silent.
Qed.
Set Silent.
Lemma unite_pairs_t_union :
  forall t t1 t2 : ty, ~ (exists ta tb, t = TUnion ta tb) -> unite_pairs t (TUnion t1 t2) = TUnion (unite_pairs t t1) (unite_pairs t t2).
Proof.
(intros t t1 t2 Hcontra).
Unset Silent.
(destruct t; try (solve [ simpl; reflexivity ])).
exfalso.
Set Printing Width 148.
Set Silent.
(apply Hcontra).
Unset Silent.
(do 2 eexists).
reflexivity.
Qed.
Set Silent.
Ltac resolve_not_union := intros [tx [ty Hcontra]]; inversion Hcontra.
Lemma unite_pairs_union_t : forall t1 t2 t' : ty, unite_pairs (TUnion t1 t2) t' = TUnion (unite_pairs t1 t') (unite_pairs t2 t').
Proof.
(intros t1 t2 t').
(destruct t'; try (solve [ simpl; reflexivity ])).
Unset Silent.
Qed.
Set Silent.
Lemma mk_nf_pair : forall t1 t2 : ty, MkNF( TPair t1 t2) = unite_pairs (MkNF( t1)) (MkNF( t2)).
Proof.
reflexivity.
Unset Silent.
Qed.
Set Silent.
Lemma mk_nf_union : forall t1 t2 : ty, MkNF( TUnion t1 t2) = TUnion (MkNF( t1)) (MkNF( t2)).
Proof.
reflexivity.
Unset Silent.
Qed.
Set Silent.
Lemma mk_nf_ref : forall t : ty, MkNF( TRef t) = TRef (MkNF( t)).
Proof.
reflexivity.
Unset Silent.
Qed.
Hint Resolve mk_nf_pair mk_nf_union mk_nf_ref: DBBetaJulia.
Set Silent.
Theorem mk_nf__in_nf : forall t : ty, InNF( MkNF( t)).
Proof.
Unset Silent.
(intros t; induction t; try (solve [ auto using unite_pairs__preserves_nf with DBBetaJulia ])).

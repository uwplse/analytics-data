Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq1RGWLI"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Denotation.
Require Import Composition.
Require Import DBCircuits.
Require Import TypeChecking.
Require Import Symmetric.
Require Import SemanticLib.
Require Import List.
Set Bullet Behavior Strict Subproofs.
Global Unset Asymmetric Patterns.
Require Import Omega.
Delimit Scope bexp_scope with bx.
Open Scope bexp_scope.
Open Scope circ_scope.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Reserved Notation "\226\140\136 b | f \226\140\137" (at level 0).
Fixpoint interpret_bexp (b : bexp) (f : Var -> bool) : bool :=
  match b with
  | b_t => true
  | b_f => false
  | b_var v => f v
  | b_not b => \194\172 \226\140\136 b | f \226\140\137
  | b_and b1 b2 => \226\140\136 b1 | f \226\140\137 && \226\140\136 b2 | f \226\140\137
  | b_xor b1 b2 => \226\140\136 b1 | f \226\140\137 \226\138\149 \226\140\136 b2 | f \226\140\137
  end
where "\226\140\136 b | f \226\140\137" := (interpret_bexp b f).
Reserved Notation "\206\1471 \226\136\170 \206\1472" (at level 30).
Fixpoint classical_merge (\206\1471 \206\1472 : Ctx) :=
  match \206\1471, \206\1472 with
  | [], _ => \206\1472
  | _, [] => \206\1471
  | None :: \206\1471', o :: \206\1472' => o :: \206\1471' \226\136\170 \206\1472'
  | Some w :: \206\1471', _ :: \206\1472' => Some w :: \206\1471' \226\136\170 \206\1472'
  end
where "\206\1471 \226\136\170 \206\1472" := (classical_merge \206\1471 \206\1472).
Fixpoint get_context (b : bexp) : Ctx :=
  match b with
  | b_t => []
  | b_f => []
  | b_var v => singleton v Qubit
  | b_not b => get_context b
  | b_and b1 b2 => get_context b1 \226\136\170 get_context b2
  | b_xor b1 b2 => get_context b1 \226\136\170 get_context b2
  end.
Reserved Notation "\206\1471 \226\138\130 \206\1472" (at level 70).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Lemma classical_merge_nil_l : forall \206\147, [] \226\136\170 \206\147 = \206\147.
Proof.
(destruct \206\147; trivial).
Qed.
Lemma classical_merge_nil_r : forall \206\147, \206\147 \226\136\170 [] = \206\147.
Proof.
(destruct \206\147; trivial).
(simpl).
(destruct o; easy).
Qed.
Lemma subset_classical_merge : forall \206\147 \206\1471 \206\1472, \206\1471 \226\136\170 \206\1472 \226\138\130 \206\147 -> (\206\1471 \226\138\130 \206\147) * (\206\1472 \226\138\130 \206\147).
Proof.
(induction \206\147).
-
(intros \206\1471 \206\1472 H).
(destruct \206\1471, \206\1472).
(split; constructor).
(inversion H).
(destruct o; inversion H).
(destruct o; inversion H).
-
(intros).
(destruct \206\1471, \206\1472).
(split; constructor).
(simpl in H).
(split; [ constructor | easy ]).
(split; [ rewrite classical_merge_nil_r in H; easy | constructor ]).
(destruct a).
(destruct (IH\206\147 \206\1471 \206\1472); auto).
(simpl in H).
(destruct o).
(inversion H; subst).
easy.
(inversion H; subst).
easy.
(split; apply sub_some; easy).
(destruct o, o0; inversion H; subst).
specialize (IH\206\147 _ _ H2) as [S1 S2].
(split; apply sub_none; easy).
Qed.
Fixpoint position_of (v : Var) (\206\147 : Ctx) : nat :=
  match v with
  | 0 => 0
  | S v' =>
      match \206\147 with
      | [] => 0
      | None :: \206\147' => position_of v' \206\147'
      | Some w :: \206\147' => S (position_of v' \206\147')
      end
  end.
Lemma position_of_lt :
  forall v \206\147 W, nth v \206\147 None = Some W -> (position_of v \206\147 < \226\159\166 \206\147 \226\159\167)%nat.
Proof.
(intros v \206\147).
revert v.
(induction \206\147).
-
(simpl).
(destruct v; easy).
-
(intros).
(destruct v).
+
(simpl in H).
subst.
(simpl).
omega.
+
(simpl in *).
specialize (IH\206\147 _ _ H).
(destruct a).
omega.
easy.
Qed.
Lemma singleton_nth_classical :
  forall \206\147 v, singleton v Qubit \226\138\130 \206\147 -> exists W, nth v \206\147 None = Some W.
Proof.
(induction \206\147; intros).
(destruct v; inversion H).
(simpl in *).
(destruct v).
(inversion H).
eauto.
(simpl in *).
(apply IH\206\147).
(inversion H; subst; easy).
Qed.
Fixpoint get_wire {W m} (n : nat) (ps : Pat (m \226\168\130 W)) (default : Pat W) : Pat W.
(destruct m as [| m']).
+
exact default.
+
(simpl in ps).
dependent destruction ps.
(destruct n as [| n']).
-
exact ps1.
-
exact (get_wire W m' n' ps2 default).
Defined.
Lemma get_wire_WT :
  forall \206\147 m n default (p : Pat (m \226\168\130 Qubit)),
  (n < m)%nat ->
  \206\147 \226\138\162 p :Pat ->
  {\206\1471 : OCtx & {\206\1472 : OCtx & \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472 & \206\1471 \226\138\162 get_wire n p default :Pat}}.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq4Orkzk"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Proof.
(intros \206\147 m).
generalize dependent \206\147.
(induction m).
(intros; omega).
(intros \206\147 n default p H H0).
dependent destruction p.
dependent destruction H0.
(destruct n).
-
(simpl).
(unfold solution_left).
(unfold eq_rect_r).
(simpl).
exists \206\1471,\206\1472.
(constructor; trivial).
assumption.
-
(edestruct (IHm \206\1472 n default) as [\206\1471' T]).
omega.
(apply H0_0).
(destruct T as [\206\1472' T]).
(simpl in t).
(simpl).
(unfold solution_left).
(unfold eq_rect_r).
(simpl).
exists \206\1471',(\206\1471 \226\139\147 \206\1472').
2: (apply t).
type_check.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq0vG5Ty"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Fixpoint replace_wire {W m} (p : Pat W) (n : nat) (ps : Pat (m \226\168\130 W)) : Pat (m \226\168\130 W).
(destruct m as [| m']).
+
exact ps.
+
dependent destruction ps.
(destruct n as [| n']).
-
exact (pair p ps2).
-
exact (pair ps1 (replace_wire W m' p n' ps2)).
Defined.
Fixpoint default_wire (W : WType) : Pat W :=
  match W with
  | One => unit
  | Qubit => qubit 0%nat
  | Bit => bit 0%nat
  | Tensor W1 W2 => pair (default_wire W1) (default_wire W2)
  end.
Fixpoint unzip_wires {W m} (n : nat) (ps : Pat (m \226\168\130 W)) :
Pat (n \226\168\130 W) * Pat W * Pat ((m - n - 1) \226\168\130 W).
(destruct m as [| m']).
-
exact (default_wire _, default_wire _, default_wire _)%core.
-
dependent destruction ps.
(destruct n as [| n']).
+
(simpl).
(rewrite Nat.sub_0_r).
exact (unit, ps1, ps2)%core.
+
(simpl).
(apply unzip_wires with (n := n') in ps2).
(destruct ps2 as [[ps1' p] ps2']).
exact (pair ps1 ps1', p, ps2')%core.
Defined.
Fixpoint zip_wires {W m1 m2} (ps1 : Pat (m1 \226\168\130 W)) (p : Pat W) 
(ps2 : Pat (m2 \226\168\130 W)) : Pat ((m1 + m2 + 1) \226\168\130 W).
(destruct m1).
-
(simpl).
(rewrite Nat.add_1_r).
(apply (pair p ps2)).
-
(simpl).
dependent destruction ps1.
specialize (zip_wires _ _ _ ps1_2 p ps2).
exact (pair ps1_1 zip_wires).
Defined.
Fixpoint share_to (n k : nat) : Square (n \226\168\130 Qubit \226\138\151 Qubit) :=
  match n with
  | 0 => id_circ
  | S n' =>
      match k with
      | 0 =>
          box_ qqst
          \226\135\146 (let_ ( (q, qs), t)\226\134\144 output qqst;
             let_ (q, t)\226\134\144 CNOT $ (q, t); ((q, qs), t))
      | S k' =>
          box_ qqst
          \226\135\146 (let_ ( (q, qs), t)\226\134\144 output qqst;
             let_ (qs, t)\226\134\144 share_to n' k' $ (qs, t); ((q, qs), t))
      end
  end.
(* Auto-generated comment: Failed. *)


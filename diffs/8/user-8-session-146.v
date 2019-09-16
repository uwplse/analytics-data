Require Export Contexts.
Require Import List.
Require Import Reals.
Import ListNotations.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Notation CNOT := (ctrl _X).
Notation CCNOT := (ctrl (ctrl _X)).
Notation _S := (_R_ (PI / 2)).
Notation _T := (_R_ (PI / 4)).
Fixpoint trans {W} (U : Unitary W) : Unitary W :=
  match U with
  | _R_ \207\149 => _R_ (- \207\149)
  | ctrl U' => ctrl (trans U')
  | bit_ctrl U' => bit_ctrl (trans U')
  | U' => U'
  end.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Coercion U : Unitary >-> Gate.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Arguments output {w}.
Arguments gate {w} {w1} {w2}.
Arguments lift {w}.
Arguments box {w1} {w2}.
Definition Square_Box W := Box W W.
Definition unbox {w1} {w2} (b : Box w1 w2) (p : Pat w1) : 
  Circuit w2 := match b with
                | box c => c p
                end.
Fixpoint compose {w1 w2} (c : Circuit w1) (f : Pat w1 -> Circuit w2) :
Circuit w2 :=
  match c with
  | output p => f p
  | gate g p c' => gate g p (fun p' => compose (c' p') f)
  | lift p c' => lift p (fun bs => compose (c' bs) f)
  end.
Reserved Notation "\206\147 \226\138\162 c :Circ" (at level 30).
Reserved Notation "\206\147 \226\138\162 f :Fun" (at level 30).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Print Types_Circuit.
Definition Typed_Box {W1 W2 : WType} (b : Box W1 W2) : Set :=
  forall \206\147 (p : Pat W1), \206\147 \226\138\162 p :Pat -> \206\147 \226\138\162 unbox b p :Circ.
Opaque merge.
Opaque Ctx.
Opaque is_valid.
Lemma compose_typing :
  forall \206\1471 \206\1471' \206\147 W W' (c : Circuit W) (f : Pat W -> Circuit W'),
  \206\1471 \226\138\162 c :Circ ->
  \206\147 \226\138\162 f :Fun -> forall {pf : \206\1471' \226\169\181 \206\1471 \226\136\153 \206\147}, \206\1471' \226\138\162 compose c f :Circ.
Proof.
(do 7 intro).
(intros types_c).
generalize dependent \206\1471'.
generalize dependent \206\147.
(dependent induction types_c; intros \206\1470 \206\14701' types_f pf0).
*
(simpl).
subst.
(eapply types_f; eauto).
*
(simpl).
(eapply @types_gate with (\206\1471 := \206\1471) (\206\147 := \206\147 \226\139\147 \206\1470); auto; try solve_merge).
(intros).
(apply H with (\206\1472 := \206\1472) (\206\147 := \206\1470) (\206\1472' := \206\1472 \226\139\147 \206\147); auto; solve_merge).
*
(simpl).
(apply @types_lift with (\206\1471 := \206\1471) (\206\1472 := \206\1472 \226\139\147 \206\1470); auto; try solve_merge).
(intros).
(apply H with (\206\147 := \206\1470); auto; solve_merge).
Qed.
Lemma unbox_typing :
  forall \206\147 W1 W2 (p : Pat W1) (c : Box W1 W2),
  \206\147 \226\138\162 p :Pat -> Typed_Box c -> \206\147 \226\138\162 unbox c p :Circ.
Proof.
(unfold Typed_Box in *).
auto.
Qed.

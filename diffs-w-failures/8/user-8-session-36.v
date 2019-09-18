Require Import DBCircuits.
Require Import TypeChecking.
Require Import Denotation.
Require Import Composition.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Definition valid_ancillae {W} (c : Circuit W) : Prop :=
  forall \206\147 \206\1470 : Ctx, \206\147 \226\138\162 c :Circ -> \226\159\168 \206\1470 | \206\147 \226\138\169 c \226\159\169 = \226\159\168! \206\1470 | \206\147 \226\138\169 c !\226\159\169.
Definition valid_ancillae_box {W1} {W2} (c : Box W1 W2) :=
  Typed_Box c -> denote_box true c = denote_box false c.
Definition valid_ancillae' {W} (c : Circuit W) :=
  forall (\206\147 \206\1470 : Ctx) \207\129,
  \206\147 \226\138\162 c :Circ -> Mixed_State \207\129 -> trace ((\226\159\168! \206\1470 | \206\147 \226\138\169 c !\226\159\169) \207\129) = 1.
Definition valid_ancillae_box' {W1} {W2} (c : Box W1 W2) : Prop :=
  forall \207\129, Typed_Box c -> Mixed_State \207\129 -> trace (denote_box false c \207\129) = 1.
Proposition valid_ancillae_equal :
  forall W (c : Circuit W), valid_ancillae c <-> valid_ancillae' c.
Proof.
(intros).
(unfold valid_ancillae, valid_ancillae').
split.
-
(intros H \206\147 \206\1470 \207\129 H0 H1).
(rewrite <- H; trivial).
(apply mixed_state_trace_1).
admit.
-
(induction c as [| W' W0 g p c IH| IH]).
+
reflexivity.
+
(intros H \206\147 \206\1470 H').
replace (gate g p c) with compose (gate g p (fun p' => output p')) c by auto.
dependent destruction H'.
(destruct \206\1471 as [| \206\1471]; try invalid_contradiction).
(erewrite denote_compose with (\206\1471 := []); trivial).

Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqn3jgCP"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Datatypes.
Require Export TypeChecking.
Require Export HOASLib.
Import ListNotations.
Open Scope list_scope.
Open Scope circ_scope.
Definition new_discard : Box One One :=
  box_ () \226\135\146 (let_ b \226\134\144 new0 $ (); discard_ b; ()).
Lemma new_discard_WT : Typed_Box new_discard.
Proof.
type_check.
Qed.
Definition init_discard : Box One One := box_ () \226\135\146 discard $ meas $ init0 $ ().
Lemma init_discard_WT : Typed_Box init_discard.
Proof.
type_check.
Qed.
Definition hadamard_measure : Box Qubit Bit := box_ q \226\135\146 meas $ _H $ q.
Lemma hadamard_measure_WT : Typed_Box hadamard_measure.
Proof.
type_check.
Qed.
Definition U_deutsch (U__f : Unitary (Qubit \226\138\151 Qubit)) : 
  Box One Bit :=
  box_ () \226\135\146 (let_ x \226\134\144 init0 $ ();
             let_ x \226\134\144 _H $ x;
             let_ y \226\134\144 init1 $ ();
             let_ y \226\134\144 _H $ y;
             let_ (x, y)\226\134\144 U__f $ (x, y);
             let_ x \226\134\144 _H $ x; let_ y \226\134\144 meas $ y; let_ () \226\134\144 discard $ y; meas $ x).
Lemma U_deutsch_WT : forall U__f, Typed_Box (U_deutsch U__f).
Proof.
type_check.
Qed.
Definition lift_deutsch (U__f : Square_Box (Qubit \226\138\151 Qubit)) : 
  Box One Bit :=
  box_ () \226\135\146 (let_ x \226\134\144 init0 $ ();
             let_ x \226\134\144 _H $ x;
             let_ y \226\134\144 init1 $ ();
             let_ y \226\134\144 _H $ y;
             let_ (x, y)\226\134\144 U__f $ (x, y);
             let_ y \226\134\144 meas $ y; let_ x \226\134\144 _H $ x; lift_ _ \226\134\144 y; meas $ x).
Lemma lift_deutsch_WT : forall U__f, Typed_Box U__f -> Typed_Box (lift_deutsch U__f).
Proof.
type_check.
Qed.
Definition deutsch_basic (U__f : Square_Box (Qubit \226\138\151 Qubit)) : 
  Box One Bit :=
  box_ () \226\135\146 (gate_ x \226\134\144 init0 @ ();
             gate_ x \226\134\144 _H @ x;
             gate_ y \226\134\144 init1 @ ();
             gate_ y \226\134\144 _H @ y;
             let_ (x, y)\226\134\144 unbox U__f (x,, y);
             gate_ y \226\134\144 meas @ y;
             gate_ () \226\134\144 discard @ y; gate_ x \226\134\144 _H @ x; gate_ x \226\134\144 meas @ x; output x).
Definition deutsch (U__f : Square_Box (Qubit \226\138\151 Qubit)) : 
  Box One Bit :=
  box_ () \226\135\146 (let_ x \226\134\144 _H $ init0 $ ();
             let_ y \226\134\144 _H $ init1 $ ();
             let_ (x, y)\226\134\144 U__f $ (x, y); let_ () \226\134\144 discard $ meas $ y; meas $ _H $ x).
Lemma deutsch_WF : forall U__f, Typed_Box U__f -> Typed_Box (deutsch U__f).
Proof.
type_check.
Qed.
Lemma deutsch_basic_eq : forall U__f, deutsch_basic U__f = deutsch U__f.
Proof.
(intros U__f).
(unfold deutsch, deutsch_basic).
(unfold apply_box).
(simpl).
easy.
Qed.
Definition Deutsch_Jozsa (n : nat) (U : Box (S n \226\168\130 Qubit) (S n \226\168\130 Qubit)) :
  Box One (n \226\168\130 Bit) :=
  box_ () \226\135\146 (let_ qs \226\134\144 _H # n $ init0 # n $ (());
             let_ q \226\134\144 _H $ init1 $ ();
             let_ (q, qs)\226\134\144 U $ (q, qs);
             let_ () \226\134\144 discard $ meas $ q; meas # n $ _H # n $ qs).
Lemma Deutsch_Jozsa_WT :
  forall n U__f, Typed_Box U__f -> Typed_Box (Deutsch_Jozsa n U__f).
Proof.
(intros n U__f U_WT).
(induction n).
+
type_check.
+
specialize inParMany_WT as WT_Par.
specialize types_units as WT_units.
type_check.
(apply WT_Par).
all: (try apply WT_Par).
all: type_check.
(apply types_units).
Qed.
Definition Deutsch_Jozsa' (n : nat)
  (U : Box (n \226\168\130 Qubit \226\138\151 Qubit) (n \226\168\130 Qubit \226\138\151 Qubit)) : Box One (n \226\168\130 Bit) :=
  box_ () \226\135\146 (let_ qs \226\134\144 _H # n $ init0 # n $ (());
             let_ q \226\134\144 _H $ init1 $ ();
             let_ (qs, q)\226\134\144 U $ (qs, q);
             let_ () \226\134\144 discard $ meas $ q; meas # n $ _H # n $ qs).
Lemma Deutsch_Jozsa_WT' :
  forall n U__f, Typed_Box U__f -> Typed_Box (Deutsch_Jozsa n U__f).
Proof.
(intros n U__f U_WT).
(induction n).
+
type_check.
+
specialize inParMany_WT as WT_Par.
specialize types_units as WT_units.
type_check.
(apply WT_Par).
all: (try apply WT_Par).
all: type_check.
(apply types_units).
Qed.
Definition bell00 : Box One (Qubit \226\138\151 Qubit) :=
  box_ () \226\135\146 (let_ a \226\134\144 _H $ init0 $ (); let_ b \226\134\144 init0 $ (); CNOT $ (a, b)).
Lemma bell00_WT : Typed_Box bell00.
Proof.
type_check.
Qed.
Definition bell_old_style : Box One (Qubit \226\138\151 Qubit) :=
  box_ () \226\135\146 (gate_ a \226\134\144 init0 @ ();
             gate_ b \226\134\144 init0 @ ();
             gate_ a \226\134\144 _H @ a; gate_ (a, b)\226\134\144 CNOT @ (a,, b); output (a,, b)).
Lemma bell_old_style_WT : Typed_Box bell_old_style.
Proof.
type_check.
Qed.
Definition bell_one_line : Box One (Qubit \226\138\151 Qubit) :=
  box_ () \226\135\146 CNOT $ (_H $ init0 $ (), init0 $ ()).
Lemma bell_one_line_WT : Typed_Box bell_one_line.
Proof.
type_check.
Qed.
Definition alice : Box (Qubit \226\138\151 Qubit) (Bit \226\138\151 Bit) :=
  box_ qa
  \226\135\146 (let_ (q, a)\226\134\144 CNOT $ qa; let_ x \226\134\144 meas $ _H $ q; let_ y \226\134\144 meas $ a; (x, y)).
Lemma alice_WT : Typed_Box alice.
Proof.
type_check.
Qed.
Definition bob : Box (Bit \226\138\151 Bit \226\138\151 Qubit) Qubit :=
  box_ (x, y, b)
  \226\135\146 (let_ (y, b)\226\134\144 bit_ctrl _X $ (y, b);
     let_ (x, b)\226\134\144 bit_ctrl _Z $ (x, b); discard_ (x, y); b).
Lemma bob_WT : Typed_Box bob.
Proof.
type_check.
Qed.
Definition teleport :=
  box_ q \226\135\146 (let_ (a, b)\226\134\144 bell00 $ (); let_ (x, y)\226\134\144 alice $ (q, a); bob $ (x, y, b)).
Lemma teleport_WT : Typed_Box teleport.
Proof.
type_check.
Defined.
Definition bob_lift : Box (Bit \226\138\151 Bit \226\138\151 Qubit) Qubit :=
  box_ (x, y, b)
  \226\135\146 (lift_ (u, v)\226\134\144 (x, y);
     let_ b \226\134\144 (if v then _X else id_circ) $ b;
     let_ b \226\134\144 (if u then _Z else id_circ) $ b; b).
Lemma bob_lift_WT : Typed_Box bob_lift.
Proof.
type_check.
Defined.
Program
Definition bob_lift' : Box (Bit \226\138\151 Bit \226\138\151 Qubit) Qubit :=
  box_ (x, y, b)
  \226\135\146 (lift_ (u, v)\226\134\144 (x, y);
     match u, v with
     | true, true => let_ b \226\134\144 _X $ b; _Z $ b
     | true, false => _Z $ b
     | false, true => _X $ b
     | false, false => b
     end).
Lemma bob_lift_WT' : Typed_Box bob_lift'.
Proof.
type_check.
Defined.
Definition teleport_lift : Box Qubit Qubit :=
  box_ q
  \226\135\146 (let_ (a, b)\226\134\144 bell00 $ (); let_ (x, y)\226\134\144 alice $ (q, a); bob_lift $ (x, y, b)).
Lemma teleport_lift_WT : Typed_Box teleport_lift.
Proof.
type_check.
Defined.
Definition bob_distant (u v : bool) : Box Qubit Qubit :=
  box_ b
  \226\135\146 (let_ b \226\134\144 (if v then _X else id_circ) $ b;
     let_ b \226\134\144 (if u then _Z else id_circ) $ b; output b).
Lemma bob_distant_WT : forall b1 b2, Typed_Box (bob_distant b1 b2).
Proof.
type_check.
Defined.
Definition teleport_distant : Box Qubit Qubit :=
  box_ q
  \226\135\146 (let_ (a, b)\226\134\144 bell00 $ ();
     let_ (x, y)\226\134\144 alice $ (q, a); lift_ (u, v)\226\134\144 (x, y); bob_distant u v $ b).
Lemma teleport_distant_WT : Typed_Box teleport_distant.
Proof.
type_check.
Qed.
Definition superdense : Box (Bit \226\138\151 Bit) (Bit \226\138\151 Bit) :=
  box_ (b1, b2)
  \226\135\146 (let_ (a, b)\226\134\144 bell00 $ (); let_ q \226\134\144 bob $ (b1, b2, b); alice $ (q, a)).
Lemma superdense_WT : Typed_Box superdense.
Proof.
type_check.
Qed.
Definition superdense_distant (b1 b2 : bool) : Box One (Bit \226\138\151 Bit) :=
  box_ () \226\135\146 (let_ (a, b)\226\134\144 bell00 $ ();
             let_ q \226\134\144 bob_distant b1 b2 $ b; alice $ (q, a)).
Lemma superdense_distant_WT : forall b1 b2, Typed_Box (superdense_distant b1 b2).
Proof.
type_check.
Qed.
Require Import Reals.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq8FnGtt"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Definition _R'_ (m : nat) := _R_ (2 * PI / INR (2 ^ m)).
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqLDAawB"
Print Ltac Signatures.

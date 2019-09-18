Time From iris.bi Require Export interface.
Time From iris.algebra Require Import monoid.
Time
Definition bi_iff {PROP : bi} (P Q : PROP) : PROP := ((P \226\134\146 Q) \226\136\167 (Q \226\134\146 P))%I.
Time Arguments bi_iff {_} _%I _%I : simpl never.
Time Instance: (Params (@bi_iff) 1) := { }.
Time Infix "\226\134\148" := bi_iff : bi_scope.
Time
Definition bi_wand_iff {PROP : bi} (P Q : PROP) : PROP :=
  ((P -\226\136\151 Q) \226\136\167 (Q -\226\136\151 P))%I.
Time Arguments bi_wand_iff {_} _%I _%I : simpl never.
Time Instance: (Params (@bi_wand_iff) 1) := { }.
Time Infix "\226\136\151-\226\136\151" := bi_wand_iff : bi_scope.
Time Class Persistent {PROP : bi} (P : PROP) :=
         persistent : P \226\138\162 <pers> P.
Time Arguments Persistent {_} _%I : simpl never.
Time Arguments persistent {_} _%I {_}.
Time Hint Mode Persistent + !: typeclass_instances.
Time Instance: (Params (@Persistent) 1) := { }.
Time Definition bi_affinely {PROP : bi} (P : PROP) : PROP := (emp \226\136\167 P)%I.
Time Arguments bi_affinely {_} _%I : simpl never.
Time Instance: (Params (@bi_affinely) 1) := { }.
Time Typeclasses Opaque bi_affinely.
Time Notation "'<affine>' P" := (bi_affinely P) : bi_scope.
Time Class Affine {PROP : bi} (Q : PROP) :=
         affine : Q \226\138\162 emp.
Time Arguments Affine {_} _%I : simpl never.
Time Arguments affine {_} _%I {_}.
Time Hint Mode Affine + !: typeclass_instances.
Time
Class BiAffine (PROP : bi) :=
    absorbing_bi : forall Q : PROP, Affine Q.
Time Hint Mode BiAffine !: typeclass_instances.
Time Existing Instance absorbing_bi |0.
Time
Class BiPositive (PROP : bi) :=
    bi_positive : forall P Q : PROP, <affine> (P \226\136\151 Q) \226\138\162 <affine> P \226\136\151 Q.
Time Hint Mode BiPositive !: typeclass_instances.
Time Definition bi_absorbingly {PROP : bi} (P : PROP) : PROP := (True \226\136\151 P)%I.
Time Arguments bi_absorbingly {_} _%I : simpl never.
Time Instance: (Params (@bi_absorbingly) 1) := { }.
Time Typeclasses Opaque bi_absorbingly.
Time Notation "'<absorb>' P" := (bi_absorbingly P) : bi_scope.
Time Class Absorbing {PROP : bi} (P : PROP) :=
         absorbing : <absorb> P \226\138\162 P.
Time Arguments Absorbing {_} _%I : simpl never.
Time Arguments absorbing {_} _%I.
Time Hint Mode Absorbing + !: typeclass_instances.
Time
Definition bi_persistently_if {PROP : bi} (p : bool) 
  (P : PROP) : PROP := (if p then <pers> P else P)%I.
Time Arguments bi_persistently_if {_} !_ _%I /.
Time Instance: (Params (@bi_persistently_if) 2) := { }.
Time Typeclasses Opaque bi_persistently_if.
Time Notation "'<pers>?' p P" := (bi_persistently_if p P) : bi_scope.
Time
Definition bi_affinely_if {PROP : bi} (p : bool) (P : PROP) : PROP :=
  (if p then <affine> P else P)%I.
Time Arguments bi_affinely_if {_} !_ _%I /.
Time Instance: (Params (@bi_affinely_if) 2) := { }.
Time Typeclasses Opaque bi_affinely_if.
Time Notation "'<affine>?' p P" := (bi_affinely_if p P) : bi_scope.
Time
Definition bi_absorbingly_if {PROP : bi} (p : bool) 
  (P : PROP) : PROP := (if p then <absorb> P else P)%I.
Time Arguments bi_absorbingly_if {_} !_ _%I /.
Time Instance: (Params (@bi_absorbingly_if) 2) := { }.
Time Typeclasses Opaque bi_absorbingly_if.
Time Notation "'<absorb>?' p P" := (bi_absorbingly_if p P) : bi_scope.
Time
Definition bi_intuitionistically {PROP : bi} (P : PROP) : PROP :=
  (<affine> <pers> P)%I.
Time Arguments bi_intuitionistically {_} _%I : simpl never.
Time Instance: (Params (@bi_intuitionistically) 1) := { }.
Time Typeclasses Opaque bi_intuitionistically.
Time Notation "\226\150\161 P" := (bi_intuitionistically P) : bi_scope.
Time
Definition bi_intuitionistically_if {PROP : bi} (p : bool) 
  (P : PROP) : PROP := (if p then \226\150\161 P else P)%I.
Time Arguments bi_intuitionistically_if {_} !_ _%I /.
Time Instance: (Params (@bi_intuitionistically_if) 2) := { }.
Time Typeclasses Opaque bi_intuitionistically_if.
Time Notation "'\226\150\161?' p P" := (bi_intuitionistically_if p P) : bi_scope.
Time
Fixpoint sbi_laterN {PROP : sbi} (n : nat) (P : PROP) : PROP :=
  match n with
  | O => P
  | S n' => \226\150\183 sbi_laterN n' P
  end%I.
Time Arguments sbi_laterN {_} !_%nat_scope _%I.
Time Instance: (Params (@sbi_laterN) 2) := { }.
Time Notation "\226\150\183^ n P" := (sbi_laterN n P) : bi_scope.
Time Notation "\226\150\183? p P" := (sbi_laterN (Nat.b2n p) P) : bi_scope.
Time
Definition sbi_except_0 {PROP : sbi} (P : PROP) : PROP := (\226\150\183 False \226\136\168 P)%I.
Time Arguments sbi_except_0 {_} _%I : simpl never.
Time Notation "\226\151\135 P" := (sbi_except_0 P) : bi_scope.
Time Instance: (Params (@sbi_except_0) 1) := { }.
Time Typeclasses Opaque sbi_except_0.
Time Class Timeless {PROP : sbi} (P : PROP) :=
         timeless : \226\150\183 P \226\138\162 \226\151\135 P.
Time Arguments Timeless {_} _%I : simpl never.
Time Arguments timeless {_} _%I {_}.
Time Hint Mode Timeless + !: typeclass_instances.
Time Instance: (Params (@Timeless) 1) := { }.
Time
Definition bi_wandM {PROP : bi} (mP : option PROP) 
  (Q : PROP) : PROP := match mP with
                       | None => Q
                       | Some P => (P -\226\136\151 Q)%I
                       end.
Time Arguments bi_wandM {_} !_%I _%I /.
Time
Notation "mP -\226\136\151? Q" := (bi_wandM mP Q)
  (at level 99, Q  at level 200, right associativity) : bi_scope.

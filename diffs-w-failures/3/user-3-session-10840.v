Time From stdpp Require Export base tactics.
Time Set Default Proof Using "Type".
Time Section definitions.
Time Context {A T : Type} `{EqDecision A}.
Time #[global]
Instance fn_insert : (Insert A T (A \226\134\146 T)) :=
 (\206\187 a t f b, if decide (a = b) then t else f b).
Time #[global]
Instance fn_alter : (Alter A T (A \226\134\146 T)) :=
 (\206\187 (g : T \226\134\146 T) a f b, if decide (a = b) then g (f a) else f b).
Time End definitions.
Time Section functions.
Time Context {A T : Type} `{!EqDecision A}.
Time Lemma fn_lookup_insert (f : A \226\134\146 T) a t : <[a:=t]> f a = t.
Time Proof.
Time (unfold insert, fn_insert).
Time by destruct (decide (a = a)).
Time Qed.
Time
Lemma fn_lookup_insert_rev (f : A \226\134\146 T) a t1 t2 : <[a:=t1]> f a = t2 \226\134\146 t1 = t2.
Time Proof.
Time (rewrite fn_lookup_insert).
Time congruence.
Time Qed.
Time
Lemma fn_lookup_insert_ne (f : A \226\134\146 T) a b t : a \226\137\160 b \226\134\146 <[a:=t]> f b = f b.
Time Proof.
Time (unfold insert, fn_insert).
Time by destruct (decide (a = b)).
Time Qed.
Time
Lemma fn_lookup_alter (g : T \226\134\146 T) (f : A \226\134\146 T) a : alter g a f a = g (f a).
Time Proof.
Time (unfold alter, fn_alter).
Time by destruct (decide (a = a)).
Time Qed.
Time
Lemma fn_lookup_alter_ne (g : T \226\134\146 T) (f : A \226\134\146 T) a 
  b : a \226\137\160 b \226\134\146 alter g a f b = f b.
Time Proof.
Time (unfold alter, fn_alter).
Time by destruct (decide (a = b)).
Time Qed.
Time End functions.

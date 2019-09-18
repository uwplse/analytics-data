Time From Coq Require Import Ascii.
Time From Coq Require Export String.
Time From stdpp Require Export list.
Time From stdpp Require Import countable.
Time Set Default Proof Using "Type".
Time Notation length := List.length.
Time Open Scope string_scope.
Time Open Scope list_scope.
Time
Infix "+:+" := String.append (at level 60, right associativity) : stdpp_scope.
Time Arguments String.append : simpl never.
Time Instance ascii_eq_dec : (EqDecision ascii) := ascii_dec.
Time Instance string_eq_dec : (EqDecision string).
Time Proof.
Time solve_decision.
Time Defined.
Time Instance string_app_inj : (Inj (=) (=) (String.append s1)).
Time Proof.
Time (intros s1 ? ? ?).
Time (induction s1; simplify_eq /=; f_equal /=; auto).
Time Qed.
Time Instance string_inhabited : (Inhabited string) := (populate "").
Time
Fixpoint string_rev_app (s1 s2 : string) : string :=
  match s1 with
  | "" => s2
  | String a s1 => string_rev_app s1 (String a s2)
  end.
Time Definition string_rev (s : string) : string := string_rev_app s "".
Time
Definition is_nat (x : ascii) : option nat :=
  match x with
  | "0" => Some 0
  | "1" => Some 1
  | "2" => Some 2
  | "3" => Some 3
  | "4" => Some 4
  | "5" => Some 5
  | "6" => Some 6
  | "7" => Some 7
  | "8" => Some 8
  | "9" => Some 9
  | _ => None
  end%char.
Time
Definition is_space (x : Ascii.ascii) : bool :=
  match x with
  | "009" | "010" | "011" | "012" | "013" | " " => true
  | _ => false
  end%char.
Time
Fixpoint words_go (cur : option string) (s : string) : 
list string :=
  match s with
  | "" => option_list (string_rev <$> cur)
  | String a s =>
      if is_space a
      then option_list (string_rev <$> cur) ++ words_go None s
      else words_go (Some (from_option (String a) (String a "") cur)) s
  end.
Time Definition words : string \226\134\146 list string := words_go None.
Time
Ltac
 words s :=
  match type of s with
  | list string => s
  | string => eval vm_compute in (words s)
  end.
Time
Fixpoint digits_to_pos (\206\178s : list bool) : positive :=
  match \206\178s with
  | [] => xH
  | false :: \206\178s => (digits_to_pos \206\178s)~0
  | true :: \206\178s => (digits_to_pos \206\178s)~1
  end%positive.
Time
Definition ascii_to_digits (a : Ascii.ascii) : list bool :=
  match a with
  | Ascii.Ascii \206\1781 \206\1782 \206\1783 \206\1784 \206\1785 \206\1786 \206\1787 \206\1788 => [\206\1781; \206\1782; \206\1783; \206\1784; \206\1785; \206\1786; \206\1787; \206\1788]
  end.
Time
Fixpoint string_to_pos (s : string) : positive :=
  match s with
  | EmptyString => xH
  | String a s => string_to_pos s ++ digits_to_pos (ascii_to_digits a)
  end%positive.
Time
Fixpoint digits_of_pos (p : positive) : list bool :=
  match p with
  | xH => []
  | p~0 => false :: digits_of_pos p
  | p~1 => true :: digits_of_pos p
  end%positive.
Time
Fixpoint ascii_of_digits (\206\178s : list bool) : ascii :=
  match \206\178s with
  | [] => zero
  | \206\178 :: \206\178s => Ascii.shift \206\178 (ascii_of_digits \206\178s)
  end.
Time
Fixpoint string_of_digits (\206\178s : list bool) : string :=
  match \206\178s with
  | \206\1781 :: \206\1782 :: \206\1783 :: \206\1784 :: \206\1785 :: \206\1786 :: \206\1787 :: \206\1788 :: \206\178s =>
      String (ascii_of_digits [\206\1781; \206\1782; \206\1783; \206\1784; \206\1785; \206\1786; \206\1787; \206\1788])
        (string_of_digits \206\178s)
  | _ => EmptyString
  end.
Time
Definition string_of_pos (p : positive) : string :=
  string_of_digits (digits_of_pos p).
Time Lemma string_of_to_pos s : string_of_pos (string_to_pos s) = s.
Time Proof.
Time (unfold string_of_pos).
Time by induction s as [| [[] [] [] [] [] [] [] []]]; f_equal /=.
Time Qed.
Time #[program]
Instance string_countable : (Countable string) :=
 {| encode := string_to_pos; decode := fun p => Some (string_of_pos p) |}.
Time
Solve Obligations with naive_solver eauto using string_of_to_pos with f_equal.

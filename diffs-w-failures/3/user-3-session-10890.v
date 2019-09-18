Time From Coq Require Import Ascii.
Time From stdpp Require Export countable vector.
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
Time Set Default Proof Using "Type".
Time
Class Finite A `{EqDecision A} :={enum : list A;
                                  NoDup_enum : NoDup enum;
                                  elem_of_enum : forall x, x \226\136\136 enum}.
Time Hint Mode Finite ! -: typeclass_instances.
Time Defined.
Time Instance string_app_inj : (Inj (=) (=) (String.append s1)).
Time Proof.
Time (intros s1 ? ? ?).
Time (induction s1; simplify_eq /=; f_equal /=; auto).
Time Arguments enum : clear implicits.
Time Arguments enum _ {_} {_} : assert.
Time Arguments NoDup_enum : clear implicits.
Time Arguments NoDup_enum _ {_} {_} : assert.
Time Definition card A `{Finite A} := length (enum A).
Time #[program]
Definition finite_countable `{Finite A} : Countable A :=
  {|
  encode := \206\187 x,
              Pos.of_nat $ S $ default 0 $ fst <$> list_find (x =) (enum A);
  decode := \206\187 p, enum A !! pred (Pos.to_nat p) |}.
Time Arguments Pos.of_nat : simpl never.
Time Next Obligation.
Time (intros ? ? [xs Hxs HA] x; unfold encode, decode; simpl).
Time Qed.
Time (destruct (list_find_elem_of (x =) xs x) as [[i y] Hi]; auto).
Time (rewrite Nat2Pos.id by done; simpl; rewrite Hi; simpl).
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
Time (destruct (list_find_Some (x =) xs i y); naive_solver).
Time
Definition is_space (x : Ascii.ascii) : bool :=
  match x with
  | "009" | "010" | "011" | "012" | "013" | " " => true
  | _ => false
  end%char.
Time Qed.
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
Time Hint Immediate finite_countable: typeclass_instances.
Time
Definition find `{Finite A} P `{\226\136\128 x, Decision (P x)} : 
  option A := list_find P (enum A) \226\137\171= decode_nat \226\136\152 fst.
Time Lemma encode_lt_card `{finA : Finite A} (x : A) : encode_nat x < card A.
Time Proof.
Time (destruct finA as [xs Hxs HA]; unfold encode_nat, encode, card; simpl).
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
Time (rewrite Nat2Pos.id by done; simpl).
Time (destruct (list_find _ xs) as [[i y]| ] eqn:?; simpl).
Time Lemma string_of_to_pos s : string_of_pos (string_to_pos s) = s.
Time Proof.
Time (unfold string_of_pos).
Time by induction s as [| [[] [] [] [] [] [] [] []]]; f_equal /=.
Time -
Time (destruct (list_find_Some (x =) xs i y); eauto using lookup_lt_Some).
Time -
Time (destruct xs; simpl).
Time (exfalso; eapply not_elem_of_nil, (HA x)).
Time lia.
Time Qed.
Time
Lemma encode_decode A `{finA : Finite A} i :
  i < card A \226\134\146 \226\136\131 x : A, decode_nat i = Some x \226\136\167 encode_nat x = i.
Time Proof.
Time (destruct finA as [xs Hxs HA]).
Time (unfold encode_nat, decode_nat, encode, decode, card; simpl).
Time (intros Hi).
Time (apply lookup_lt_is_Some in Hi).
Time (destruct Hi as [x Hx]).
Time exists x.
Time (rewrite !Nat2Pos.id by done; simpl).
Time (destruct (list_find_elem_of (x =) xs x) as [[j y] Hj]; auto).
Time (destruct (list_find_Some (x =) xs j y) as [? ->]; auto).
Time (rewrite Hj; csimpl; eauto using NoDup_lookup).
Time Qed.
Time
Lemma find_Some `{finA : Finite A} P `{\226\136\128 x, Decision (P x)} 
  (x : A) : find P = Some x \226\134\146 P x.
Time Proof.
Time (destruct finA as [xs Hxs HA]; unfold find, decode_nat, decode; simpl).
Time (intros Hx).
Time (destruct (list_find _ _) as [[i y]| ] eqn:Hi; simplify_eq /=).
Time (rewrite !Nat2Pos.id in Hx by done).
Time (destruct (list_find_Some P xs i y); naive_solver).
Time Qed.
Time
Lemma find_is_Some `{finA : Finite A} P `{\226\136\128 x, Decision (P x)} 
  (x : A) : P x \226\134\146 \226\136\131 y, find P = Some y \226\136\167 P y.
Time Proof.
Time (destruct finA as [xs Hxs HA]; unfold find, decode; simpl).
Time (intros Hx).
Time (destruct (list_find_elem_of P xs x) as [[i y] Hi]; auto).
Time (rewrite Hi).
Time (destruct (list_find_Some P xs i y); simplify_eq /=; auto).
Time exists y.
Time by rewrite !Nat2Pos.id by done.
Time Qed.
Time
Definition encode_fin `{Finite A} (x : A) : fin (card A) :=
  Fin.of_nat_lt (encode_lt_card x).
Time #[program]
Definition decode_fin `{Finite A} (i : fin (card A)) : A :=
  match Some_dec (decode_nat i) with
  | inleft (x \226\134\190 _) => x
  | inright _ => _
  end.
Time Next Obligation.
Time (intros A ? ? i ?; exfalso).
Time (destruct (encode_decode A i); naive_solver auto using fin_to_nat_lt).
Time Qed.
Time
Lemma decode_encode_fin `{Finite A} (x : A) : decode_fin (encode_fin x) = x.
Time Proof.
Time (unfold decode_fin, encode_fin).
Time (destruct (Some_dec _) as [[x' Hx]| Hx]).
Time {
Time by rewrite fin_to_of_nat, decode_encode_nat in Hx; simplify_eq.
Time }
Time (exfalso; by rewrite fin_to_of_nat, decode_encode_nat in Hx).
Time Qed.
Time
Lemma fin_choice {n} {B : fin n \226\134\146 Type} (P : \226\136\128 i, B i \226\134\146 Prop) :
  (\226\136\128 i, \226\136\131 y, P i y) \226\134\146 \226\136\131 f, \226\136\128 i, P i (f i).
Time Proof.
Time (induction n as [| n IH]; intros Hex).
Time {
Time (exists (fin_0_inv _); intros i; inv_fin i).
Time }
Time (destruct (IH _ _ (\206\187 i, Hex (FS i))) as [f Hf], (Hex 0%fin) as [y Hy]).
Time (exists (fin_S_inv _ y f); intros i; by inv_fin i).
Time Qed.
Time
Lemma finite_choice `{Finite A} {B : A \226\134\146 Type} (P : \226\136\128 x, B x \226\134\146 Prop) :
  (\226\136\128 x, \226\136\131 y, P x y) \226\134\146 \226\136\131 f, \226\136\128 x, P x (f x).
Time Proof.
Time (intros Hex).
Time (destruct (fin_choice _ (\206\187 i, Hex (decode_fin i))) as [f ?]).
Time
(exists (\206\187 x, eq_rect _ _ (f (encode_fin x)) _ (decode_encode_fin x));
  intros x).
Time (destruct (decode_encode_fin x); simpl; auto).
Time Qed.
Time Lemma card_0_inv P `{finA : Finite A} : card A = 0 \226\134\146 A \226\134\146 P.
Time Proof.
Time (intros ? x).
Time (destruct finA as [[| ? ?] ? ?]; simplify_eq).
Time by destruct (not_elem_of_nil x).
Time Qed.
Time Lemma finite_inhabited A `{finA : Finite A} : 0 < card A \226\134\146 Inhabited A.
Time Proof.
Time (unfold card; intros).
Time (destruct finA as [[| x ?] ? ?]; simpl in *; [ exfalso; lia |  ]).
Time (constructor; exact x).
Time Qed.
Time
Lemma finite_inj_submseteq `{finA : Finite A} `{finB : Finite B} 
  (f : A \226\134\146 B) `{!Inj (=) (=) f} : f <$> enum A \226\138\134+ enum B.
Time Proof.
Time (intros).
Time (destruct finA, finB).
Time (apply NoDup_submseteq; auto using NoDup_fmap_2).
Time Qed.
Time
Lemma finite_inj_Permutation `{Finite A} `{Finite B} 
  (f : A \226\134\146 B) `{!Inj (=) (=) f} : card A = card B \226\134\146 f <$> enum A \226\137\161\226\130\154 enum B.
Time Proof.
Time (intros).
Time (apply submseteq_Permutation_length_eq).
Time -
Time by rewrite fmap_length.
Time -
Time by apply finite_inj_submseteq.
Time Qed.
Time
Lemma finite_inj_surj `{Finite A} `{Finite B} (f : A \226\134\146 B) 
  `{!Inj (=) (=) f} : card A = card B \226\134\146 Surj (=) f.
Time Proof.
Time (intros HAB y).
Time (destruct (elem_of_list_fmap_2 f (enum A) y) as (x, (?, ?)); eauto).
Time (rewrite finite_inj_Permutation; auto using elem_of_enum).
Time Qed.
Time
Lemma finite_surj A `{Finite A} B `{Finite B} :
  0 < card A \226\137\164 card B \226\134\146 \226\136\131 g : B \226\134\146 A, Surj (=) g.
Time Proof.
Time (intros [? ?]).
Time (destruct (finite_inhabited A) as [x']; auto with lia).
Time exists (\206\187 y : B, default x' (decode_nat (encode_nat y))).
Time (intros x).
Time (destruct (encode_decode B (encode_nat x)) as (y, (Hy1, Hy2))).
Time {
Time (pose proof (encode_lt_card x); lia).
Time }
Time exists y.
Time by rewrite Hy2, decode_encode_nat.
Time Qed.
Time
Lemma finite_inj A `{Finite A} B `{Finite B} :
  card A \226\137\164 card B \226\134\148 (\226\136\131 f : A \226\134\146 B, Inj (=) (=) f).
Time Proof.
Time split.
Time -
Time (intros).
Time (destruct (decide (card A = 0)) as [HA| ?]).
Time {
Time exists (card_0_inv B HA).
Time (intros y).
Time (apply (card_0_inv _ HA y)).
Time }
Time (destruct (finite_surj A B) as (g, ?); auto with lia).
Time (destruct (surj_cancel g) as (f, ?)).
Time exists f.
Time (apply cancel_inj).
Time -
Time (intros [f ?]).
Time (unfold card).
Time (rewrite <- (fmap_length f)).
Time by apply submseteq_length, (finite_inj_submseteq f).
Time Qed.
Time
Lemma finite_bijective A `{Finite A} B `{Finite B} :
  card A = card B \226\134\148 (\226\136\131 f : A \226\134\146 B, Inj (=) (=) f \226\136\167 Surj (=) f).
Time Proof.
Time split.
Time -
Time (intros; destruct (proj1 (finite_inj A B)) as [f ?]; auto with lia).
Time (exists f; auto using (finite_inj_surj f)).
Time -
Time (intros (f, (?, ?))).
Time (apply (anti_symm (\226\137\164)); apply finite_inj).
Time +
Time by exists f.
Time +
Time (destruct (surj_cancel f) as (g, ?); eauto using cancel_inj).
Time Qed.
Time
Lemma inj_card `{Finite A} `{Finite B} (f : A \226\134\146 B) 
  `{!Inj (=) (=) f} : card A \226\137\164 card B.
Time Proof.
Time (apply finite_inj).
Time eauto.
Time Qed.
Time
Lemma surj_card `{Finite A} `{Finite B} (f : A \226\134\146 B) 
  `{!Surj (=) f} : card B \226\137\164 card A.
Time Proof.
Time (destruct (surj_cancel f) as (g, ?)).
Time (apply inj_card with g, cancel_inj).
Time Qed.
Time
Lemma bijective_card `{Finite A} `{Finite B} (f : A \226\134\146 B) 
  `{!Inj (=) (=) f} `{!Surj (=) f} : card A = card B.
Time Proof.
Time (apply finite_bijective).
Time eauto.
Time Qed.
Time Section forall_exists.
Time Context `{Finite A} (P : A \226\134\146 Prop).
Time Lemma Forall_finite : Forall P (enum A) \226\134\148 (\226\136\128 x, P x).
Time Proof.
Time (rewrite Forall_forall).
Time intuition auto using elem_of_enum.
Time Qed.
Time Lemma Exists_finite : Exists P (enum A) \226\134\148 (\226\136\131 x, P x).
Time Proof.
Time (rewrite Exists_exists).
Time naive_solver eauto using elem_of_enum.
Time Qed.
Time Context `{\226\136\128 x, Decision (P x)}.
Time #[global]Instance forall_dec : (Decision (\226\136\128 x, P x)).
Time Proof  using ((Type))*.
Time
(refine (cast_if (decide (Forall P (enum A)))); abstract by
  rewrite <- Forall_finite).
Time Defined.
Time #[global]Instance exists_dec : (Decision (\226\136\131 x, P x)).
Time Proof  using ((Type))*.
Time
(refine (cast_if (decide (Exists P (enum A)))); abstract by
  rewrite <- Exists_finite).
Time Defined.
Time End forall_exists.
Time Section enc_finite.
Time Context `{EqDecision A}.
Time Context (to_nat : A \226\134\146 nat) (of_nat : nat \226\134\146 A) (c : nat).
Time Context (of_to_nat : \226\136\128 x, of_nat (to_nat x) = x).
Time Context (to_nat_c : \226\136\128 x, to_nat x < c).
Time Context (to_of_nat : \226\136\128 i, i < c \226\134\146 to_nat (of_nat i) = i).
Time #[program]
Instance enc_finite : (Finite A) := {| enum := of_nat <$> seq 0 c |}.
Time Next Obligation.
Time (apply NoDup_alt).
Time (intros i j x).
Time (rewrite !list_lookup_fmap).
Time (intros Hi Hj).
Time
(destruct (seq _ _ !! i) as [i'| ] eqn:Hi', (seq _ _ !! j) as [j'| ] eqn:Hj';
  simplify_eq /=).
Time
(destruct (lookup_seq_inv _ _ _ _ Hi'), (lookup_seq_inv _ _ _ _ Hj'); subst).
Time (rewrite <- (to_of_nat i), <- (to_of_nat j) by done).
Time by f_equal.
Time Qed.
Time Next Obligation.
Time (intros x).
Time (rewrite elem_of_list_fmap).
Time exists (to_nat x).
Time (split; auto).
Time by apply elem_of_list_lookup_2 with (to_nat x), lookup_seq.
Time Qed.
Time Lemma enc_finite_card : card A = c.
Time Proof.
Time (unfold card).
Time (simpl).
Time by rewrite fmap_length, seq_length.
Time Qed.
Time End enc_finite.
Time Section bijective_finite.
Time Context `{Finite A} `{EqDecision B} (f : A \226\134\146 B) (g : B \226\134\146 A).
Time Context `{!Inj (=) (=) f} `{!Cancel (=) f g}.
Time #[program]
Instance bijective_finite : (Finite B) := {| enum := f <$> enum A |}.
Time Next Obligation.
Time (apply (NoDup_fmap_2 _), NoDup_enum).
Time Qed.
Time Next Obligation.
Time (intros y).
Time (rewrite elem_of_list_fmap).
Time eauto using elem_of_enum.
Time Qed.
Time End bijective_finite.
Time #[program]
Instance option_finite  `{Finite A}: (Finite (option A)) :=
 {| enum := None :: (Some <$> enum A) |}.
Time Next Obligation.
Time constructor.
Time -
Time (rewrite elem_of_list_fmap).
Time by intros (?, (?, ?)).
Time -
Time (apply (NoDup_fmap_2 _); auto using NoDup_enum).
Time Qed.
Time Next Obligation.
Time (intros ? ? ? [x| ]; [ right | left ]; auto).
Time (apply elem_of_list_fmap).
Time eauto using elem_of_enum.
Time Qed.
Time Lemma option_cardinality `{Finite A} : card (option A) = S (card A).
Time Proof.
Time (unfold card).
Time (simpl).
Time by rewrite fmap_length.
Time Qed.
Time #[program]
Instance Empty_set_finite : (Finite Empty_set) := {| enum := [] |}.
Time Next Obligation.
Time by apply NoDup_nil.
Time Qed.
Time Next Obligation.
Time (intros []).
Time Qed.
Time Lemma Empty_set_card : card Empty_set = 0.
Time Proof.
Time done.
Time Qed.
Time #[program]Instance unit_finite : (Finite ()) := {| enum := [tt] |}.
Time Next Obligation.
Time (apply NoDup_singleton).
Time Qed.
Time Next Obligation.
Time (intros []).
Time by apply elem_of_list_singleton.
Time Qed.
Time Lemma unit_card : card unit = 1.
Time Proof.
Time done.
Time Qed.
Time #[program]
Instance bool_finite : (Finite bool) := {| enum := [true; false] |}.
Time Next Obligation.
Time constructor.
Time by rewrite elem_of_list_singleton.
Time (apply NoDup_singleton).
Time Qed.
Time Next Obligation.
Time (intros [| ]).
Time left.
Time (right; left).
Time Qed.
Time Lemma bool_card : card bool = 2.
Time Proof.
Time done.
Time Qed.
Time #[program]
Instance sum_finite  `{Finite A} `{Finite B}: (Finite (A + B)%type) :=
 {| enum := (inl <$> enum A) ++ (inr <$> enum B) |}.
Time Next Obligation.
Time (intros).
Time (apply NoDup_app; split_and ?).
Time -
Time (apply (NoDup_fmap_2 _)).
Time by apply NoDup_enum.
Time -
Time intro.
Time (rewrite !elem_of_list_fmap).
Time (intros (?, (?, ?)) (?, (?, ?)); congruence).
Time -
Time (apply (NoDup_fmap_2 _)).
Time by apply NoDup_enum.
Time Qed.
Time Next Obligation.
Time
(intros ? ? ? ? ? ? [x| y]; rewrite elem_of_app, !elem_of_list_fmap; eauto
  using @elem_of_enum).
Time Qed.
Time Lemma sum_card `{Finite A} `{Finite B} : card (A + B) = card A + card B.
Time Proof.
Time (unfold card).
Time (simpl).
Time by rewrite app_length, !fmap_length.
Time Qed.
Time #[program]
Instance prod_finite  `{Finite A} `{Finite B}: (Finite (A * B)%type) :=
 {| enum := foldr (\206\187 x, (pair x <$> enum B ++)) [] (enum A) |}.
Time Next Obligation.
Time (intros ? ? ? ? ? ?).
Time (induction (NoDup_enum A) as [| x xs Hx Hxs IH]; simpl).
Time {
Time constructor.
Time }
Time (apply NoDup_app; split_and ?).
Time -
Time by apply (NoDup_fmap_2 _), NoDup_enum.
Time -
Time (intros [? y]).
Time (rewrite elem_of_list_fmap).
Time (intros (?, (?, ?)); simplify_eq).
Time clear IH.
Time (induction Hxs as [| x' xs ? ? IH]; simpl).
Time {
Time (rewrite elem_of_nil).
Time tauto.
Time }
Time (rewrite elem_of_app, elem_of_list_fmap).
Time (intros [(?, (?, ?))| ?]; simplify_eq).
Time +
Time (destruct Hx).
Time by left.
Time +
Time (destruct IH).
Time by intro; destruct Hx; right.
Time auto.
Time -
Time done.
Time Qed.
Time Next Obligation.
Time (intros ? ? ? ? ? ? [x y]).
Time (induction (elem_of_enum x); simpl).
Time -
Time (rewrite elem_of_app, !elem_of_list_fmap).
Time eauto using @elem_of_enum.
Time -
Time (rewrite elem_of_app; eauto).
Time Qed.
Time
Lemma prod_card `{Finite A} `{Finite B} : card (A * B) = card A * card B.
Time Proof.
Time (unfold card; simpl).
Time (induction (enum A); simpl; auto).
Time (rewrite app_length, fmap_length).
Time auto.
Time Qed.
Time
Definition list_enum {A} (l : list A) :
  \226\136\128 n, list {l : list A | length l = n} :=
  fix go n :=
    match n with
    | 0 => [[] \226\134\190 eq_refl]
    | S n =>
        foldr (\206\187 x, (sig_map (x::) (\206\187 _ H, f_equal S H) <$> go n ++)) [] l
    end.
Time #[program]
Instance list_finite  `{Finite A} n: (Finite {l : list A | length l = n}) :=
 {| enum := list_enum (enum A) n |}.
Time Next Obligation.
Time (intros ? ? ? ?).
Time (induction n as [| n IH]; simpl; [ apply NoDup_singleton |  ]).
Time revert IH.
Time (generalize (list_enum (enum A) n)).
Time (intros l Hl).
Time
(induction (NoDup_enum A) as [| x xs Hx Hxs IH]; simpl; auto;
  [ constructor |  ]).
Time (apply NoDup_app; split_and ?).
Time -
Time by apply (NoDup_fmap_2 _).
Time -
Time (intros [k1 Hk1]).
Time clear Hxs IH.
Time (rewrite elem_of_list_fmap).
Time (intros ([k2 Hk2], (?, ?)) Hxk2; simplify_eq /=).
Time (destruct Hx).
Time revert Hxk2.
Time
(induction xs as [| x' xs IH]; simpl in *; [ by rewrite elem_of_nil |  ]).
Time (rewrite elem_of_app, elem_of_list_fmap, elem_of_cons).
Time Qed.
Time (intros [([? ?], (?, ?))| ?]; simplify_eq /=; auto).
Time -
Time (apply IH).
Time Qed.
Time #[program]
Instance string_countable : (Countable string) :=
 {| encode := string_to_pos; decode := fun p => Some (string_of_pos p) |}.
Time Next Obligation.
Time (intros ? ? ? ? [l Hl]).
Time revert l Hl.
Time (induction n as [| n IH]; intros [| x l] ?; simpl; simplify_eq).
Time
Solve Obligations with naive_solver eauto using string_of_to_pos with f_equal.
Time {
Time (apply elem_of_list_singleton).
Time by apply (sig_eq_pi _).
Time }
Time revert IH.
Time (generalize (list_enum (enum A) n)).
Time (intros k Hk).
Time (induction (elem_of_enum x) as [x xs| x xs]; simpl in *).
Time -
Time (rewrite elem_of_app, elem_of_list_fmap).
Time left.
Time injection Hl.
Time (intros Hl').
Time eexists (l \226\134\190 Hl').
Time split.
Time by apply (sig_eq_pi _).
Time done.
Time -
Time (rewrite elem_of_app).
Time eauto.
Time Qed.
Time
Lemma list_card `{Finite A} n : card {l : list A | length l = n} = card A ^ n.
Time Proof.
Time (unfold card; simpl).
Time (induction n as [| n IH]; simpl; auto).
Time (rewrite <- IH).
Time clear IH.
Time (generalize (list_enum (enum A) n)).
Time (induction (enum A) as [| x xs IH]; intros l; simpl; auto).
Time by rewrite app_length, fmap_length, IH.
Time Qed.
Time
Fixpoint fin_enum (n : nat) : list (fin n) :=
  match n with
  | 0 => []
  | S n => 0%fin :: (FS <$> fin_enum n)
  end.
Time #[program]
Instance fin_finite  n: (Finite (fin n)) := {| enum := fin_enum n |}.
Time Next Obligation.
Time (intros n).
Time (induction n; simpl; constructor).
Time -
Time (rewrite elem_of_list_fmap).
Time by intros (?, (?, ?)).
Time -
Time by apply (NoDup_fmap _).
Time Qed.
Time Next Obligation.
Time (intros n i).
Time
(induction i as [| n i IH]; simpl; rewrite elem_of_cons, ?elem_of_list_fmap;
  eauto).
Time Qed.
Time Lemma fin_card n : card (fin n) = n.
Time Proof.
Time (unfold card; simpl).
Time (induction n; simpl; rewrite ?fmap_length; auto).
Time Qed.

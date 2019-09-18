Time From Coq Require Export Permutation.
Time From stdpp Require Export numbers base option.
Time Set Default Proof Using "Type*".
Time Arguments length {_} _ : assert.
Time Arguments cons {_} _ _ : assert.
Time Arguments app {_} _ _ : assert.
Time Instance: (Params (@length) 1) := { }.
Time Instance: (Params (@cons) 1) := { }.
Time Instance: (Params (@app) 1) := { }.
Time Notation tail := tl.
Time Notation take := firstn.
Time Notation drop := skipn.
Time Arguments head {_} _ : assert.
Time Arguments tail {_} _ : assert.
Time Arguments take {_} !_ !_ / : assert.
Time Arguments drop {_} !_ !_ / : assert.
Time Instance: (Params (@head) 1) := { }.
Time Instance: (Params (@tail) 1) := { }.
Time Instance: (Params (@take) 1) := { }.
Time Instance: (Params (@drop) 1) := { }.
Time Arguments Permutation {_} _ _ : assert.
Time Arguments Forall_cons {_} _ _ _ _ _ : assert.
Time Remove Hints Permutation_cons: typeclass_instances.
Time Notation "(::)" := cons (only parsing) : list_scope.
Time Notation "( x ::)" := (cons x) (only parsing) : list_scope.
Time Notation "(:: l )" := (\206\187 x, cons x l) (only parsing) : list_scope.
Time Notation "(++)" := app (only parsing) : list_scope.
Time Notation "( l ++)" := (app l) (only parsing) : list_scope.
Time Notation "(++ k )" := (\206\187 l, app l k) (only parsing) : list_scope.
Time Infix "\226\137\161\226\130\154" := Permutation (at level 70, no associativity) : stdpp_scope.
Time Notation "(\226\137\161\226\130\154)" := Permutation (only parsing) : stdpp_scope.
Time Notation "( x \226\137\161\226\130\154)" := (Permutation x) (only parsing) : stdpp_scope.
Time Notation "(\226\137\161\226\130\154 x )" := (\206\187 y, y \226\137\161\226\130\154 x) (only parsing) : stdpp_scope.
Time Notation "(\226\137\162\226\130\154)" := (\206\187 x y, \194\172 x \226\137\161\226\130\154 y) (only parsing) : stdpp_scope.
Time
Notation "x \226\137\162\226\130\154 y" := (\194\172 x \226\137\161\226\130\154 y) (at level 70, no associativity) : stdpp_scope.
Time Notation "( x \226\137\162\226\130\154)" := (\206\187 y, x \226\137\162\226\130\154 y) (only parsing) : stdpp_scope.
Time Notation "(\226\137\162\226\130\154 x )" := (\206\187 y, y \226\137\162\226\130\154 x) (only parsing) : stdpp_scope.
Time
Infix "\226\137\161\226\130\154@{ A }" := (@Permutation A)
(at level 70, no associativity, only parsing) : stdpp_scope.
Time Notation "(\226\137\161\226\130\154@{ A } )" := (@Permutation A) (only parsing) : stdpp_scope.
Time
Instance maybe_cons  {A}: (Maybe2 (@cons A)) :=
 (\206\187 l, match l with
       | x :: l => Some (x, l)
       | _ => None
       end).
Time
Inductive list_equiv `{Equiv A} : Equiv (list A) :=
  | nil_equiv : [] \226\137\161 []
  | cons_equiv : forall x y l k, x \226\137\161 y \226\134\146 l \226\137\161 k \226\134\146 x :: l \226\137\161 y :: k.
Time Existing Instance list_equiv.
Time
Instance list_lookup  {A}: (Lookup nat A (list A)) :=
 (fix go i l {struct l} : option A :=
    let _ : Lookup _ _ _ := @go in
    match l with
    | [] => None
    | x :: l => match i with
                | 0 => Some x
                | S i => l !! i
                end
    end).
Time
Instance list_alter  {A}: (Alter nat A (list A)) :=
 (\206\187 f,
    fix go i l {struct l} :=
      match l with
      | [] => []
      | x :: l => match i with
                  | 0 => f x :: l
                  | S i => x :: go i l
                  end
      end).
Time
Instance list_insert  {A}: (Insert nat A (list A)) :=
 (fix go i y l {struct l} :=
    let _ : Insert _ _ _ := @go in
    match l with
    | [] => []
    | x :: l => match i with
                | 0 => y :: l
                | S i => x :: <[i:=y]> l
                end
    end).
Time
Fixpoint list_inserts {A} (i : nat) (k l : list A) : 
list A :=
  match k with
  | [] => l
  | y :: k => <[i:=y]> (list_inserts (S i) k l)
  end.
Time Instance: (Params (@list_inserts) 1) := { }.
Time
Instance list_delete  {A}: (Delete nat (list A)) :=
 (fix go (i : nat) (l : list A) {struct l} : list A :=
    match l with
    | [] => []
    | x :: l => match i with
                | 0 => l
                | S i => x :: @delete _ _ go i l
                end
    end).
Time
Definition option_list {A} : option A \226\134\146 list A := option_rect _ (\206\187 x, [x]) [].
Time Instance: (Params (@option_list) 1) := { }.
Time
Instance maybe_list_singleton  {A}: (Maybe (\206\187 x : A, [x])) :=
 (\206\187 l, match l with
       | [x] => Some x
       | _ => None
       end).
Time
Instance list_filter  {A}: (Filter A (list A)) :=
 (fix go P _ l :=
    let _ : Filter _ _ := @go in
    match l with
    | [] => []
    | x :: l => if decide (P x) then x :: filter P l else filter P l
    end).
Time
Definition list_find {A} P `{\226\136\128 x, Decision (P x)} :
  list A \226\134\146 option (nat * A) :=
  fix go l :=
    match l with
    | [] => None
    | x :: l => if decide (P x) then Some (0, x) else prod_map S id <$> go l
    end.
Time Instance: (Params (@list_find) 3) := { }.
Time
Fixpoint replicate {A} (n : nat) (x : A) : list A :=
  match n with
  | 0 => []
  | S n => x :: replicate n x
  end.
Time Instance: (Params (@replicate) 2) := { }.
Time Definition reverse {A} (l : list A) : list A := rev_append l [].
Time Instance: (Params (@reverse) 1) := { }.
Time
Fixpoint last {A} (l : list A) : option A :=
  match l with
  | [] => None
  | [x] => Some x
  | _ :: l => last l
  end.
Time Instance: (Params (@last) 1) := { }.
Time
Fixpoint resize {A} (n : nat) (y : A) (l : list A) : 
list A :=
  match l with
  | [] => replicate n y
  | x :: l => match n with
              | 0 => []
              | S n => x :: resize n y l
              end
  end.
Time Arguments resize {_} !_ _ !_ : assert.
Time Instance: (Params (@resize) 2) := { }.
Time
Fixpoint reshape {A} (szs : list nat) (l : list A) : 
list (list A) :=
  match szs with
  | [] => []
  | sz :: szs => take sz l :: reshape szs (drop sz l)
  end.
Time Instance: (Params (@reshape) 2) := { }.
Time
Definition sublist_lookup {A} (i n : nat) (l : list A) : 
  option (list A) := guard i + n \226\137\164 length l; Some (take n (drop i l)).
Time
Definition sublist_alter {A} (f : list A \226\134\146 list A) 
  (i n : nat) (l : list A) : list A :=
  take i l ++ f (take n (drop i l)) ++ drop (i + n) l.
Time Notation foldr := fold_right.
Time
Definition foldl {A} {B} (f : A \226\134\146 B \226\134\146 A) : A \226\134\146 list B \226\134\146 A :=
  fix go a l := match l with
                | [] => a
                | x :: l => go (f a x) l
                end.
Time Instance list_ret : (MRet list) := (\206\187 A x, x :: @nil A).
Time
Instance list_fmap : (FMap list) :=
 (\206\187 A B f,
    fix go (l : list A) :=
      match l with
      | [] => []
      | x :: l => f x :: go l
      end).
Time
Instance list_omap : (OMap list) :=
 (\206\187 A B f,
    fix go (l : list A) :=
      match l with
      | [] => []
      | x :: l => match f x with
                  | Some y => y :: go l
                  | None => go l
                  end
      end).
Time
Instance list_bind : (MBind list) :=
 (\206\187 A B f,
    fix go (l : list A) :=
      match l with
      | [] => []
      | x :: l => f x ++ go l
      end).
Time
Instance list_join : (MJoin list) :=
 (fix go A (ls : list (list A)) : list A :=
    match ls with
    | [] => []
    | l :: ls => l ++ @mjoin _ go _ ls
    end).
Time
Definition mapM `{MBind M} `{MRet M} {A} {B} (f : A \226\134\146 M B) :
  list A \226\134\146 M (list B) :=
  fix go l :=
    match l with
    | [] => mret []
    | x :: l => y \226\134\144 f x; k \226\134\144 go l; mret (y :: k)
    end.
Time
Fixpoint imap {A B} (f : nat \226\134\146 A \226\134\146 B) (l : list A) : 
list B := match l with
          | [] => []
          | x :: l => f 0 x :: imap (f \226\136\152 S) l
          end.
Time
Definition zipped_map {A} {B} (f : list A \226\134\146 list A \226\134\146 A \226\134\146 B) :
  list A \226\134\146 list A \226\134\146 list B :=
  fix go l k :=
    match k with
    | [] => []
    | x :: k => f l k x :: go (x :: l) k
    end.
Time
Fixpoint imap2 {A B C} (f : nat \226\134\146 A \226\134\146 B \226\134\146 C) (l : list A) 
(k : list B) : list C :=
  match l, k with
  | [], _ | _, [] => []
  | x :: l, y :: k => f 0 x y :: imap2 (f \226\136\152 S) l k
  end.
Time
Inductive zipped_Forall {A} (P : list A \226\134\146 list A \226\134\146 A \226\134\146 Prop) :
list A \226\134\146 list A \226\134\146 Prop :=
  | zipped_Forall_nil : forall l, zipped_Forall P l []
  | zipped_Forall_cons :
      forall l k x,
      P l k x \226\134\146 zipped_Forall P (x :: l) k \226\134\146 zipped_Forall P l (x :: k).
Time Arguments zipped_Forall_nil {_} {_} _ : assert.
Time Arguments zipped_Forall_cons {_} {_} _ _ _ _ _ : assert.
Time
Fixpoint mask {A} (f : A \226\134\146 A) (\206\178s : list bool) (l : list A) : 
list A :=
  match \206\178s, l with
  | \206\178 :: \206\178s, x :: l => (if \206\178 then f x else x) :: mask f \206\178s l
  | _, _ => l
  end.
Time
Fixpoint interleave {A} (x : A) (l : list A) : list (list A) :=
  match l with
  | [] => [[x]]
  | y :: l => (x :: y :: l) :: ((y::) <$> interleave x l)
  end.
Time
Fixpoint permutations {A} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: l => permutations l \226\137\171= interleave x
  end.
Time Definition suffix {A} : relation (list A) := \206\187 l1 l2, \226\136\131 k, l2 = k ++ l1.
Time Definition prefix {A} : relation (list A) := \206\187 l1 l2, \226\136\131 k, l2 = l1 ++ k.
Time Infix "`suffix_of`" := suffix (at level 70) : stdpp_scope.
Time Infix "`prefix_of`" := prefix (at level 70) : stdpp_scope.
Time Hint Extern 0 (_ `prefix_of` _) => reflexivity: core.
Time Hint Extern 0 (_ `suffix_of` _) => reflexivity: core.
Time Section prefix_suffix_ops.
Time Context `{EqDecision A}.
Time
Definition max_prefix : list A \226\134\146 list A \226\134\146 list A * list A * list A :=
  fix go l1 l2 :=
    match l1, l2 with
    | [], l2 => ([], l2, [])
    | l1, [] => (l1, [], [])
    | x1 :: l1, x2 :: l2 =>
        if decide_rel (=) x1 x2
        then prod_map id (x1::) (go l1 l2)
        else (x1 :: l1, x2 :: l2, [])
    end.
Time
Definition max_suffix (l1 l2 : list A) : list A * list A * list A :=
  match max_prefix (reverse l1) (reverse l2) with
  | (k1, k2, k3) => (reverse k1, reverse k2, reverse k3)
  end.
Time Definition strip_prefix (l1 l2 : list A) := (max_prefix l1 l2).1.2.
Time Definition strip_suffix (l1 l2 : list A) := (max_suffix l1 l2).1.2.
Time End prefix_suffix_ops.
Time
Inductive sublist {A} : relation (list A) :=
  | sublist_nil : sublist [] []
  | sublist_skip :
      forall x l1 l2, sublist l1 l2 \226\134\146 sublist (x :: l1) (x :: l2)
  | sublist_cons : forall x l1 l2, sublist l1 l2 \226\134\146 sublist l1 (x :: l2).
Time Infix "`sublist_of`" := sublist (at level 70) : stdpp_scope.
Time Hint Extern 0 (_ `sublist_of` _) => reflexivity: core.
Time
Inductive submseteq {A} : relation (list A) :=
  | submseteq_nil : submseteq [] []
  | submseteq_skip :
      forall x l1 l2, submseteq l1 l2 \226\134\146 submseteq (x :: l1) (x :: l2)
  | submseteq_swap : forall x y l, submseteq (y :: x :: l) (x :: y :: l)
  | submseteq_cons : forall x l1 l2, submseteq l1 l2 \226\134\146 submseteq l1 (x :: l2)
  | submseteq_trans :
      forall l1 l2 l3, submseteq l1 l2 \226\134\146 submseteq l2 l3 \226\134\146 submseteq l1 l3.
Time Infix "\226\138\134+" := submseteq (at level 70) : stdpp_scope.
Time Hint Extern 0 (_ \226\138\134+ _) => reflexivity: core.
Time
Fixpoint list_remove `{EqDecision A} (x : A) (l : list A) : 
option (list A) :=
  match l with
  | [] => None
  | y :: l => if decide (x = y) then Some l else (y::) <$> list_remove x l
  end.
Time
Fixpoint list_remove_list `{EqDecision A} (k : list A) 
(l : list A) : option (list A) :=
  match k with
  | [] => Some l
  | x :: k => list_remove x l \226\137\171= list_remove_list k
  end.
Time
Inductive Forall3 {A} {B} {C} (P : A \226\134\146 B \226\134\146 C \226\134\146 Prop) :
list A \226\134\146 list B \226\134\146 list C \226\134\146 Prop :=
  | Forall3_nil : Forall3 P [] [] []
  | Forall3_cons :
      forall x y z l k k',
      P x y z \226\134\146 Forall3 P l k k' \226\134\146 Forall3 P (x :: l) (y :: k) (z :: k').
Time
Instance list_subseteq  {A}: (SubsetEq (list A)) :=
 (\206\187 l1 l2, \226\136\128 x, x \226\136\136 l1 \226\134\146 x \226\136\136 l2).
Time Section list_set.
Time Context `{dec : EqDecision A}.
Time #[global]Instance elem_of_list_dec : (RelDecision (\226\136\136@{list A} )).
Time Proof.
Time
(refine
  (fix go x l :=
     match l return (Decision (x \226\136\136 l)) with
     | [] => right _
     | y :: l => cast_if_or (decide (x = y)) (go x l)
     end); clear go dec; subst; try by constructor; abstract by 
  inversion 1).
Time Defined.
Time
Fixpoint remove_dups (l : list A) : list A :=
  match l with
  | [] => []
  | x :: l =>
      if decide_rel (\226\136\136) x l then remove_dups l else x :: remove_dups l
  end.
Time
Fixpoint list_difference (l k : list A) : list A :=
  match l with
  | [] => []
  | x :: l =>
      if decide_rel (\226\136\136) x k
      then list_difference l k
      else x :: list_difference l k
  end.
Time
Definition list_union (l k : list A) : list A := list_difference l k ++ k.
Time
Fixpoint list_intersection (l k : list A) : list A :=
  match l with
  | [] => []
  | x :: l =>
      if decide_rel (\226\136\136) x k
      then x :: list_intersection l k
      else list_intersection l k
  end.
Time
Definition list_intersection_with (f : A \226\134\146 A \226\134\146 option A) :
  list A \226\134\146 list A \226\134\146 list A :=
  fix go l k :=
    match l with
    | [] => []
    | x :: l =>
        foldr (\206\187 y, match f x y with
                    | None => id
                    | Some z => (z::)
                    end) (go l k) k
    end.
Time End list_set.
Time
Fixpoint positives_flatten_go (xs : list positive) 
(acc : positive) : positive :=
  match xs with
  | [] => acc
  | x :: xs => positives_flatten_go xs (acc~1~0 ++ Preverse (Pdup x))
  end.
Time
Definition positives_flatten (xs : list positive) : positive :=
  positives_flatten_go xs 1.
Time
Fixpoint positives_unflatten_go (p : positive) (acc_xs : list positive)
(acc_elm : positive) : option (list positive) :=
  match p with
  | 1 => Some acc_xs
  | p'~0~0 => positives_unflatten_go p' acc_xs acc_elm~0
  | p'~1~1 => positives_unflatten_go p' acc_xs acc_elm~1
  | p'~1~0 => positives_unflatten_go p' (acc_elm :: acc_xs) 1
  | _ => None
  end%positive.
Time
Definition positives_unflatten (p : positive) : option (list positive) :=
  positives_unflatten_go p [] 1.
Time
Definition seqZ (m len : Z) : list Z :=
  (\206\187 i : nat, Z.add i m) <$> seq 0 (Z.to_nat len).
Time Arguments seqZ : simpl never.
Time
Tactic Notation "discriminate_list" hyp(H) :=
 (apply (f_equal length) in H; repeat csimpl in H || rewrite app_length in H;
   exfalso; lia).
Time
Tactic Notation "discriminate_list" :=
 (match goal with
  | H:_ =@{ list _} _ |- _ => discriminate_list H
  end).
Time
Lemma app_inj_1 {A} (l1 k1 l2 k2 : list A) :
  length l1 = length k1 \226\134\146 l1 ++ l2 = k1 ++ k2 \226\134\146 l1 = k1 \226\136\167 l2 = k2.
Time Proof.
Time revert k1.
Time (induction l1; intros [| ? ?]; naive_solver).
Time Qed.
Time
Lemma app_inj_2 {A} (l1 k1 l2 k2 : list A) :
  length l2 = length k2 \226\134\146 l1 ++ l2 = k1 ++ k2 \226\134\146 l1 = k1 \226\136\167 l2 = k2.
Time Proof.
Time (intros ? Hl).
Time (apply app_inj_1; auto).
Time (apply (f_equal length) in Hl).
Time (rewrite !app_length in Hl).
Time lia.
Time Qed.
Time
Ltac
 simplify_list_eq :=
  repeat
   match goal with
   | _ =>
       progress simplify_eq /=
   | H:_ ++ _ = _ ++ _
     |- _ => first
     [ apply app_inv_head in H
     | apply app_inv_tail in H
     | apply app_inj_1 in H; [ destruct H | done ]
     | apply app_inj_2 in H; [ destruct H | done ] ]
   | H:[?x] !! ?i = Some ?y
     |- _ =>
         destruct i;
          [ change_no_check (Some x = Some y) in H | discriminate ]
   end.
Time Section general_properties.
Time Context {A : Type}.
Time Implicit Types x y z : A.
Time Implicit Types l k : list A.
Time #[global]Instance: (Inj2 (=) (=) (=) (@cons A)).
Time Proof.
Time by injection 1.
Time Qed.
Time #[global]Instance: (\226\136\128 k, Inj (=) (=) (k ++)).
Time Proof.
Time (intros ? ? ?).
Time (apply app_inv_head).
Time Qed.
Time #[global]Instance: (\226\136\128 k, Inj (=) (=) (++k)).
Time Proof.
Time (intros ? ? ?).
Time (apply app_inv_tail).
Time Qed.
Time #[global]Instance: (Assoc (=) (@app A)).
Time Proof.
Time (intros ? ? ?).
Time (apply app_assoc).
Time Qed.
Time #[global]Instance: (LeftId (=) [] (@app A)).
Time Proof.
Time done.
Time Qed.
Time #[global]Instance: (RightId (=) [] (@app A)).
Time Proof.
Time intro.
Time (apply app_nil_r).
Time Qed.
Time Lemma app_nil l1 l2 : l1 ++ l2 = [] \226\134\148 l1 = [] \226\136\167 l2 = [].
Time Proof.
Time split.
Time (apply app_eq_nil).
Time by intros [-> ->].
Time Qed.
Time
Lemma app_singleton l1 l2 x :
  l1 ++ l2 = [x] \226\134\148 l1 = [] \226\136\167 l2 = [x] \226\136\168 l1 = [x] \226\136\167 l2 = [].
Time Proof.
Time split.
Time (apply app_eq_unit).
Time by intros [[-> ->]| [-> ->]].
Time Qed.
Time Lemma cons_middle x l1 l2 : l1 ++ x :: l2 = l1 ++ [x] ++ l2.
Time Proof.
Time done.
Time Qed.
Time Lemma list_eq l1 l2 : (\226\136\128 i, l1 !! i = l2 !! i) \226\134\146 l1 = l2.
Time Proof.
Time revert l2.
Time (induction l1 as [| x l1 IH]; intros [| y l2] H).
Time -
Time done.
Time -
Time discriminate (H 0).
Time -
Time discriminate (H 0).
Time -
Time (f_equal; [ by injection (H 0) |  ]).
Time (apply (IH _ $ (\206\187 i, H (S i)))).
Time Qed.
Time #[global]
Instance list_eq_dec  {dec : EqDecision A}: (EqDecision (list A)) :=
 (list_eq_dec dec).
Time #[global]Instance list_eq_nil_dec  l: (Decision (l = [])).
Time Proof.
Time by refine match l with
               | [] => left _
               | _ => right _
               end.
Time Defined.
Time
Lemma list_singleton_reflect l :
  option_reflect (\206\187 x, l = [x]) (length l \226\137\160 1) (maybe (\206\187 x, [x]) l).
Time Proof.
Time by destruct l as [| ? []]; constructor.
Time Defined.
Time Definition nil_length : length (@nil A) = 0 := eq_refl.
Time Definition cons_length x l : length (x :: l) = S (length l) := eq_refl.
Time Lemma nil_or_length_pos l : l = [] \226\136\168 length l \226\137\160 0.
Time Proof.
Time (destruct l; simpl; auto with lia).
Time Qed.
Time Lemma nil_length_inv l : length l = 0 \226\134\146 l = [].
Time Proof.
Time by destruct l.
Time Qed.
Time Lemma lookup_nil i : @nil A !! i = None.
Time Proof.
Time by destruct i.
Time Qed.
Time Lemma lookup_tail l i : tail l !! i = l !! S i.
Time Proof.
Time by destruct l.
Time Qed.
Time Lemma lookup_lt_Some l i x : l !! i = Some x \226\134\146 i < length l.
Time Proof.
Time revert i.
Time (induction l; intros [| ?] ?; naive_solver auto with arith).
Time Qed.
Time Lemma lookup_lt_is_Some_1 l i : is_Some (l !! i) \226\134\146 i < length l.
Time Proof.
Time (intros [? ?]; eauto using lookup_lt_Some).
Time Qed.
Time Lemma lookup_lt_is_Some_2 l i : i < length l \226\134\146 is_Some (l !! i).
Time Proof.
Time revert i.
Time (induction l; intros [| ?] ?; naive_solver eauto with lia).
Time Qed.
Time Lemma lookup_lt_is_Some l i : is_Some (l !! i) \226\134\148 i < length l.
Time Proof.
Time (split; auto using lookup_lt_is_Some_1, lookup_lt_is_Some_2).
Time Qed.
Time Lemma lookup_ge_None l i : l !! i = None \226\134\148 length l \226\137\164 i.
Time Proof.
Time (rewrite eq_None_not_Some, lookup_lt_is_Some).
Time lia.
Time Qed.
Time Lemma lookup_ge_None_1 l i : l !! i = None \226\134\146 length l \226\137\164 i.
Time Proof.
Time by rewrite lookup_ge_None.
Time Qed.
Time Lemma lookup_ge_None_2 l i : length l \226\137\164 i \226\134\146 l !! i = None.
Time Proof.
Time by rewrite lookup_ge_None.
Time Qed.
Time
Lemma list_eq_same_length l1 l2 n :
  length l2 = n
  \226\134\146 length l1 = n
    \226\134\146 (\226\136\128 i x y, i < n \226\134\146 l1 !! i = Some x \226\134\146 l2 !! i = Some y \226\134\146 x = y)
      \226\134\146 l1 = l2.
Time Proof.
Time (intros <- Hlen Hl; apply list_eq; intros i).
Time (destruct (l2 !! i) as [x| ] eqn:Hx).
Time -
Time (destruct (lookup_lt_is_Some_2 l1 i) as [y Hy]).
Time {
Time (rewrite Hlen; eauto using lookup_lt_Some).
Time }
Time (rewrite Hy; f_equal; apply (Hl i); eauto using lookup_lt_Some).
Time -
Time by rewrite lookup_ge_None, Hlen, <- lookup_ge_None.
Time Qed.
Time Lemma lookup_app_l l1 l2 i : i < length l1 \226\134\146 (l1 ++ l2) !! i = l1 !! i.
Time Proof.
Time revert i.
Time (induction l1; intros [| ?]; naive_solver auto with lia).
Time Qed.
Time
Lemma lookup_app_l_Some l1 l2 i x :
  l1 !! i = Some x \226\134\146 (l1 ++ l2) !! i = Some x.
Time Proof.
Time (intros).
Time (rewrite lookup_app_l; eauto using lookup_lt_Some).
Time Qed.
Time
Lemma lookup_app_r l1 l2 i :
  length l1 \226\137\164 i \226\134\146 (l1 ++ l2) !! i = l2 !! (i - length l1).
Time Proof.
Time revert i.
Time (induction l1; intros [| ?]; simpl; auto with lia).
Time Qed.
Time
Lemma lookup_app_Some l1 l2 i x :
  (l1 ++ l2) !! i = Some x
  \226\134\148 l1 !! i = Some x \226\136\168 length l1 \226\137\164 i \226\136\167 l2 !! (i - length l1) = Some x.
Time Proof.
Time split.
Time -
Time revert i.
Time
(induction l1 as [| y l1 IH]; intros [| i] ?; simplify_eq /=; auto with lia).
Time (destruct (IH i) as [?| [? ?]]; auto with lia).
Time -
Time (intros [?| [? ?]]; auto using lookup_app_l_Some).
Time by rewrite lookup_app_r.
Time Qed.
Time
Lemma list_lookup_middle l1 l2 x n :
  n = length l1 \226\134\146 (l1 ++ x :: l2) !! n = Some x.
Time Proof.
Time (intros ->).
Time by induction l1.
Time Qed.
Time Lemma nth_lookup l i d : nth i l d = default d (l !! i).
Time Proof.
Time revert i.
Time (induction l as [| x l IH]; intros [| i]; simpl; auto).
Time Qed.
Time Lemma nth_lookup_Some l i d x : l !! i = Some x \226\134\146 nth i l d = x.
Time Proof.
Time (rewrite nth_lookup).
Time by intros ->.
Time Qed.
Time
Lemma nth_lookup_or_length l i d :
  {l !! i = Some (nth i l d)} + {length l \226\137\164 i}.
Time Proof.
Time (rewrite nth_lookup).
Time (destruct (l !! i) eqn:?; eauto using lookup_ge_None_1).
Time Qed.
Time Lemma list_insert_alter l i x : <[i:=x]> l = alter (\206\187 _, x) i l.
Time Proof.
Time by revert i; induction l; intros []; intros; f_equal /=.
Time Qed.
Time Lemma alter_length f l i : length (alter f i l) = length l.
Time Proof.
Time revert i.
Time by induction l; intros [| ?]; f_equal /=.
Time Qed.
Time Lemma insert_length l i x : length (<[i:=x]> l) = length l.
Time Proof.
Time revert i.
Time by induction l; intros [| ?]; f_equal /=.
Time Qed.
Time Lemma list_lookup_alter f l i : alter f i l !! i = f <$> l !! i.
Time Proof.
Time revert i.
Time (induction l).
Time done.
Time (intros [| i]).
Time done.
Time (apply (IHl i)).
Time Qed.
Time Lemma list_lookup_alter_ne f l i j : i \226\137\160 j \226\134\146 alter f i l !! j = l !! j.
Time Proof.
Time revert i j.
Time (induction l; [ done |  ]).
Time (intros [] []; naive_solver).
Time Qed.
Time
Lemma list_lookup_insert l i x : i < length l \226\134\146 <[i:=x]> l !! i = Some x.
Time Proof.
Time revert i.
Time (induction l; intros [| ?] ?; f_equal /=; auto with lia).
Time Qed.
Time Lemma list_lookup_insert_ne l i j x : i \226\137\160 j \226\134\146 <[i:=x]> l !! j = l !! j.
Time Proof.
Time revert i j.
Time (induction l; [ done |  ]).
Time (intros [] []; naive_solver).
Time Qed.
Time
Lemma list_lookup_insert_Some l i x j y :
  <[i:=x]> l !! j = Some y
  \226\134\148 i = j \226\136\167 x = y \226\136\167 j < length l \226\136\168 i \226\137\160 j \226\136\167 l !! j = Some y.
Time Proof.
Time
(destruct (decide (i = j)) as [->| ];
  [ split | rewrite list_lookup_insert_ne by done; tauto ]).
Time -
Time (intros Hy).
Time (assert (j < length l)).
Time {
Time (rewrite <- (insert_length l j x); eauto using lookup_lt_Some).
Time }
Time (rewrite list_lookup_insert in Hy by done; naive_solver).
Time -
Time
(intros [(?, (?, ?))| [? ?]]; rewrite ?list_lookup_insert; naive_solver).
Time Qed.
Time
Lemma list_insert_commute l i j x y :
  i \226\137\160 j \226\134\146 <[i:=x]> (<[j:=y]> l) = <[j:=y]> (<[i:=x]> l).
Time Proof.
Time revert i j.
Time by induction l; intros [| ?] [| ?] ?; f_equal /=; auto.
Time Qed.
Time Lemma list_insert_id l i x : l !! i = Some x \226\134\146 <[i:=x]> l = l.
Time Proof.
Time revert i.
Time (induction l; intros [| i] [=]; f_equal /=; auto).
Time Qed.
Time Lemma list_insert_ge l i x : length l \226\137\164 i \226\134\146 <[i:=x]> l = l.
Time Proof.
Time revert i.
Time (induction l; intros [| i] ?; f_equal /=; auto with lia).
Time Qed.
Time Lemma list_insert_insert l i x y : <[i:=x]> (<[i:=y]> l) = <[i:=x]> l.
Time Proof.
Time revert i.
Time (induction l; intros [| i]; f_equal /=; auto).
Time Qed.
Time
Lemma list_lookup_other l i x :
  length l \226\137\160 1 \226\134\146 l !! i = Some x \226\134\146 \226\136\131 j y, j \226\137\160 i \226\136\167 l !! j = Some y.
Time Proof.
Time (intros).
Time (destruct i, l as [| x0 [| x1 l]]; simplify_eq /=).
Time -
Time by exists 1,x1.
Time -
Time by exists 0,x0.
Time Qed.
Time
Lemma alter_app_l f l1 l2 i :
  i < length l1 \226\134\146 alter f i (l1 ++ l2) = alter f i l1 ++ l2.
Time Proof.
Time revert i.
Time (induction l1; intros [| ?] ?; f_equal /=; auto with lia).
Time Qed.
Time
Lemma alter_app_r f l1 l2 i :
  alter f (length l1 + i) (l1 ++ l2) = l1 ++ alter f i l2.
Time Proof.
Time revert i.
Time (induction l1; intros [| ?]; f_equal /=; auto).
Time Qed.
Time
Lemma alter_app_r_alt f l1 l2 i :
  length l1 \226\137\164 i \226\134\146 alter f i (l1 ++ l2) = l1 ++ alter f (i - length l1) l2.
Time Proof.
Time (intros).
Time (assert (Hi : i = length l1 + (i - length l1)) by lia).
Time (rewrite Hi  at 1).
Time by apply alter_app_r.
Time Qed.
Time Lemma list_alter_id f l i : (\226\136\128 x, f x = x) \226\134\146 alter f i l = l.
Time Proof.
Time (intros ?).
Time revert i.
Time (induction l; intros [| ?]; f_equal /=; auto).
Time Qed.
Time
Lemma list_alter_ext f g l k i :
  (\226\136\128 x, l !! i = Some x \226\134\146 f x = g x) \226\134\146 l = k \226\134\146 alter f i l = alter g i k.
Time Proof.
Time (intros H ->).
Time revert i H.
Time (induction k; intros [| ?] ?; f_equal /=; auto).
Time Qed.
Time
Lemma list_alter_compose f g l i :
  alter (f \226\136\152 g) i l = alter f i (alter g i l).
Time Proof.
Time revert i.
Time (induction l; intros [| ?]; f_equal /=; auto).
Time Qed.
Time
Lemma list_alter_commute f g l i j :
  i \226\137\160 j \226\134\146 alter f i (alter g j l) = alter g j (alter f i l).
Time Proof.
Time revert i j.
Time (induction l; intros [| ?] [| ?] ?; f_equal /=; auto with lia).
Time Qed.
Time
Lemma insert_app_l l1 l2 i x :
  i < length l1 \226\134\146 <[i:=x]> (l1 ++ l2) = <[i:=x]> l1 ++ l2.
Time Proof.
Time revert i.
Time (induction l1; intros [| ?] ?; f_equal /=; auto with lia).
Time Qed.
Time
Lemma insert_app_r l1 l2 i x :
  <[length l1 + i:=x]> (l1 ++ l2) = l1 ++ <[i:=x]> l2.
Time Proof.
Time revert i.
Time (induction l1; intros [| ?]; f_equal /=; auto).
Time Qed.
Time
Lemma insert_app_r_alt l1 l2 i x :
  length l1 \226\137\164 i \226\134\146 <[i:=x]> (l1 ++ l2) = l1 ++ <[i - length l1:=x]> l2.
Time Proof.
Time (intros).
Time (assert (Hi : i = length l1 + (i - length l1)) by lia).
Time (rewrite Hi  at 1).
Time by apply insert_app_r.
Time Qed.
Time
Lemma delete_middle l1 l2 x : delete (length l1) (l1 ++ x :: l2) = l1 ++ l2.
Time Proof.
Time (induction l1; f_equal /=; auto).
Time Qed.
Time Lemma inserts_length l i k : length (list_inserts i k l) = length l.
Time Proof.
Time revert i.
Time (induction k; intros ?; csimpl; rewrite ?insert_length; auto).
Time Qed.
Time
Lemma list_lookup_inserts l i k j :
  i \226\137\164 j < i + length k
  \226\134\146 j < length l \226\134\146 list_inserts i k l !! j = k !! (j - i).
Time Proof.
Time revert i j.
Time (induction k as [| y k IH]; csimpl; intros i j ? ?; [ lia |  ]).
Time (destruct (decide (i = j)) as [->| ]).
Time {
Time
by rewrite list_lookup_insert, Nat.sub_diag by (rewrite inserts_length; lia).
Time }
Time (rewrite list_lookup_insert_ne, IH by lia).
Time by replace (j - i) with S (j - S i) by lia.
Time Qed.
Time
Lemma list_lookup_inserts_lt l i k j :
  j < i \226\134\146 list_inserts i k l !! j = l !! j.
Time Proof.
Time revert i j.
Time
(induction k; intros i j ?; csimpl; rewrite ?list_lookup_insert_ne by lia;
  auto with lia).
Time Qed.
Time
Lemma list_lookup_inserts_ge l i k j :
  i + length k \226\137\164 j \226\134\146 list_inserts i k l !! j = l !! j.
Time Proof.
Time revert i j.
Time
(induction k; csimpl; intros i j ?; rewrite ?list_lookup_insert_ne by lia;
  auto with lia).
Time Qed.
Time
Lemma list_lookup_inserts_Some l i k j y :
  list_inserts i k l !! j = Some y
  \226\134\148 (j < i \226\136\168 i + length k \226\137\164 j) \226\136\167 l !! j = Some y
    \226\136\168 i \226\137\164 j < i + length k \226\136\167 j < length l \226\136\167 k !! (j - i) = Some y.
Time Proof.
Time (destruct (decide (j < i))).
Time {
Time (rewrite list_lookup_inserts_lt by done; intuition lia).
Time }
Time (destruct (decide (i + length k \226\137\164 j))).
Time {
Time (rewrite list_lookup_inserts_ge by done; intuition lia).
Time }
Time split.
Time -
Time (intros Hy).
Time (assert (j < length l)).
Time {
Time (rewrite <- (inserts_length l i k); eauto using lookup_lt_Some).
Time }
Time (rewrite list_lookup_inserts in Hy by lia).
Time intuition lia.
Time -
Time intuition.
Time by rewrite list_lookup_inserts by lia.
Time Qed.
Time
Lemma list_insert_inserts_lt l i j x k :
  i < j \226\134\146 <[i:=x]> (list_inserts j k l) = list_inserts j k (<[i:=x]> l).
Time Proof.
Time revert i j.
Time
(induction k; intros i j ?; simpl; rewrite 1?list_insert_commute by lia; auto
  with f_equal).
Time Qed.
Time
Lemma list_inserts_app_l l1 l2 l3 i :
  list_inserts i (l1 ++ l2) l3 =
  list_inserts (length l1 + i) l2 (list_inserts i l1 l3).
Time Proof.
Time (revert l1 i; induction l1 as [| x l1 IH]; [ done |  ]).
Time intro i.
Time (simpl).
Time (rewrite IH, Nat.add_succ_r).
Time (apply list_insert_inserts_lt).
Time lia.
Time Qed.
Time
Lemma list_inserts_app_r l1 l2 l3 i :
  list_inserts (length l2 + i) l1 (l2 ++ l3) = l2 ++ list_inserts i l1 l3.
Time Proof.
Time (revert l1 i; induction l1 as [| x l1 IH]; [ done |  ]).
Time (intros i).
Time (simpl).
Time by rewrite plus_n_Sm, IH, insert_app_r.
Time Qed.
Time Lemma list_inserts_nil l1 i : list_inserts i l1 [] = [].
Time Proof.
Time (revert i; induction l1 as [| x l1 IH]; [ done |  ]).
Time intro i.
Time (simpl).
Time by rewrite IH.
Time Qed.
Time
Lemma list_inserts_cons l1 l2 i x :
  list_inserts (S i) l1 (x :: l2) = x :: list_inserts i l1 l2.
Time Proof.
Time (revert i; induction l1 as [| y l1 IH]; [ done |  ]).
Time intro i.
Time (simpl).
Time by rewrite IH.
Time Qed.
Time
Lemma list_inserts_0_r l1 l2 l3 :
  length l1 = length l2 \226\134\146 list_inserts 0 l1 (l2 ++ l3) = l1 ++ l3.
Time Proof.
Time revert l2.
Time
(induction l1 as [| x l1 IH]; intros [| y l2] ?; simplify_eq /=; [ done |  ]).
Time (rewrite list_inserts_cons).
Time (simpl).
Time by rewrite IH.
Time Qed.
Time
Lemma list_inserts_0_l l1 l2 l3 :
  length l1 = length l3 \226\134\146 list_inserts 0 (l1 ++ l2) l3 = l1.
Time Proof.
Time revert l3.
Time (induction l1 as [| x l1 IH]; intros [| z l3] ?; simplify_eq /=).
Time {
Time by rewrite list_inserts_nil.
Time }
Time (rewrite list_inserts_cons).
Time (simpl).
Time by rewrite IH.
Time Qed.
Time Lemma not_elem_of_nil x : x \226\136\137 [].
Time Proof.
Time by inversion 1.
Time Qed.
Time Lemma elem_of_nil x : x \226\136\136 [] \226\134\148 False.
Time Proof.
Time intuition.
Time by destruct (not_elem_of_nil x).
Time Qed.
Time Lemma elem_of_nil_inv l : (\226\136\128 x, x \226\136\137 l) \226\134\146 l = [].
Time Proof.
Time (destruct l).
Time done.
Time by edestruct 1; constructor.
Time Qed.
Time Lemma elem_of_not_nil x l : x \226\136\136 l \226\134\146 l \226\137\160 [].
Time Proof.
Time (intros ? ->).
Time by apply (elem_of_nil x).
Time Qed.
Time Lemma elem_of_cons l x y : x \226\136\136 y :: l \226\134\148 x = y \226\136\168 x \226\136\136 l.
Time Proof.
Time by split; [ inversion 1; subst | intros [->| ?] ]; constructor.
Time Qed.
Time Lemma not_elem_of_cons l x y : x \226\136\137 y :: l \226\134\148 x \226\137\160 y \226\136\167 x \226\136\137 l.
Time Proof.
Time (rewrite elem_of_cons).
Time tauto.
Time Qed.
Time Lemma elem_of_app l1 l2 x : x \226\136\136 l1 ++ l2 \226\134\148 x \226\136\136 l1 \226\136\168 x \226\136\136 l2.
Time Proof.
Time (induction l1).
Time -
Time (split; [ by right |  ]).
Time (intros [Hx| ]; [  | done ]).
Time by destruct (elem_of_nil x).
Time -
Time (simpl).
Time (rewrite !elem_of_cons, IHl1).
Time tauto.
Time Qed.
Time Lemma not_elem_of_app l1 l2 x : x \226\136\137 l1 ++ l2 \226\134\148 (x \226\136\137 l1) \226\136\167 x \226\136\137 l2.
Time Proof.
Time (rewrite elem_of_app).
Time tauto.
Time Qed.
Time Lemma elem_of_list_singleton x y : x \226\136\136 [y] \226\134\148 x = y.
Time Proof.
Time (rewrite elem_of_cons, elem_of_nil).
Time tauto.
Time Qed.
Time #[global]
Instance elem_of_list_permutation_proper  x: (Proper ((\226\137\161\226\130\154) ==> iff) (x\226\136\136)).
Time Proof.
Time (induction 1; rewrite ?elem_of_nil, ?elem_of_cons; intuition).
Time Qed.
Time Lemma elem_of_list_split l x : x \226\136\136 l \226\134\146 \226\136\131 l1 l2, l = l1 ++ x :: l2.
Time Proof.
Time (induction 1 as [x l| x y l ? [l1 [l2 ->]]]; [ by eexists [],l |  ]).
Time by exists (y :: l1),l2.
Time Qed.
Time
Lemma elem_of_list_split_l `{EqDecision A} l x :
  x \226\136\136 l \226\134\146 \226\136\131 l1 l2, l = l1 ++ x :: l2 \226\136\167 x \226\136\137 l1.
Time Proof.
Time (induction 1 as [x l| x y l ? IH]).
Time {
Time exists [],l.
Time (rewrite elem_of_nil).
Time naive_solver.
Time }
Time (destruct (decide (x = y)) as [->| ?]).
Time -
Time exists [],l.
Time (rewrite elem_of_nil).
Time naive_solver.
Time -
Time (destruct IH as (l1, (l2, (->, ?)))).
Time exists (y :: l1),l2.
Time (rewrite elem_of_cons).
Time naive_solver.
Time Qed.
Time
Lemma elem_of_list_split_r `{EqDecision A} l x :
  x \226\136\136 l \226\134\146 \226\136\131 l1 l2, l = l1 ++ x :: l2 \226\136\167 x \226\136\137 l2.
Time Proof.
Time (induction l as [| y l IH] using rev_ind).
Time {
Time by rewrite elem_of_nil.
Time }
Time (destruct (decide (x = y)) as [->| ]).
Time -
Time exists l,[].
Time (rewrite elem_of_nil).
Time naive_solver.
Time -
Time (rewrite elem_of_app, elem_of_list_singleton).
Time (intros [?| ->]; try done).
Time (destruct IH as (l1, (l2, (->, ?))); auto).
Time exists l1,(l2 ++ [y]).
Time (rewrite elem_of_app, elem_of_list_singleton, <- (assoc_L (++))).
Time naive_solver.
Time Qed.
Time Lemma elem_of_list_lookup_1 l x : x \226\136\136 l \226\134\146 \226\136\131 i, l !! i = Some x.
Time Proof.
Time (induction 1 as [| ? ? ? ? IH]; [ by exists 0 |  ]).
Time (destruct IH as [i ?]; auto).
Time by exists (S i).
Time Qed.
Time Lemma elem_of_list_lookup_2 l i x : l !! i = Some x \226\134\146 x \226\136\136 l.
Time Proof.
Time revert i.
Time (induction l; intros [| i] ?; simplify_eq /=; constructor; eauto).
Time Qed.
Time Lemma elem_of_list_lookup l x : x \226\136\136 l \226\134\148 (\226\136\131 i, l !! i = Some x).
Time Proof.
Time firstorder  eauto using elem_of_list_lookup_1, elem_of_list_lookup_2.
Time Qed.
Time
Lemma elem_of_list_omap {B} (f : A \226\134\146 option B) l (y : B) :
  y \226\136\136 omap f l \226\134\148 (\226\136\131 x, x \226\136\136 l \226\136\167 f x = Some y).
Time Proof.
Time split.
Time -
Time
(induction l as [| x l]; csimpl; repeat case_match; inversion 1; subst;
  setoid_rewrite elem_of_cons; naive_solver).
Time -
Time (intros (x, (Hx, ?))).
Time
by
 induction Hx; csimpl; repeat case_match; simplify_eq; try constructor; auto.
Time Qed.
Time Lemma list_elem_of_insert l i x : i < length l \226\134\146 x \226\136\136 <[i:=x]> l.
Time Proof.
Time (intros).
Time by eapply elem_of_list_lookup_2, list_lookup_insert.
Time Qed.
Time Lemma nth_elem_of l i d : i < length l \226\134\146 nth i l d \226\136\136 l.
Time Proof.
Time (intros; eapply elem_of_list_lookup_2).
Time (destruct (nth_lookup_or_length l i d); [ done | by lia ]).
Time Qed.
Time Lemma NoDup_nil : NoDup (@nil A) \226\134\148 True.
Time Proof.
Time (split; constructor).
Time Qed.
Time Lemma NoDup_cons x l : NoDup (x :: l) \226\134\148 (x \226\136\137 l) \226\136\167 NoDup l.
Time Proof.
Time split.
Time by inversion 1.
Time (intros [? ?]).
Time by constructor.
Time Qed.
Time Lemma NoDup_cons_11 x l : NoDup (x :: l) \226\134\146 x \226\136\137 l.
Time Proof.
Time (rewrite NoDup_cons).
Time by intros [? ?].
Time Qed.
Time Lemma NoDup_cons_12 x l : NoDup (x :: l) \226\134\146 NoDup l.
Time Proof.
Time (rewrite NoDup_cons).
Time by intros [? ?].
Time Qed.
Time Lemma NoDup_singleton x : NoDup [x].
Time Proof.
Time constructor.
Time (apply not_elem_of_nil).
Time constructor.
Time Qed.
Time
Lemma NoDup_app l k :
  NoDup (l ++ k) \226\134\148 NoDup l \226\136\167 (\226\136\128 x, x \226\136\136 l \226\134\146 x \226\136\137 k) \226\136\167 NoDup k.
Time Proof.
Time (induction l; simpl).
Time -
Time (rewrite NoDup_nil).
Time setoid_rewrite elem_of_nil.
Time naive_solver.
Time -
Time (rewrite !NoDup_cons).
Time setoid_rewrite elem_of_cons.
Time setoid_rewrite elem_of_app.
Time naive_solver.
Time Qed.
Time #[global]Instance NoDup_proper : (Proper ((\226\137\161\226\130\154) ==> iff) (@NoDup A)).
Time Proof.
Time (induction 1 as [| x l k Hlk IH| | ]).
Time -
Time by rewrite !NoDup_nil.
Time -
Time by rewrite !NoDup_cons, IH, Hlk.
Time -
Time (rewrite !NoDup_cons, !elem_of_cons).
Time intuition.
Time -
Time intuition.
Time Qed.
Time
Lemma NoDup_lookup l i j x :
  NoDup l \226\134\146 l !! i = Some x \226\134\146 l !! j = Some x \226\134\146 i = j.
Time Proof.
Time (intros Hl).
Time revert i j.
Time (induction Hl as [| x' l Hx Hl IH]).
Time {
Time (intros; simplify_eq).
Time }
Time
(intros [| i] [| j] ? ?; simplify_eq /=; eauto with f_equal; exfalso; eauto
  using elem_of_list_lookup_2).
Time Qed.
Time
Lemma NoDup_alt l :
  NoDup l \226\134\148 (\226\136\128 i j x, l !! i = Some x \226\134\146 l !! j = Some x \226\134\146 i = j).
Time Proof.
Time (split; eauto using NoDup_lookup).
Time (induction l as [| x l IH]; intros Hl; constructor).
Time -
Time (rewrite elem_of_list_lookup).
Time (intros [i ?]).
Time by feed pose proof Hl (S i) 0 x; auto.
Time -
Time (apply IH).
Time (intros i j x' ? ?).
Time by apply (inj S), (Hl (S i) (S j) x').
Time Qed.
Time Section no_dup_dec.
Time Context `{!EqDecision A}.
Time #[global]
Instance NoDup_dec : (\226\136\128 l, Decision (NoDup l)) :=
 (fix NoDup_dec l :=
    match l return (Decision (NoDup l)) with
    | [] => left NoDup_nil_2
    | x :: l =>
        match decide_rel (\226\136\136) x l with
        | left Hin => right (\206\187 H, NoDup_cons_11 _ _ H Hin)
        | right Hin =>
            match NoDup_dec l with
            | left H => left (NoDup_cons_2 _ _ Hin H)
            | right H => right (H \226\136\152 NoDup_cons_12 _ _)
            end
        end
    end).
Time Lemma elem_of_remove_dups l x : x \226\136\136 remove_dups l \226\134\148 x \226\136\136 l.
Time Proof.
Time
(split; induction l; simpl; repeat case_decide; rewrite ?elem_of_cons;
  intuition simplify_eq; auto).
Time Qed.
Time Lemma NoDup_remove_dups l : NoDup (remove_dups l).
Time Proof.
Time (induction l; simpl; repeat case_decide; try constructor; auto).
Time by rewrite elem_of_remove_dups.
Time Qed.
Time End no_dup_dec.
Time Section list_set.
Time
Lemma elem_of_list_intersection_with f l k x :
  x \226\136\136 list_intersection_with f l k
  \226\134\148 (\226\136\131 x1 x2, x1 \226\136\136 l \226\136\167 x2 \226\136\136 k \226\136\167 f x1 x2 = Some x).
Time Proof.
Time split.
Time -
Time (induction l as [| x1 l IH]; simpl; [ by rewrite elem_of_nil |  ]).
Time (intros Hx).
Time setoid_rewrite elem_of_cons.
Time
(cut ((\226\136\131 x2, x2 \226\136\136 k \226\136\167 f x1 x2 = Some x) \226\136\168 x \226\136\136 list_intersection_with f l k);
  [ naive_solver |  ]).
Time clear IH.
Time revert Hx.
Time (generalize (list_intersection_with f l k)).
Time (induction k; simpl; [ by auto |  ]).
Time (case_match; setoid_rewrite elem_of_cons; naive_solver).
Time -
Time (intros (x1, (x2, (Hx1, (Hx2, Hx))))).
Time (induction Hx1 as [x1| x1 ? l ? IH]; simpl).
Time +
Time (generalize (list_intersection_with f l k)).
Time (induction Hx2; simpl; [ by rewrite Hx; left |  ]).
Time (case_match; simpl; try setoid_rewrite elem_of_cons; auto).
Time +
Time (generalize (IH Hx)).
Time clear Hx IH Hx2.
Time (generalize (list_intersection_with f l k)).
Time (induction k; simpl; intros; [ done |  ]).
Time (case_match; simpl; rewrite ?elem_of_cons; auto).
Time Qed.
Time Context `{!EqDecision A}.
Time
Lemma elem_of_list_difference l k x : x \226\136\136 list_difference l k \226\134\148 x \226\136\136 l \226\136\167 x \226\136\137 k.
Time Proof.
Time
(split; induction l; simpl; try case_decide;
  rewrite ?elem_of_nil, ?elem_of_cons; intuition congruence).
Time Qed.
Time Lemma NoDup_list_difference l k : NoDup l \226\134\146 NoDup (list_difference l k).
Time Proof.
Time (induction 1; simpl; try case_decide).
Time -
Time constructor.
Time -
Time done.
Time -
Time constructor.
Time (rewrite elem_of_list_difference; intuition).
Time done.
Time Qed.
Time Lemma elem_of_list_union l k x : x \226\136\136 list_union l k \226\134\148 x \226\136\136 l \226\136\168 x \226\136\136 k.
Time Proof.
Time (unfold list_union).
Time (rewrite elem_of_app, elem_of_list_difference).
Time intuition.
Time (case (decide (x \226\136\136 k)); intuition).
Time Qed.
Time Lemma NoDup_list_union l k : NoDup l \226\134\146 NoDup k \226\134\146 NoDup (list_union l k).
Time Proof.
Time (intros).
Time (apply NoDup_app).
Time (repeat split).
Time -
Time by apply NoDup_list_difference.
Time -
Time intro.
Time (rewrite elem_of_list_difference).
Time intuition.
Time -
Time done.
Time Qed.
Time
Lemma elem_of_list_intersection l k x :
  x \226\136\136 list_intersection l k \226\134\148 x \226\136\136 l \226\136\167 x \226\136\136 k.
Time Proof.
Time
(split; induction l; simpl; repeat case_decide;
  rewrite ?elem_of_nil, ?elem_of_cons; intuition congruence).
Time Qed.
Time
Lemma NoDup_list_intersection l k : NoDup l \226\134\146 NoDup (list_intersection l k).
Time Proof.
Time (induction 1; simpl; try case_decide).
Time -
Time constructor.
Time -
Time constructor.
Time (rewrite elem_of_list_intersection; intuition).
Time done.
Time -
Time done.
Time Qed.
Time End list_set.
Time Section find.
Time Context (P : A \226\134\146 Prop) `{\226\136\128 x, Decision (P x)}.
Time
Lemma list_find_Some l i x :
  list_find P l = Some (i, x) \226\134\146 l !! i = Some x \226\136\167 P x.
Time Proof.
Time
(revert i; induction l; intros [] ?;
  repeat (first
   [ match goal with
     | x:prod _ _ |- _ => destruct x
     end | simplify_option_eq ]); eauto).
Time Qed.
Time Lemma list_find_None l : list_find P l = None \226\134\146 Forall (\206\187 x, \194\172 P x) l.
Time Proof.
Time (induction l as [| ? l IHl]; [ eauto |  ]).
Time (simpl).
Time (case_decide; [ done |  ]).
Time (intros).
Time (constructor; [ done |  ]).
Time (apply IHl).
Time by destruct (list_find P l).
Time Qed.
Time Lemma list_find_elem_of l x : x \226\136\136 l \226\134\146 P x \226\134\146 is_Some (list_find P l).
Time Proof.
Time (induction 1 as [| x y l ? IH]; intros; simplify_option_eq; eauto).
Time by destruct IH as [[i x'] ->]; [  | exists (S i, x') ].
Time Qed.
Time
Lemma list_find_fmap {B : Type} (f : B \226\134\146 A) (l : list B) :
  list_find P (f <$> l) = prod_map id f <$> list_find (P \226\136\152 f) l.
Time Proof.
Time (induction l as [| x l IH]; [ done |  ]).
Time csimpl.
Time (case_decide; [ done |  ]).
Time (rewrite IH).
Time by destruct (list_find (P \226\136\152 f) l).
Time Qed.
Time
Lemma list_find_ext (Q : A \226\134\146 Prop) `{\226\136\128 x, Decision (Q x)} 
  l : (\226\136\128 x, P x \226\134\148 Q x) \226\134\146 list_find P l = list_find Q l.
Time Proof.
Time (intros HPQ).
Time (induction l as [| x l IH]; simpl; [ done |  ]).
Time by rewrite (decide_iff (P x) (Q x)), IH by done.
Time Qed.
Time End find.
Time
Lemma list_fmap_omap {B C : Type} (f : A \226\134\146 option B) 
  (g : B \226\134\146 C) (l : list A) : g <$> omap f l = omap (\206\187 x, g <$> f x) l.
Time Proof.
Time (induction l as [| x y IH]; [ done |  ]).
Time csimpl.
Time (destruct (f x); [  | done ]).
Time csimpl.
Time by f_equal.
Time Qed.
Time
Lemma list_omap_ext {B C : Type} (f : A \226\134\146 option C) 
  (g : B \226\134\146 option C) (l1 : list A) (l2 : list B) :
  Forall2 (\206\187 a b, f a = g b) l1 l2 \226\134\146 omap f l1 = omap g l2.
Time Proof.
Time (induction 1 as [| x y l l' Hfg ? IH]; [ done |  ]).
Time csimpl.
Time (rewrite Hfg).
Time (destruct (g y); [  | done ]).
Time by f_equal.
Time Qed.
Time Lemma reverse_nil : reverse [] =@{ list A} [].
Time Proof.
Time done.
Time Qed.
Time Lemma reverse_singleton x : reverse [x] = [x].
Time Proof.
Time done.
Time Qed.
Time Lemma reverse_cons l x : reverse (x :: l) = reverse l ++ [x].
Time Proof.
Time (unfold reverse).
Time by rewrite <- !rev_alt.
Time Qed.
Time Lemma reverse_snoc l x : reverse (l ++ [x]) = x :: reverse l.
Time Proof.
Time (unfold reverse).
Time by rewrite <- !rev_alt, rev_unit.
Time Qed.
Time Lemma reverse_app l1 l2 : reverse (l1 ++ l2) = reverse l2 ++ reverse l1.
Time Proof.
Time (unfold reverse).
Time (rewrite <- !rev_alt).
Time (apply rev_app_distr).
Time Qed.
Time Lemma reverse_length l : length (reverse l) = length l.
Time Proof.
Time (unfold reverse).
Time (rewrite <- !rev_alt).
Time (apply rev_length).
Time Qed.
Time Lemma reverse_involutive l : reverse (reverse l) = l.
Time Proof.
Time (unfold reverse).
Time (rewrite <- !rev_alt).
Time (apply rev_involutive).
Time Qed.
Time Lemma elem_of_reverse_2 x l : x \226\136\136 l \226\134\146 x \226\136\136 reverse l.
Time Proof.
Time
(induction 1; rewrite reverse_cons, elem_of_app, ?elem_of_list_singleton;
  intuition).
Time Qed.
Time Lemma elem_of_reverse x l : x \226\136\136 reverse l \226\134\148 x \226\136\136 l.
Time Proof.
Time (split; auto using elem_of_reverse_2).
Time (intros).
Time (rewrite <- (reverse_involutive l)).
Time by apply elem_of_reverse_2.
Time Qed.
Time #[global]Instance: (Inj (=) (=) (@reverse A)).
Time Proof.
Time (intros l1 l2 Hl).
Time by rewrite <- (reverse_involutive l1), <- (reverse_involutive l2), Hl.
Time Qed.
Time
Lemma sum_list_with_app (f : A \226\134\146 nat) l k :
  sum_list_with f (l ++ k) = sum_list_with f l + sum_list_with f k.
Time Proof.
Time (induction l; simpl; lia).
Time Qed.
Time
Lemma sum_list_with_reverse (f : A \226\134\146 nat) l :
  sum_list_with f (reverse l) = sum_list_with f l.
Time Proof.
Time
(induction l; simpl; rewrite ?reverse_cons, ?sum_list_with_app; simpl; lia).
Time Qed.
Time Lemma last_snoc x l : last (l ++ [x]) = Some x.
Time Proof.
Time (induction l as [| ? []]; simpl; auto).
Time Qed.
Time Lemma last_reverse l : last (reverse l) = head l.
Time Proof.
Time by destruct l as [| x l]; rewrite ?reverse_cons, ?last_snoc.
Time Qed.
Time Lemma head_reverse l : head (reverse l) = last l.
Time Proof.
Time by rewrite <- last_reverse, reverse_involutive.
Time Qed.
Time Definition take_drop i l : take i l ++ drop i l = l := firstn_skipn i l.
Time
Lemma take_drop_middle l i x :
  l !! i = Some x \226\134\146 take i l ++ x :: drop (S i) l = l.
Time Proof.
Time revert i x.
Time (induction l; intros [| ?] ? ?; simplify_eq /=; f_equal; auto).
Time Qed.
Time Lemma take_nil n : take n [] =@{ list A} [].
Time Proof.
Time by destruct n.
Time Qed.
Time Lemma take_S_r l n x : l !! n = Some x \226\134\146 take (S n) l = take n l ++ [x].
Time Proof.
Time revert n.
Time (induction l; intros []; naive_solver eauto with f_equal).
Time Qed.
Time Lemma take_app l k : take (length l) (l ++ k) = l.
Time Proof.
Time (induction l; f_equal /=; auto).
Time Qed.
Time Lemma take_app_alt l k n : n = length l \226\134\146 take n (l ++ k) = l.
Time Proof.
Time (intros ->).
Time by apply take_app.
Time Qed.
Time
Lemma take_app3_alt l1 l2 l3 n :
  n = length l1 \226\134\146 take n ((l1 ++ l2) ++ l3) = l1.
Time Proof.
Time (intros ->).
Time by rewrite <- (assoc_L (++)), take_app.
Time Qed.
Time Lemma take_app_le l k n : n \226\137\164 length l \226\134\146 take n (l ++ k) = take n l.
Time Proof.
Time revert n.
Time (induction l; intros [| ?] ?; f_equal /=; auto with lia).
Time Qed.
Time
Lemma take_plus_app l k n m :
  length l = n \226\134\146 take (n + m) (l ++ k) = l ++ take m k.
Time Proof.
Time (intros <-).
Time (induction l; f_equal /=; auto).
Time Qed.
Time
Lemma take_app_ge l k n :
  length l \226\137\164 n \226\134\146 take n (l ++ k) = l ++ take (n - length l) k.
Time Proof.
Time revert n.
Time (induction l; intros [| ?] ?; f_equal /=; auto with lia).
Time Qed.
Time Lemma take_ge l n : length l \226\137\164 n \226\134\146 take n l = l.
Time Proof.
Time revert n.
Time (induction l; intros [| ?] ?; f_equal /=; auto with lia).
Time Qed.
Time Lemma take_take l n m : take n (take m l) = take (min n m) l.
Time Proof.
Time revert n m.
Time (induction l; intros [| ?] [| ?]; f_equal /=; auto).
Time Qed.
Time Lemma take_idemp l n : take n (take n l) = take n l.
Time Proof.
Time by rewrite take_take, Min.min_idempotent.
Time Qed.
Time Lemma take_length l n : length (take n l) = min n (length l).
Time Proof.
Time revert n.
Time (induction l; intros [| ?]; f_equal /=; done).
Time Qed.
Time Lemma take_length_le l n : n \226\137\164 length l \226\134\146 length (take n l) = n.
Time Proof.
Time (rewrite take_length).
Time (apply Min.min_l).
Time Qed.
Time Lemma take_length_ge l n : length l \226\137\164 n \226\134\146 length (take n l) = length l.
Time Proof.
Time (rewrite take_length).
Time (apply Min.min_r).
Time Qed.
Time
Lemma take_drop_commute l n m : take n (drop m l) = drop m (take (m + n) l).
Time Proof.
Time revert n m.
Time (induction l; intros [| ?] [| ?]; simpl; auto using take_nil with lia).
Time Qed.
Time Lemma lookup_take l n i : i < n \226\134\146 take n l !! i = l !! i.
Time Proof.
Time revert n i.
Time (induction l; intros [| n] [| i] ?; simpl; auto with lia).
Time Qed.
Time Lemma lookup_take_ge l n i : n \226\137\164 i \226\134\146 take n l !! i = None.
Time Proof.
Time revert n i.
Time (induction l; intros [| ?] [| ?] ?; simpl; auto with lia).
Time Qed.
Time Lemma take_alter f l n i : n \226\137\164 i \226\134\146 take n (alter f i l) = take n l.
Time Proof.
Time (intros).
Time (apply list_eq).
Time (intros j).
Time (destruct (le_lt_dec n j)).
Time -
Time by rewrite !lookup_take_ge.
Time -
Time by rewrite !lookup_take, !list_lookup_alter_ne by lia.
Time Qed.
Time Lemma take_insert l n i x : n \226\137\164 i \226\134\146 take n (<[i:=x]> l) = take n l.
Time Proof.
Time (intros).
Time (apply list_eq).
Time (intros j).
Time (destruct (le_lt_dec n j)).
Time -
Time by rewrite !lookup_take_ge.
Time -
Time by rewrite !lookup_take, !list_lookup_insert_ne by lia.
Time Qed.
Time
Lemma take_insert_lt l n i x :
  i < n \226\134\146 take n (<[i:=x]> l) = <[i:=x]> (take n l).
Time Proof.
Time revert l i.
Time (induction n as [| ? IHn]; auto; simpl).
Time (intros [| ] [| ] ?; auto; simpl).
Time by rewrite IHn by lia.
Time Qed.
Time Lemma drop_0 l : drop 0 l = l.
Time Proof.
Time done.
Time Qed.
Time Lemma drop_nil n : drop n [] =@{ list A} [].
Time Proof.
Time by destruct n.
Time Qed.
Time Lemma drop_S l x n : l !! n = Some x \226\134\146 drop n l = x :: drop (S n) l.
Time Proof.
Time revert n.
Time (induction l; intros []; naive_solver).
Time Qed.
Time Lemma drop_length l n : length (drop n l) = length l - n.
Time Proof.
Time revert n.
Time by induction l; intros [| i]; f_equal /=.
Time Qed.
Time Lemma drop_ge l n : length l \226\137\164 n \226\134\146 drop n l = [].
Time Proof.
Time revert n.
Time (induction l; intros [| ?]; simpl in *; auto with lia).
Time Qed.
Time Lemma drop_all l : drop (length l) l = [].
Time Proof.
Time by apply drop_ge.
Time Qed.
Time Lemma drop_drop l n1 n2 : drop n1 (drop n2 l) = drop (n2 + n1) l.
Time Proof.
Time revert n2.
Time (induction l; intros [| ?]; simpl; rewrite ?drop_nil; auto).
Time Qed.
Time
Lemma drop_app_le l k n : n \226\137\164 length l \226\134\146 drop n (l ++ k) = drop n l ++ k.
Time Proof.
Time revert n.
Time (induction l; intros [| ?]; simpl; auto with lia).
Time Qed.
Time Lemma drop_app l k : drop (length l) (l ++ k) = k.
Time Proof.
Time by rewrite drop_app_le, drop_all.
Time Qed.
Time Lemma drop_app_alt l k n : n = length l \226\134\146 drop n (l ++ k) = k.
Time Proof.
Time (intros ->).
Time by apply drop_app.
Time Qed.
Time
Lemma drop_app3_alt l1 l2 l3 n :
  n = length l1 \226\134\146 drop n ((l1 ++ l2) ++ l3) = l2 ++ l3.
Time Proof.
Time (intros ->).
Time by rewrite <- (assoc_L (++)), drop_app.
Time Qed.
Time
Lemma drop_app_ge l k n :
  length l \226\137\164 n \226\134\146 drop n (l ++ k) = drop (n - length l) k.
Time Proof.
Time (intros).
Time (rewrite <- (Nat.sub_add (length l) n)  at 1 by done).
Time by rewrite Nat.add_comm, <- drop_drop, drop_app.
Time Qed.
Time
Lemma drop_plus_app l k n m : length l = n \226\134\146 drop (n + m) (l ++ k) = drop m k.
Time Proof.
Time (intros <-).
Time by rewrite <- drop_drop, drop_app.
Time Qed.
Time Lemma lookup_drop l n i : drop n l !! i = l !! (n + i).
Time Proof.
Time revert n i.
Time (induction l; intros [| i] ?; simpl; auto).
Time Qed.
Time Lemma drop_alter f l n i : i < n \226\134\146 drop n (alter f i l) = drop n l.
Time Proof.
Time (intros).
Time (apply list_eq).
Time (intros j).
Time by rewrite !lookup_drop, !list_lookup_alter_ne by lia.
Time Qed.
Time Lemma drop_insert l n i x : i < n \226\134\146 drop n (<[i:=x]> l) = drop n l.
Time Proof.
Time (intros).
Time (apply list_eq).
Time (intros j).
Time by rewrite !lookup_drop, !list_lookup_insert_ne by lia.
Time Qed.
Time Lemma delete_take_drop l i : delete i l = take i l ++ drop (S i) l.
Time Proof.
Time revert i.
Time (induction l; intros [| ?]; f_equal /=; auto).
Time Qed.
Time
Lemma take_take_drop l n m : take n l ++ take m (drop n l) = take (n + m) l.
Time Proof.
Time revert n m.
Time (induction l; intros [| ?] [| ?]; f_equal /=; auto).
Time Qed.
Time
Lemma drop_take_drop l n m : n \226\137\164 m \226\134\146 drop n (take m l) ++ drop m l = drop n l.
Time Proof.
Time revert n m.
Time
(induction l; intros [| ?] [| ?] ?; f_equal /=; auto using take_drop with lia).
Time Qed.
Time
Lemma app_eq_inv l1 l2 k1 k2 :
  l1 ++ l2 = k1 ++ k2
  \226\134\146 (\226\136\131 k, l1 = k1 ++ k \226\136\167 k2 = k ++ l2) \226\136\168 (\226\136\131 k, k1 = l1 ++ k \226\136\167 l2 = k ++ k2).
Time Proof.
Time (intros Hlk).
Time (destruct (decide (length l1 < length k1))).
Time -
Time right.
Time (rewrite <- (take_drop (length l1) k1), <- (assoc_L _) in Hlk).
Time (apply app_inj_1 in Hlk as [Hl1 Hl2]; [  | rewrite take_length; lia ]).
Time exists (drop (length l1) k1).
Time by rewrite Hl1  at 1; rewrite take_drop.
Time -
Time left.
Time (rewrite <- (take_drop (length k1) l1), <- (assoc_L _) in Hlk).
Time (apply app_inj_1 in Hlk as [Hk1 Hk2]; [  | rewrite take_length; lia ]).
Time exists (drop (length k1) l1).
Time by rewrite <- Hk1  at 1; rewrite take_drop.
Time Qed.
Time Lemma replicate_length n x : length (replicate n x) = n.
Time Proof.
Time (induction n; simpl; auto).
Time Qed.
Time
Lemma lookup_replicate n x y i : replicate n x !! i = Some y \226\134\148 y = x \226\136\167 i < n.
Time Proof.
Time split.
Time -
Time revert i.
Time (induction n; intros [| ?]; naive_solver auto with lia).
Time -
Time (intros [-> Hi]).
Time revert i Hi.
Time (induction n; intros [| ?]; naive_solver auto with lia).
Time Qed.
Time Lemma elem_of_replicate n x y : y \226\136\136 replicate n x \226\134\148 y = x \226\136\167 n \226\137\160 0.
Time Proof.
Time (rewrite elem_of_list_lookup, Nat.neq_0_lt_0).
Time (setoid_rewrite lookup_replicate; naive_solver eauto with lia).
Time Qed.
Time
Lemma lookup_replicate_1 n x y i :
  replicate n x !! i = Some y \226\134\146 y = x \226\136\167 i < n.
Time Proof.
Time by rewrite lookup_replicate.
Time Qed.
Time Lemma lookup_replicate_2 n x i : i < n \226\134\146 replicate n x !! i = Some x.
Time Proof.
Time by rewrite lookup_replicate.
Time Qed.
Time Lemma lookup_replicate_None n x i : n \226\137\164 i \226\134\148 replicate n x !! i = None.
Time Proof.
Time (rewrite eq_None_not_Some, Nat.le_ngt).
Time split.
Time -
Time (intros Hin [x' Hx']; destruct Hin).
Time (rewrite lookup_replicate in Hx'; tauto).
Time -
Time (intros Hx ?).
Time (destruct Hx).
Time (exists x; auto using lookup_replicate_2).
Time Qed.
Time Lemma insert_replicate x n i : <[i:=x]> (replicate n x) = replicate n x.
Time Proof.
Time revert i.
Time (induction n; intros [| ?]; f_equal /=; auto).
Time Qed.
Time Lemma elem_of_replicate_inv x n y : x \226\136\136 replicate n y \226\134\146 x = y.
Time Proof.
Time (induction n; simpl; rewrite ?elem_of_nil, ?elem_of_cons; intuition).
Time Qed.
Time Lemma replicate_S n x : replicate (S n) x = x :: replicate n x.
Time Proof.
Time done.
Time Qed.
Time Lemma replicate_S_end n x : replicate (S n) x = replicate n x ++ [x].
Time Proof.
Time (induction n; f_equal /=; auto).
Time Qed.
Time
Lemma replicate_plus n m x :
  replicate (n + m) x = replicate n x ++ replicate m x.
Time Proof.
Time (induction n; f_equal /=; auto).
Time Qed.
Time
Lemma replicate_cons_app n x : x :: replicate n x = replicate n x ++ [x].
Time Proof.
Time (induction n; f_equal /=; eauto).
Time Qed.
Time
Lemma take_replicate n m x : take n (replicate m x) = replicate (min n m) x.
Time Proof.
Time revert m.
Time by induction n; intros [| ?]; f_equal /=.
Time Qed.
Time
Lemma take_replicate_plus n m x :
  take n (replicate (n + m) x) = replicate n x.
Time Proof.
Time by rewrite take_replicate, min_l by lia.
Time Qed.
Time
Lemma drop_replicate n m x : drop n (replicate m x) = replicate (m - n) x.
Time Proof.
Time revert m.
Time by induction n; intros [| ?]; f_equal /=.
Time Qed.
Time
Lemma drop_replicate_plus n m x :
  drop n (replicate (n + m) x) = replicate m x.
Time Proof.
Time (rewrite drop_replicate).
Time f_equal.
Time lia.
Time Qed.
Time
Lemma replicate_as_elem_of x n l :
  replicate n x = l \226\134\148 length l = n \226\136\167 (\226\136\128 y, y \226\136\136 l \226\134\146 y = x).
Time Proof.
Time
(split; [ intros <-; eauto using elem_of_replicate_inv, replicate_length |  ]).
Time (intros [<- Hl]).
Time symmetry.
Time (induction l as [| y l IH]; f_equal /=).
Time -
Time (apply Hl).
Time by left.
Time -
Time (apply IH).
Time (intros ? ?).
Time (apply Hl).
Time by right.
Time Qed.
Time Lemma reverse_replicate n x : reverse (replicate n x) = replicate n x.
Time Proof.
Time symmetry.
Time (apply replicate_as_elem_of).
Time (rewrite reverse_length, replicate_length).
Time (split; auto).
Time (intros y).
Time (rewrite elem_of_reverse).
Time by apply elem_of_replicate_inv.
Time Qed.
Time Lemma replicate_false \206\178s n : length \206\178s = n \226\134\146 replicate n false =.>* \206\178s.
Time Proof.
Time (intros <-).
Time by induction \206\178s; simpl; constructor.
Time Qed.
Time
Lemma resize_spec l n x :
  resize n x l = take n l ++ replicate (n - length l) x.
Time Proof.
Time revert n.
Time (induction l; intros [| ?]; f_equal /=; auto).
Time Qed.
Time Lemma resize_0 l x : resize 0 x l = [].
Time Proof.
Time by destruct l.
Time Qed.
Time Lemma resize_nil n x : resize n x [] = replicate n x.
Time Proof.
Time (rewrite resize_spec).
Time (rewrite take_nil).
Time f_equal /=.
Time lia.
Time Qed.
Time
Lemma resize_ge l n x :
  length l \226\137\164 n \226\134\146 resize n x l = l ++ replicate (n - length l) x.
Time Proof.
Time (intros).
Time by rewrite resize_spec, take_ge.
Time Qed.
Time Lemma resize_le l n x : n \226\137\164 length l \226\134\146 resize n x l = take n l.
Time Proof.
Time (intros).
Time (rewrite resize_spec, (proj2 (Nat.sub_0_le _ _)) by done).
Time (simpl).
Time by rewrite (right_id_L [] (++)).
Time Qed.
Time Lemma resize_all l x : resize (length l) x l = l.
Time Proof.
Time (intros).
Time by rewrite resize_le, take_ge.
Time Qed.
Time Lemma resize_all_alt l n x : n = length l \226\134\146 resize n x l = l.
Time Proof.
Time (intros ->).
Time by rewrite resize_all.
Time Qed.
Time
Lemma resize_plus l n m x :
  resize (n + m) x l = resize n x l ++ resize m x (drop n l).
Time Proof.
Time revert n m.
Time (induction l; intros [| ?] [| ?]; f_equal /=; auto).
Time -
Time by rewrite Nat.add_0_r, (right_id_L [] (++)).
Time -
Time by rewrite replicate_plus.
Time Qed.
Time
Lemma resize_plus_eq l n m x :
  length l = n \226\134\146 resize (n + m) x l = l ++ replicate m x.
Time Proof.
Time (intros <-).
Time by rewrite resize_plus, resize_all, drop_all, resize_nil.
Time Qed.
Time
Lemma resize_app_le l1 l2 n x :
  n \226\137\164 length l1 \226\134\146 resize n x (l1 ++ l2) = resize n x l1.
Time Proof.
Time (intros).
Time by rewrite !resize_le, take_app_le by (rewrite ?app_length; lia).
Time Qed.
Time Lemma resize_app l1 l2 n x : n = length l1 \226\134\146 resize n x (l1 ++ l2) = l1.
Time Proof.
Time (intros ->).
Time by rewrite resize_app_le, resize_all.
Time Qed.
Time
Lemma resize_app_ge l1 l2 n x :
  length l1 \226\137\164 n \226\134\146 resize n x (l1 ++ l2) = l1 ++ resize (n - length l1) x l2.
Time Proof.
Time (intros).
Time (rewrite !resize_spec, take_app_ge, (assoc_L (++)) by done).
Time (do 2 f_equal).
Time (rewrite app_length).
Time lia.
Time Qed.
Time Lemma resize_length l n x : length (resize n x l) = n.
Time Proof.
Time (rewrite resize_spec, app_length, replicate_length, take_length).
Time lia.
Time Qed.
Time
Lemma resize_replicate x n m : resize n x (replicate m x) = replicate n x.
Time Proof.
Time revert m.
Time (induction n; intros [| ?]; f_equal /=; auto).
Time Qed.
Time
Lemma resize_resize l n m x :
  n \226\137\164 m \226\134\146 resize n x (resize m x l) = resize n x l.
Time Proof.
Time revert n m.
Time (induction l; simpl).
Time -
Time (intros).
Time by rewrite !resize_nil, resize_replicate.
Time -
Time (intros [| ?] [| ?] ?; f_equal /=; auto with lia).
Time Qed.
Time Lemma resize_idemp l n x : resize n x (resize n x l) = resize n x l.
Time Proof.
Time by rewrite resize_resize.
Time Qed.
Time
Lemma resize_take_le l n m x : n \226\137\164 m \226\134\146 resize n x (take m l) = resize n x l.
Time Proof.
Time revert n m.
Time (induction l; intros [| ?] [| ?] ?; f_equal /=; auto with lia).
Time Qed.
Time Lemma resize_take_eq l n x : resize n x (take n l) = resize n x l.
Time Proof.
Time by rewrite resize_take_le.
Time Qed.
Time
Lemma take_resize l n m x : take n (resize m x l) = resize (min n m) x l.
Time Proof.
Time revert n m.
Time
(induction l; intros [| ?] [| ?]; f_equal /=; auto using take_replicate).
Time Qed.
Time
Lemma take_resize_le l n m x : n \226\137\164 m \226\134\146 take n (resize m x l) = resize n x l.
Time Proof.
Time (intros).
Time by rewrite take_resize, Min.min_l.
Time Qed.
Time Lemma take_resize_eq l n x : take n (resize n x l) = resize n x l.
Time Proof.
Time (intros).
Time by rewrite take_resize, Min.min_l.
Time Qed.
Time
Lemma take_resize_plus l n m x : take n (resize (n + m) x l) = resize n x l.
Time Proof.
Time by rewrite take_resize, min_l by lia.
Time Qed.
Time
Lemma drop_resize_le l n m x :
  n \226\137\164 m \226\134\146 drop n (resize m x l) = resize (m - n) x (drop n l).
Time Proof.
Time revert n m.
Time (induction l; simpl).
Time -
Time (intros).
Time by rewrite drop_nil, !resize_nil, drop_replicate.
Time -
Time (intros [| ?] [| ?] ?; simpl; try case_match; auto with lia).
Time Qed.
Time
Lemma drop_resize_plus l n m x :
  drop n (resize (n + m) x l) = resize m x (drop n l).
Time Proof.
Time (rewrite drop_resize_le by lia).
Time f_equal.
Time lia.
Time Qed.
Time
Lemma lookup_resize l n x i :
  i < n \226\134\146 i < length l \226\134\146 resize n x l !! i = l !! i.
Time Proof.
Time (intros ? ?).
Time (destruct (decide (n < length l))).
Time -
Time by rewrite resize_le, lookup_take by lia.
Time -
Time by rewrite resize_ge, lookup_app_l by lia.
Time Qed.
Time
Lemma lookup_resize_new l n x i :
  length l \226\137\164 i \226\134\146 i < n \226\134\146 resize n x l !! i = Some x.
Time Proof.
Time (intros ? ?).
Time (rewrite resize_ge by lia).
Time replace i with length l + (i - length l) by lia.
Time by rewrite lookup_app_r, lookup_replicate_2 by lia.
Time Qed.
Time Lemma lookup_resize_old l n x i : n \226\137\164 i \226\134\146 resize n x l !! i = None.
Time Proof.
Time (intros ?).
Time (apply lookup_ge_None_2).
Time by rewrite resize_length.
Time Qed.
Time Lemma reshape_length szs l : length (reshape szs l) = length szs.
Time Proof.
Time revert l.
Time by induction szs; intros; f_equal /=.
Time Qed.
Time
Lemma join_reshape szs l :
  sum_list szs = length l \226\134\146 mjoin (reshape szs l) = l.
Time Proof.
Time revert l.
Time
(induction szs as [| sz szs IH]; simpl; intros l Hl; [ by destruct l |  ]).
Time by rewrite IH, take_drop by (rewrite drop_length; lia).
Time Qed.
Time Lemma sum_list_replicate n m : sum_list (replicate m n) = m * n.
Time Proof.
Time (induction m; simpl; auto).
Time Qed.
Time End general_properties.
Time Section more_general_properties.
Time Context {A : Type}.
Time Implicit Types x y z : A.
Time Implicit Types l k : list A.
Time
Lemma sublist_lookup_length l i n k :
  sublist_lookup i n l = Some k \226\134\146 length k = n.
Time Proof.
Time (unfold sublist_lookup; intros; simplify_option_eq).
Time (rewrite take_length, drop_length; lia).
Time Qed.
Time
Lemma sublist_lookup_all l n : length l = n \226\134\146 sublist_lookup 0 n l = Some l.
Time Proof.
Time (intros).
Time (unfold sublist_lookup; case_option_guard; [  | lia ]).
Time by rewrite take_ge by (rewrite drop_length; lia).
Time Qed.
Time
Lemma sublist_lookup_Some l i n :
  i + n \226\137\164 length l \226\134\146 sublist_lookup i n l = Some (take n (drop i l)).
Time Proof.
Time by unfold sublist_lookup; intros; simplify_option_eq.
Time Qed.
Time
Lemma sublist_lookup_None l i n :
  length l < i + n \226\134\146 sublist_lookup i n l = None.
Time Proof.
Time by unfold sublist_lookup; intros; simplify_option_eq by lia.
Time Qed.
Time
Lemma sublist_eq l k n :
  (n | length l)
  \226\134\146 (n | length k)
    \226\134\146 (\226\136\128 i, sublist_lookup (i * n) n l = sublist_lookup (i * n) n k) \226\134\146 l = k.
Time Proof.
Time revert l k.
Time
(assert
  (\226\136\128 l i,
     n \226\137\160 0 \226\134\146 (n | length l) \226\134\146 \194\172 n * i `div` n + n \226\137\164 length l \226\134\146 length l \226\137\164 i)).
Time {
Time (intros l i ? [j ->] Hjn).
Time (apply Nat.nlt_ge; contradict Hjn).
Time (rewrite <- Nat.mul_succ_r, (Nat.mul_comm n)).
Time (apply Nat.mul_le_mono_r, Nat.le_succ_l, Nat.div_lt_upper_bound; lia).
Time }
Time (intros l k Hl Hk Hlookup).
Time (destruct (decide (n = 0)) as [->| ]).
Time {
Time
by
 rewrite (nil_length_inv l), (nil_length_inv k) by eauto using Nat.divide_0_l.
Time }
Time (apply list_eq; intros i).
Time specialize (Hlookup (i `div` n)).
Time (rewrite (Nat.mul_comm _ n) in Hlookup).
Time
(unfold sublist_lookup in *; simplify_option_eq;
  [  | by rewrite !lookup_ge_None_2 by auto ]).
Time (apply (f_equal (!!i `mod` n)) in Hlookup).
Time
by
 rewrite !lookup_take, !lookup_drop, <- !Nat.div_mod 
  in Hlookup by auto using Nat.mod_upper_bound with lia.
Time Qed.
Time
Lemma sublist_eq_same_length l k j n :
  length l = j * n
  \226\134\146 length k = j * n
    \226\134\146 (\226\136\128 i, i < j \226\134\146 sublist_lookup (i * n) n l = sublist_lookup (i * n) n k)
      \226\134\146 l = k.
Time Proof.
Time (intros Hl Hk ?).
Time (destruct (decide (n = 0)) as [->| ]).
Time {
Time by rewrite (nil_length_inv l), (nil_length_inv k) by lia.
Time }
Time (apply sublist_eq with n; [ by exists j | by exists j |  ]).
Time (intros i).
Time (destruct (decide (i < j)); [ by auto |  ]).
Time (assert (\226\136\128 m, m = j * n \226\134\146 m < i * n + n)).
Time {
Time (intros ? ->).
Time replace (i * n + n) with S i * n by lia.
Time (apply Nat.mul_lt_mono_pos_r; lia).
Time }
Time by rewrite !sublist_lookup_None by auto.
Time Qed.
Time
Lemma sublist_lookup_reshape l i n m :
  0 < n
  \226\134\146 length l = m * n
    \226\134\146 reshape (replicate m n) l !! i = sublist_lookup (i * n) n l.
Time Proof.
Time (intros Hn Hl).
Time (unfold sublist_lookup).
Time (apply option_eq; intros x; split).
Time -
Time (intros Hx).
Time case_option_guard as Hi.
Time {
Time f_equal.
Time clear Hi.
Time revert i l Hl Hx.
Time (induction m as [| m IH]; intros [| i] l ? ?; simplify_eq /=; auto).
Time (rewrite <- drop_drop).
Time (apply IH; rewrite ?drop_length; auto with lia).
Time }
Time (destruct Hi).
Time (rewrite Hl, <- Nat.mul_succ_l).
Time (apply Nat.mul_le_mono_r, Nat.le_succ_l).
Time (apply lookup_lt_Some in Hx).
Time by rewrite reshape_length, replicate_length in Hx.
Time -
Time (intros Hx).
Time (case_option_guard as Hi; simplify_eq /=).
Time revert i l Hl Hi.
Time (induction m as [| m IH]; [ auto with lia |  ]).
Time (intros [| i] l ? ?; simpl; [ done |  ]).
Time (rewrite <- drop_drop).
Time (rewrite IH; rewrite ?drop_length; auto with lia).
Time Qed.
Time
Lemma sublist_lookup_compose l1 l2 l3 i n j m :
  sublist_lookup i n l1 = Some l2
  \226\134\146 sublist_lookup j m l2 = Some l3 \226\134\146 sublist_lookup (i + j) m l1 = Some l3.
Time Proof.
Time
(unfold sublist_lookup; intros; simplify_option_eq;
  repeat
   match goal with
   | H:_ \226\137\164 length _ |- _ => rewrite take_length, drop_length in H
   end;
  rewrite ?take_drop_commute, ?drop_drop, ?take_take, ?Min.min_l,
   Nat.add_assoc by lia; auto with lia).
Time Qed.
Time
Lemma sublist_alter_length f l i n k :
  sublist_lookup i n l = Some k
  \226\134\146 length (f k) = n \226\134\146 length (sublist_alter f i n l) = length l.
Time Proof.
Time (unfold sublist_alter, sublist_lookup).
Time (intros Hk ?; simplify_option_eq).
Time (rewrite !app_length, Hk, !take_length, !drop_length; lia).
Time Qed.
Time
Lemma sublist_lookup_alter f l i n k :
  sublist_lookup i n l = Some k
  \226\134\146 length (f k) = n
    \226\134\146 sublist_lookup i n (sublist_alter f i n l) = f <$> sublist_lookup i n l.
Time Proof.
Time (unfold sublist_lookup).
Time (intros Hk ?).
Time (erewrite sublist_alter_length by eauto).
Time (unfold sublist_alter; simplify_option_eq).
Time
by rewrite Hk, drop_app_alt, take_app_alt by (rewrite ?take_length; lia).
Time Qed.
Time
Lemma sublist_lookup_alter_ne f l i j n k :
  sublist_lookup j n l = Some k
  \226\134\146 length (f k) = n
    \226\134\146 i + n \226\137\164 j \226\136\168 j + n \226\137\164 i
      \226\134\146 sublist_lookup i n (sublist_alter f j n l) = sublist_lookup i n l.
Time Proof.
Time (unfold sublist_lookup).
Time (intros Hk Hi ?).
Time (erewrite sublist_alter_length by eauto).
Time (unfold sublist_alter; simplify_option_eq; f_equal; rewrite Hk).
Time (apply list_eq; intros ii).
Time
(destruct (decide (ii < length (f k)));
  [  | by rewrite !lookup_take_ge by lia ]).
Time (rewrite !lookup_take, !lookup_drop by done).
Time (destruct (decide (i + ii < j))).
Time {
Time by rewrite lookup_app_l, lookup_take by (rewrite ?take_length; lia).
Time }
Time (rewrite lookup_app_r by (rewrite take_length; lia)).
Time (rewrite take_length_le, lookup_app_r, lookup_drop by lia).
Time (f_equal; lia).
Time Qed.
Time
Lemma sublist_alter_all f l n : length l = n \226\134\146 sublist_alter f 0 n l = f l.
Time Proof.
Time (intros <-).
Time (unfold sublist_alter; simpl).
Time by rewrite drop_all, (right_id_L [] (++)), take_ge.
Time Qed.
Time
Lemma sublist_alter_compose f g l i n k :
  sublist_lookup i n l = Some k
  \226\134\146 length (f k) = n
    \226\134\146 length (g k) = n
      \226\134\146 sublist_alter (f \226\136\152 g) i n l =
        sublist_alter f i n (sublist_alter g i n l).
Time Proof.
Time (unfold sublist_alter, sublist_lookup).
Time (intros Hk ? ?; simplify_option_eq).
Time
by
 rewrite !take_app_alt, drop_app_alt, !(assoc_L (++)), drop_app_alt,
  take_app_alt by (rewrite ?app_length, ?take_length, ?Hk; lia).
Time Qed.
Time Lemma imap_nil {B} (f : nat \226\134\146 A \226\134\146 B) : imap f [] = [].
Time Proof.
Time done.
Time Qed.
Time
Lemma imap_app {B} (f : nat \226\134\146 A \226\134\146 B) l1 l2 :
  imap f (l1 ++ l2) = imap f l1 ++ imap (\206\187 n, f (length l1 + n)) l2.
Time Proof.
Time revert f.
Time (induction l1 as [| x l1 IH]; intros f; f_equal /=; auto).
Time by rewrite IH.
Time Qed.
Time
Lemma imap_cons {B} (f : nat \226\134\146 A \226\134\146 B) x l :
  imap f (x :: l) = f 0 x :: imap (f \226\136\152 S) l.
Time Proof.
Time done.
Time Qed.
Time
Lemma imap_ext {B} (f g : nat \226\134\146 A \226\134\146 B) l :
  (\226\136\128 i x, l !! i = Some x \226\134\146 f i x = g i x) \226\134\146 imap f l = imap g l.
Time Proof.
Time (revert f g; induction l as [| x l IH]; intros; f_equal /=; eauto).
Time Qed.
Time
Lemma imap_fmap {B} {C} (f : nat \226\134\146 B \226\134\146 C) (g : A \226\134\146 B) 
  l : imap f (g <$> l) = imap (\206\187 n, f n \226\136\152 g) l.
Time Proof.
Time revert f.
Time (induction l; intros; f_equal /=; eauto).
Time Qed.
Time
Lemma fmap_imap {B} {C} (f : nat \226\134\146 A \226\134\146 B) (g : B \226\134\146 C) 
  l : g <$> imap f l = imap (\206\187 n, g \226\136\152 f n) l.
Time Proof.
Time revert f.
Time (induction l; intros; f_equal /=; eauto).
Time Qed.
Time Lemma imap_const {B} (f : A \226\134\146 B) l : imap (const f) l = f <$> l.
Time Proof.
Time (induction l; f_equal /=; auto).
Time Qed.
Time
Lemma list_lookup_imap {B} (f : nat \226\134\146 A \226\134\146 B) l i :
  imap f l !! i = f i <$> l !! i.
Time Proof.
Time revert f i.
Time (induction l as [| x l IH]; intros f [| i]; f_equal /=; auto).
Time by rewrite IH.
Time Qed.
Time
Lemma imap_length {B} (f : nat \226\134\146 A \226\134\146 B) l : length (imap f l) = length l.
Time Proof.
Time revert f.
Time (induction l; simpl; eauto).
Time Qed.
Time
Lemma elem_of_lookup_imap_1 {B} (f : nat \226\134\146 A \226\134\146 B) 
  l (x : B) : x \226\136\136 imap f l \226\134\146 \226\136\131 i y, x = f i y \226\136\167 l !! i = Some y.
Time Proof.
Time (intros [i Hin]%elem_of_list_lookup).
Time (rewrite list_lookup_imap in Hin).
Time (simplify_option_eq; naive_solver).
Time Qed.
Time
Lemma elem_of_lookup_imap_2 {B} (f : nat \226\134\146 A \226\134\146 B) 
  l x i : l !! i = Some x \226\134\146 f i x \226\136\136 imap f l.
Time Proof.
Time (intros Hl).
Time (rewrite elem_of_list_lookup).
Time exists i.
Time by rewrite list_lookup_imap, Hl.
Time Qed.
Time
Lemma elem_of_lookup_imap {B} (f : nat \226\134\146 A \226\134\146 B) l 
  (x : B) : x \226\136\136 imap f l \226\134\148 (\226\136\131 i y, x = f i y \226\136\167 l !! i = Some y).
Time Proof.
Time naive_solver eauto using elem_of_lookup_imap_1, elem_of_lookup_imap_2.
Time Qed.
Time Lemma mask_nil f \206\178s : mask f \206\178s [] =@{ list A} [].
Time Proof.
Time by destruct \206\178s.
Time Qed.
Time Lemma mask_length f \206\178s l : length (mask f \206\178s l) = length l.
Time Proof.
Time revert \206\178s.
Time (induction l; intros [| ? ?]; f_equal /=; auto).
Time Qed.
Time
Lemma mask_true f l n : length l \226\137\164 n \226\134\146 mask f (replicate n true) l = f <$> l.
Time Proof.
Time revert n.
Time (induction l; intros [| ?] ?; f_equal /=; auto with lia).
Time Qed.
Time Lemma mask_false f l n : mask f (replicate n false) l = l.
Time Proof.
Time revert l.
Time (induction n; intros [| ? ?]; f_equal /=; auto).
Time Qed.
Time
Lemma mask_app f \206\178s1 \206\178s2 l :
  mask f (\206\178s1 ++ \206\178s2) l =
  mask f \206\178s1 (take (length \206\178s1) l) ++ mask f \206\178s2 (drop (length \206\178s1) l).
Time Proof.
Time revert l.
Time (induction \206\178s1; intros [| ? ?]; f_equal /=; auto using mask_nil).
Time Qed.
Time
Lemma mask_app_2 f \206\178s l1 l2 :
  mask f \206\178s (l1 ++ l2) =
  mask f (take (length l1) \206\178s) l1 ++ mask f (drop (length l1) \206\178s) l2.
Time Proof.
Time revert \206\178s.
Time (induction l1; intros [| ? ?]; f_equal /=; auto).
Time Qed.
Time
Lemma take_mask f \206\178s l n :
  take n (mask f \206\178s l) = mask f (take n \206\178s) (take n l).
Time Proof.
Time revert n \206\178s.
Time (induction l; intros [| ?] [| [] ?]; f_equal /=; auto).
Time Qed.
Time
Lemma drop_mask f \206\178s l n :
  drop n (mask f \206\178s l) = mask f (drop n \206\178s) (drop n l).
Time Proof.
Time revert n \206\178s.
Time (induction l; intros [| ?] [| [] ?]; f_equal /=; auto using mask_nil).
Time Qed.
Time
Lemma sublist_lookup_mask f \206\178s l i n :
  sublist_lookup i n (mask f \206\178s l) =
  mask f (take n (drop i \206\178s)) <$> sublist_lookup i n l.
Time Proof.
Time (unfold sublist_lookup; rewrite mask_length; simplify_option_eq; auto).
Time by rewrite drop_mask, take_mask.
Time Qed.
Time
Lemma mask_mask f g \206\178s1 \206\178s2 l :
  (\226\136\128 x, f (g x) = f x)
  \226\134\146 \206\178s1 =.>* \206\178s2 \226\134\146 mask f \206\178s2 (mask g \206\178s1 l) = mask f \206\178s2 l.
Time Proof.
Time (intros ? H\206\178s).
Time revert l.
Time by induction H\206\178s as [| [] []]; intros [| ? ?]; f_equal /=.
Time Qed.
Time
Lemma lookup_mask f \206\178s l i :
  \206\178s !! i = Some true \226\134\146 mask f \206\178s l !! i = f <$> l !! i.
Time Proof.
Time revert i \206\178s.
Time (induction l; intros [] [] ?; simplify_eq /=; f_equal; auto).
Time Qed.
Time
Lemma lookup_mask_notin f \206\178s l i :
  \206\178s !! i \226\137\160 Some true \226\134\146 mask f \206\178s l !! i = l !! i.
Time Proof.
Time revert i \206\178s.
Time (induction l; intros [] [| []] ?; simplify_eq /=; auto).
Time Qed.
Time Lemma fmap_seq j n : S <$> seq j n = seq (S j) n.
Time Proof.
Time revert j.
Time (induction n; intros; f_equal /=; auto).
Time Qed.
Time
Lemma imap_seq {B} l (g : nat \226\134\146 B) i :
  imap (\206\187 j _, g (i + j)) l = g <$> seq i (length l).
Time Proof.
Time revert i.
Time (induction l as [| x l IH]; [ done |  ]).
Time csimpl.
Time (intros n).
Time (rewrite <- IH, <- plus_n_O).
Time f_equal.
Time (apply imap_ext).
Time (intros).
Time (simpl).
Time f_equal.
Time lia.
Time Qed.
Time
Lemma imap_seq_0 {B} l (g : nat \226\134\146 B) :
  imap (\206\187 j _, g j) l = g <$> seq 0 (length l).
Time Proof.
Time (rewrite (imap_ext _ (\206\187 i o, g (0 + i))%nat); [  | done ]).
Time (apply imap_seq).
Time Qed.
Time Lemma lookup_seq j n i : i < n \226\134\146 seq j n !! i = Some (j + i).
Time Proof.
Time revert j i.
Time (induction n as [| n IH]; intros j [| i] ?; simpl; auto with lia).
Time (rewrite IH; auto with lia).
Time Qed.
Time Lemma lookup_seq_ge j n i : n \226\137\164 i \226\134\146 seq j n !! i = None.
Time Proof.
Time revert j i.
Time (induction n; intros j [| i] ?; simpl; auto with lia).
Time Qed.
Time
Lemma lookup_seq_inv j n i j' : seq j n !! i = Some j' \226\134\146 j' = j + i \226\136\167 i < n.
Time Proof.
Time (destruct (le_lt_dec n i); [ by rewrite lookup_seq_ge |  ]).
Time (rewrite lookup_seq by done).
Time intuition congruence.
Time Qed.
Time Lemma NoDup_seq j n : NoDup (seq j n).
Time Proof.
Time (apply NoDup_ListNoDup, seq_NoDup).
Time Qed.
Time Lemma seq_S_end_app j n : seq j (S n) = seq j n ++ [j + n].
Time Proof.
Time revert j.
Time (induction n as [| n IH]; intros j; simpl in *; f_equal; [ done |  ]).
Time (rewrite IH).
Time f_equal.
Time f_equal.
Time lia.
Time Qed.
Time Lemma Permutation_nil l : l \226\137\161\226\130\154 [] \226\134\148 l = [].
Time Proof.
Time split.
Time by intro; apply Permutation_nil.
Time by intros ->.
Time Qed.
Time Lemma Permutation_singleton l x : l \226\137\161\226\130\154 [x] \226\134\148 l = [x].
Time Proof.
Time split.
Time by intro; apply Permutation_length_1_inv.
Time by intros ->.
Time Qed.
Time Definition Permutation_skip := @perm_skip A.
Time Definition Permutation_swap := @perm_swap A.
Time Definition Permutation_singleton_inj := @Permutation_length_1 A.
Time #[global]
Instance Permutation_cons : (Proper ((\226\137\161\226\130\154) ==> (\226\137\161\226\130\154)) (@cons A x)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Existing Instance Permutation_app'.
Time #[global]Instance: (Proper ((\226\137\161\226\130\154) ==> (=)) (@length A)).
Time Proof.
Time (induction 1; simpl; auto with lia).
Time Qed.
Time #[global]Instance: (Comm (\226\137\161\226\130\154) (@app A)).
Time Proof.
Time (intros l1).
Time (induction l1 as [| x l1 IH]; intros l2; simpl).
Time -
Time by rewrite (right_id_L [] (++)).
Time -
Time (rewrite Permutation_middle, IH).
Time (simpl).
Time by rewrite Permutation_middle.
Time Qed.
Time #[global]Instance: (\226\136\128 x : A, Inj (\226\137\161\226\130\154) (\226\137\161\226\130\154) (x::)).
Time Proof.
Time (red).
Time eauto using Permutation_cons_inv.
Time Qed.
Time #[global]Instance: (\226\136\128 k : list A, Inj (\226\137\161\226\130\154) (\226\137\161\226\130\154) (k ++)).
Time Proof.
Time (red).
Time (induction k as [| x k IH]; intros l1 l2; simpl; auto).
Time (intros).
Time by apply IH, (inj (x::)).
Time Qed.
Time #[global]Instance: (\226\136\128 k : list A, Inj (\226\137\161\226\130\154) (\226\137\161\226\130\154) (++k)).
Time Proof.
Time (intros k l1 l2).
Time (rewrite !(comm (++) _ k)).
Time by apply (inj (k ++)).
Time Qed.
Time
Lemma replicate_Permutation n x l : replicate n x \226\137\161\226\130\154 l \226\134\146 replicate n x = l.
Time Proof.
Time (intros Hl).
Time (apply replicate_as_elem_of).
Time split.
Time -
Time by rewrite <- Hl, replicate_length.
Time -
Time (intros y).
Time (rewrite <- Hl).
Time by apply elem_of_replicate_inv.
Time Qed.
Time Lemma reverse_Permutation l : reverse l \226\137\161\226\130\154 l.
Time Proof.
Time (induction l as [| x l IH]; [ done |  ]).
Time by rewrite reverse_cons, (comm (++)), IH.
Time Qed.
Time Lemma delete_Permutation l i x : l !! i = Some x \226\134\146 l \226\137\161\226\130\154 x :: delete i l.
Time Proof.
Time
(revert i; induction l as [| y l IH]; intros [| i] ?; simplify_eq /=; auto).
Time by rewrite Permutation_swap, <- (IH i).
Time Qed.
Time Lemma elem_of_Permutation l x : x \226\136\136 l \226\134\146 \226\136\131 k, l \226\137\161\226\130\154 x :: k.
Time Proof.
Time (intros [i ?]%elem_of_list_lookup).
Time eauto using delete_Permutation.
Time Qed.
Time
Lemma Permutation_cons_inv l k x :
  k \226\137\161\226\130\154 x :: l \226\134\146 \226\136\131 k1 k2, k = k1 ++ x :: k2 \226\136\167 l \226\137\161\226\130\154 k1 ++ k2.
Time Proof.
Time (intros Hk).
Time (assert (\226\136\131 i, k !! i = Some x) as [i Hi]).
Time {
Time (apply elem_of_list_lookup).
Time (rewrite Hk, elem_of_cons; auto).
Time }
Time exists (take i k),(drop (S i) k).
Time split.
Time -
Time by rewrite take_drop_middle.
Time -
Time (rewrite <- delete_take_drop).
Time (apply (inj (x::))).
Time by rewrite <- Hk, <- (delete_Permutation k) by done.
Time Qed.
Time
Lemma length_delete l i :
  is_Some (l !! i) \226\134\146 length (delete i l) = length l - 1.
Time Proof.
Time (rewrite lookup_lt_is_Some).
Time revert i.
Time
(induction l as [| x l IH]; intros [| i] ?; simpl in *; [ lia.. | idtac ]).
Time (rewrite IH by lia).
Time lia.
Time Qed.
Time Lemma lookup_delete_lt l i j : j < i \226\134\146 delete i l !! j = l !! j.
Time Proof.
Time (revert i j; induction l; intros [] []; naive_solver eauto with lia).
Time Qed.
Time Lemma lookup_delete_ge l i j : i \226\137\164 j \226\134\146 delete i l !! j = l !! S j.
Time Proof.
Time (revert i j; induction l; intros [] []; naive_solver eauto with lia).
Time Qed.
Time
Lemma Permutation_inj l1 l2 :
  Permutation l1 l2
  \226\134\148 length l1 = length l2
    \226\136\167 (\226\136\131 f : nat \226\134\146 nat, Inj (=) (=) f \226\136\167 (\226\136\128 i, l1 !! i = l2 !! f i)).
Time Proof.
Time split.
Time -
Time (intros Hl; split; [ by apply Permutation_length |  ]).
Time
(induction Hl
  as [| x l1 l2 _ [f [? ?]]| x y l| l1 l2 l3 _ [f [? Hf]] _ [g [? Hg]]]).
Time +
Time (exists id; split; [ apply _ | done ]).
Time +
Time (exists (\206\187 i, match i with
                   | 0 => 0
                   | S i => S (f i)
                   end); split).
Time *
Time by intros [| i] [| j] ?; simplify_eq /=.
Time *
Time (intros [| i]; simpl; auto).
Time +
Time (exists (\206\187 i, match i with
                   | 0 => 1
                   | 1 => 0
                   | _ => i
                   end); split).
Time *
Time (intros [| [| i]] [| [| j]]; congruence).
Time *
Time by intros [| [| i]].
Time +
Time (exists (g \226\136\152 f); split; [ apply _ |  ]).
Time (intros i; simpl).
Time by rewrite <- Hg, <- Hf.
Time -
Time (intros (Hlen, (f, (Hf, Hl)))).
Time revert l2 f Hlen Hf Hl.
Time
(induction l1 as [| x l1 IH]; intros l2 f Hlen Hf Hl; [ by destruct l2 |  ]).
Time (rewrite (delete_Permutation l2 (f 0) x) by by rewrite <- Hl).
Time
(pose
  (g :=
   fun n => let m := f (S n) in if lt_eq_lt_dec m (f 0) then m else m - 1)).
Time (eapply Permutation_cons, (IH _ g)).
Time +
Time (rewrite length_delete by (rewrite <- Hl; eauto); simpl in *; lia).
Time +
Time (unfold g).
Time (intros i j Hg).
Time
(repeat destruct (lt_eq_lt_dec _ _) as [[?| ?]| ?]; simplify_eq /=; try lia).
Time (apply (inj S), (inj f); lia).
Time +
Time (intros i).
Time (unfold g).
Time (destruct (lt_eq_lt_dec _ _) as [[?| ?]| ?]).
Time *
Time by rewrite lookup_delete_lt, <- Hl.
Time *
Time simplify_eq.
Time *
Time (rewrite lookup_delete_ge, <- Nat.sub_succ_l by lia; simpl).
Time by rewrite Nat.sub_0_r, <- Hl.
Time Qed.
Time Section filter.
Time Context (P : A \226\134\146 Prop) `{\226\136\128 x, Decision (P x)}.
Time #[local]Arguments filter {_} {_} {_} _ {_} !_ /.
Time Lemma filter_nil : filter P [] = [].
Time Proof.
Time done.
Time Qed.
Time
Lemma filter_cons x l :
  filter P (x :: l) = (if decide (P x) then x :: filter P l else filter P l).
Time Proof.
Time done.
Time Qed.
Time Lemma filter_cons_True x l : P x \226\134\146 filter P (x :: l) = x :: filter P l.
Time Proof.
Time (intros).
Time by rewrite filter_cons, decide_True.
Time Qed.
Time Lemma filter_cons_False x l : \194\172 P x \226\134\146 filter P (x :: l) = filter P l.
Time Proof.
Time (intros).
Time by rewrite filter_cons, decide_False.
Time Qed.
Time Lemma elem_of_list_filter l x : x \226\136\136 filter P l \226\134\148 P x \226\136\167 x \226\136\136 l.
Time Proof.
Time
(induction l; simpl; repeat case_decide; rewrite ?elem_of_nil, ?elem_of_cons;
  naive_solver).
Time Qed.
Time Lemma NoDup_filter l : NoDup l \226\134\146 NoDup (filter P l).
Time Proof.
Time
(induction 1; simpl; repeat case_decide;
  rewrite ?NoDup_nil, ?NoDup_cons, ?elem_of_list_filter; tauto).
Time Qed.
Time #[global]
Instance filter_Permutation : (Proper ((\226\137\161\226\130\154) ==> (\226\137\161\226\130\154)) (filter P)).
Time Proof.
Time (induction 1; repeat (simpl; repeat case_decide); by econstructor).
Time Qed.
Time Lemma filter_length l : length (filter P l) \226\137\164 length l.
Time Proof.
Time (induction l; simpl; repeat case_decide; simpl; lia).
Time Qed.
Time
Lemma filter_length_lt l x : x \226\136\136 l \226\134\146 \194\172 P x \226\134\146 length (filter P l) < length l.
Time Proof.
Time (intros [k ->]%elem_of_Permutation ?; simpl).
Time (rewrite decide_False, Nat.lt_succ_r by done).
Time (apply filter_length).
Time Qed.
Time End filter.
Time #[global]Instance: (PreOrder (@prefix A)).
Time Proof.
Time split.
Time -
Time (intros ?).
Time eexists [].
Time by rewrite (right_id_L [] (++)).
Time -
Time (intros ? ? ? [k1 ->] [k2 ->]).
Time exists (k1 ++ k2).
Time by rewrite (assoc_L (++)).
Time Qed.
Time Lemma prefix_nil l : [] `prefix_of` l.
Time Proof.
Time by exists l.
Time Qed.
Time Lemma prefix_nil_not x l : \194\172 x :: l `prefix_of` [].
Time Proof.
Time by intros [k ?].
Time Qed.
Time
Lemma prefix_cons x l1 l2 : l1 `prefix_of` l2 \226\134\146 x :: l1 `prefix_of` x :: l2.
Time Proof.
Time (intros [k ->]).
Time by exists k.
Time Qed.
Time
Lemma prefix_cons_alt x y l1 l2 :
  x = y \226\134\146 l1 `prefix_of` l2 \226\134\146 x :: l1 `prefix_of` y :: l2.
Time Proof.
Time (intros ->).
Time (apply prefix_cons).
Time Qed.
Time Lemma prefix_cons_inv_1 x y l1 l2 : x :: l1 `prefix_of` y :: l2 \226\134\146 x = y.
Time Proof.
Time by intros [k ?]; simplify_eq /=.
Time Qed.
Time
Lemma prefix_cons_inv_2 x y l1 l2 :
  x :: l1 `prefix_of` y :: l2 \226\134\146 l1 `prefix_of` l2.
Time Proof.
Time (intros [k ?]; simplify_eq /=).
Time by exists k.
Time Qed.
Time
Lemma prefix_app k l1 l2 : l1 `prefix_of` l2 \226\134\146 k ++ l1 `prefix_of` k ++ l2.
Time Proof.
Time (intros [k' ->]).
Time exists k'.
Time by rewrite (assoc_L (++)).
Time Qed.
Time
Lemma prefix_app_alt k1 k2 l1 l2 :
  k1 = k2 \226\134\146 l1 `prefix_of` l2 \226\134\146 k1 ++ l1 `prefix_of` k2 ++ l2.
Time Proof.
Time (intros ->).
Time (apply prefix_app).
Time Qed.
Time
Lemma prefix_app_l l1 l2 l3 : l1 ++ l3 `prefix_of` l2 \226\134\146 l1 `prefix_of` l2.
Time Proof.
Time (intros [k ->]).
Time exists (l3 ++ k).
Time by rewrite (assoc_L (++)).
Time Qed.
Time
Lemma prefix_app_r l1 l2 l3 : l1 `prefix_of` l2 \226\134\146 l1 `prefix_of` l2 ++ l3.
Time Proof.
Time (intros [k ->]).
Time exists (k ++ l3).
Time by rewrite (assoc_L (++)).
Time Qed.
Time
Lemma prefix_lookup l1 l2 i x :
  l1 !! i = Some x \226\134\146 l1 `prefix_of` l2 \226\134\146 l2 !! i = Some x.
Time Proof.
Time (intros ? [k ->]).
Time (rewrite lookup_app_l; eauto using lookup_lt_Some).
Time Qed.
Time Lemma prefix_length l1 l2 : l1 `prefix_of` l2 \226\134\146 length l1 \226\137\164 length l2.
Time Proof.
Time (intros [? ->]).
Time (rewrite app_length).
Time lia.
Time Qed.
Time Lemma prefix_snoc_not l x : \194\172 l ++ [x] `prefix_of` l.
Time Proof.
Time (intros [? ?]).
Time discriminate_list.
Time Qed.
Time #[global]Instance: (PreOrder (@suffix A)).
Time Proof.
Time split.
Time -
Time (intros ?).
Time by eexists [].
Time -
Time (intros ? ? ? [k1 ->] [k2 ->]).
Time exists (k2 ++ k1).
Time by rewrite (assoc_L (++)).
Time Qed.
Time #[global]
Instance prefix_dec  `{!EqDecision A}: (RelDecision prefix) :=
 (fix go l1 l2 :=
    match l1, l2 with
    | [], _ => left (prefix_nil _)
    | _, [] => right (prefix_nil_not _ _)
    | x :: l1, y :: l2 =>
        match decide_rel (=) x y with
        | left Hxy =>
            match go l1 l2 with
            | left Hl1l2 => left (prefix_cons_alt _ _ _ _ Hxy Hl1l2)
            | right Hl1l2 => right (Hl1l2 \226\136\152 prefix_cons_inv_2 _ _ _ _)
            end
        | right Hxy => right (Hxy \226\136\152 prefix_cons_inv_1 _ _ _ _)
        end
    end).
Time Section prefix_ops.
Time Context `{!EqDecision A}.
Time
Lemma max_prefix_fst l1 l2 :
  l1 = (max_prefix l1 l2).2 ++ (max_prefix l1 l2).1.1.
Time Proof.
Time revert l2.
Time
(induction l1; intros [| ? ?]; simpl; repeat case_decide; f_equal /=; auto).
Time Qed.
Time
Lemma max_prefix_fst_alt l1 l2 k1 k2 k3 :
  max_prefix l1 l2 = (k1, k2, k3) \226\134\146 l1 = k3 ++ k1.
Time Proof.
Time (intros).
Time (pose proof (max_prefix_fst l1 l2)).
Time by destruct (max_prefix l1 l2) as [[] ?]; simplify_eq.
Time Qed.
Time Lemma max_prefix_fst_prefix l1 l2 : (max_prefix l1 l2).2 `prefix_of` l1.
Time Proof.
Time eexists.
Time (apply max_prefix_fst).
Time Qed.
Time
Lemma max_prefix_fst_prefix_alt l1 l2 k1 k2 k3 :
  max_prefix l1 l2 = (k1, k2, k3) \226\134\146 k3 `prefix_of` l1.
Time Proof.
Time eexists.
Time eauto using max_prefix_fst_alt.
Time Qed.
Time
Lemma max_prefix_snd l1 l2 :
  l2 = (max_prefix l1 l2).2 ++ (max_prefix l1 l2).1.2.
Time Proof.
Time revert l2.
Time
(induction l1; intros [| ? ?]; simpl; repeat case_decide; f_equal /=; auto).
Time Qed.
Time
Lemma max_prefix_snd_alt l1 l2 k1 k2 k3 :
  max_prefix l1 l2 = (k1, k2, k3) \226\134\146 l2 = k3 ++ k2.
Time Proof.
Time intro.
Time (pose proof (max_prefix_snd l1 l2)).
Time by destruct (max_prefix l1 l2) as [[] ?]; simplify_eq.
Time Qed.
Time Lemma max_prefix_snd_prefix l1 l2 : (max_prefix l1 l2).2 `prefix_of` l2.
Time Proof.
Time eexists.
Time (apply max_prefix_snd).
Time Qed.
Time
Lemma max_prefix_snd_prefix_alt l1 l2 k1 k2 k3 :
  max_prefix l1 l2 = (k1, k2, k3) \226\134\146 k3 `prefix_of` l2.
Time Proof.
Time eexists.
Time eauto using max_prefix_snd_alt.
Time Qed.
Time
Lemma max_prefix_max l1 l2 k :
  k `prefix_of` l1 \226\134\146 k `prefix_of` l2 \226\134\146 k `prefix_of` (max_prefix l1 l2).2.
Time Proof.
Time (intros [l1' ->] [l2' ->]).
Time
by
 induction k; simpl; repeat case_decide; simpl; auto
  using prefix_nil, prefix_cons.
Time Qed.
Time
Lemma max_prefix_max_alt l1 l2 k1 k2 k3 k :
  max_prefix l1 l2 = (k1, k2, k3)
  \226\134\146 k `prefix_of` l1 \226\134\146 k `prefix_of` l2 \226\134\146 k `prefix_of` k3.
Time Proof.
Time intro.
Time (pose proof (max_prefix_max l1 l2 k)).
Time by destruct (max_prefix l1 l2) as [[] ?]; simplify_eq.
Time Qed.
Time
Lemma max_prefix_max_snoc l1 l2 k1 k2 k3 x1 x2 :
  max_prefix l1 l2 = (x1 :: k1, x2 :: k2, k3) \226\134\146 x1 \226\137\160 x2.
Time Proof.
Time (intros Hl ->).
Time (destruct (prefix_snoc_not k3 x2)).
Time (eapply max_prefix_max_alt; eauto).
Time -
Time (rewrite (max_prefix_fst_alt _ _ _ _ _ Hl)).
Time (apply prefix_app, prefix_cons, prefix_nil).
Time -
Time (rewrite (max_prefix_snd_alt _ _ _ _ _ Hl)).
Time (apply prefix_app, prefix_cons, prefix_nil).
Time Qed.
Time End prefix_ops.
Time
Lemma prefix_suffix_reverse l1 l2 :
  l1 `prefix_of` l2 \226\134\148 reverse l1 `suffix_of` reverse l2.
Time Proof.
Time (split; intros [k E]; exists (reverse k)).
Time -
Time by rewrite E, reverse_app.
Time -
Time
by rewrite <- (reverse_involutive l2), E, reverse_app, reverse_involutive.
Time Qed.
Time
Lemma suffix_prefix_reverse l1 l2 :
  l1 `suffix_of` l2 \226\134\148 reverse l1 `prefix_of` reverse l2.
Time Proof.
Time by rewrite prefix_suffix_reverse, !reverse_involutive.
Time Qed.
Time Lemma suffix_nil l : [] `suffix_of` l.
Time Proof.
Time exists l.
Time by rewrite (right_id_L [] (++)).
Time Qed.
Time Lemma suffix_nil_inv l : l `suffix_of` [] \226\134\146 l = [].
Time Proof.
Time by intros [[| ?] ?]; simplify_list_eq.
Time Qed.
Time Lemma suffix_cons_nil_inv x l : \194\172 x :: l `suffix_of` [].
Time Proof.
Time by intros [[] ?].
Time Qed.
Time
Lemma suffix_snoc l1 l2 x :
  l1 `suffix_of` l2 \226\134\146 l1 ++ [x] `suffix_of` l2 ++ [x].
Time Proof.
Time (intros [k ->]).
Time exists k.
Time by rewrite (assoc_L (++)).
Time Qed.
Time
Lemma suffix_snoc_alt x y l1 l2 :
  x = y \226\134\146 l1 `suffix_of` l2 \226\134\146 l1 ++ [x] `suffix_of` l2 ++ [y].
Time Proof.
Time (intros ->).
Time (apply suffix_snoc).
Time Qed.
Time
Lemma suffix_app l1 l2 k : l1 `suffix_of` l2 \226\134\146 l1 ++ k `suffix_of` l2 ++ k.
Time Proof.
Time (intros [k' ->]).
Time exists k'.
Time by rewrite (assoc_L (++)).
Time Qed.
Time
Lemma suffix_app_alt l1 l2 k1 k2 :
  k1 = k2 \226\134\146 l1 `suffix_of` l2 \226\134\146 l1 ++ k1 `suffix_of` l2 ++ k2.
Time Proof.
Time (intros ->).
Time (apply suffix_app).
Time Qed.
Time
Lemma suffix_snoc_inv_1 x y l1 l2 : l1 ++ [x] `suffix_of` l2 ++ [y] \226\134\146 x = y.
Time Proof.
Time (intros [k' E]).
Time (rewrite (assoc_L (++)) in E).
Time by simplify_list_eq.
Time Qed.
Time
Lemma suffix_snoc_inv_2 x y l1 l2 :
  l1 ++ [x] `suffix_of` l2 ++ [y] \226\134\146 l1 `suffix_of` l2.
Time Proof.
Time (intros [k' E]).
Time exists k'.
Time (rewrite (assoc_L (++)) in E).
Time by simplify_list_eq.
Time Qed.
Time
Lemma suffix_app_inv l1 l2 k :
  l1 ++ k `suffix_of` l2 ++ k \226\134\146 l1 `suffix_of` l2.
Time Proof.
Time (intros [k' E]).
Time exists k'.
Time (rewrite (assoc_L (++)) in E).
Time by simplify_list_eq.
Time Qed.
Time
Lemma suffix_cons_l l1 l2 x : x :: l1 `suffix_of` l2 \226\134\146 l1 `suffix_of` l2.
Time Proof.
Time (intros [k ->]).
Time exists (k ++ [x]).
Time by rewrite <- (assoc_L (++)).
Time Qed.
Time
Lemma suffix_app_l l1 l2 l3 : l3 ++ l1 `suffix_of` l2 \226\134\146 l1 `suffix_of` l2.
Time Proof.
Time (intros [k ->]).
Time exists (k ++ l3).
Time by rewrite <- (assoc_L (++)).
Time Qed.
Time
Lemma suffix_cons_r l1 l2 x : l1 `suffix_of` l2 \226\134\146 l1 `suffix_of` x :: l2.
Time Proof.
Time (intros [k ->]).
Time by exists (x :: k).
Time Qed.
Time
Lemma suffix_app_r l1 l2 l3 : l1 `suffix_of` l2 \226\134\146 l1 `suffix_of` l3 ++ l2.
Time Proof.
Time (intros [k ->]).
Time exists (l3 ++ k).
Time by rewrite (assoc_L (++)).
Time Qed.
Time
Lemma suffix_cons_inv l1 l2 x y :
  x :: l1 `suffix_of` y :: l2 \226\134\146 x :: l1 = y :: l2 \226\136\168 x :: l1 `suffix_of` l2.
Time Proof.
Time (intros [[| ? k] E]; [ by left |  ]).
Time right.
Time simplify_eq /=.
Time by apply suffix_app_r.
Time Qed.
Time Lemma suffix_length l1 l2 : l1 `suffix_of` l2 \226\134\146 length l1 \226\137\164 length l2.
Time Proof.
Time (intros [? ->]).
Time (rewrite app_length).
Time lia.
Time Qed.
Time Lemma suffix_cons_not x l : \194\172 x :: l `suffix_of` l.
Time Proof.
Time (intros [? ?]).
Time discriminate_list.
Time Qed.
Time #[global]
Instance suffix_dec  `{!EqDecision A}: (RelDecision (@suffix A)).
Time Proof.
Time
(refine (\206\187 l1 l2, cast_if (decide_rel prefix (reverse l1) (reverse l2)));
  abstract by rewrite suffix_prefix_reverse).
Time Defined.
Time Section max_suffix.
Time Context `{!EqDecision A}.
Time
Lemma max_suffix_fst l1 l2 :
  l1 = (max_suffix l1 l2).1.1 ++ (max_suffix l1 l2).2.
Time Proof.
Time (rewrite <- (reverse_involutive l1)  at 1).
Time (rewrite (max_prefix_fst (reverse l1) (reverse l2))).
Time (unfold max_suffix).
Time (destruct (max_prefix (reverse l1) (reverse l2)) as ((?, ?), ?); simpl).
Time by rewrite reverse_app.
Time Qed.
Time
Lemma max_suffix_fst_alt l1 l2 k1 k2 k3 :
  max_suffix l1 l2 = (k1, k2, k3) \226\134\146 l1 = k1 ++ k3.
Time Proof.
Time intro.
Time (pose proof (max_suffix_fst l1 l2)).
Time by destruct (max_suffix l1 l2) as [[] ?]; simplify_eq.
Time Qed.
Time Lemma max_suffix_fst_suffix l1 l2 : (max_suffix l1 l2).2 `suffix_of` l1.
Time Proof.
Time eexists.
Time (apply max_suffix_fst).
Time Qed.
Time
Lemma max_suffix_fst_suffix_alt l1 l2 k1 k2 k3 :
  max_suffix l1 l2 = (k1, k2, k3) \226\134\146 k3 `suffix_of` l1.
Time Proof.
Time eexists.
Time eauto using max_suffix_fst_alt.
Time Qed.
Time
Lemma max_suffix_snd l1 l2 :
  l2 = (max_suffix l1 l2).1.2 ++ (max_suffix l1 l2).2.
Time Proof.
Time (rewrite <- (reverse_involutive l2)  at 1).
Time (rewrite (max_prefix_snd (reverse l1) (reverse l2))).
Time (unfold max_suffix).
Time (destruct (max_prefix (reverse l1) (reverse l2)) as ((?, ?), ?); simpl).
Time by rewrite reverse_app.
Time Qed.
Time
Lemma max_suffix_snd_alt l1 l2 k1 k2 k3 :
  max_suffix l1 l2 = (k1, k2, k3) \226\134\146 l2 = k2 ++ k3.
Time Proof.
Time intro.
Time (pose proof (max_suffix_snd l1 l2)).
Time by destruct (max_suffix l1 l2) as [[] ?]; simplify_eq.
Time Qed.
Time Lemma max_suffix_snd_suffix l1 l2 : (max_suffix l1 l2).2 `suffix_of` l2.
Time Proof.
Time eexists.
Time (apply max_suffix_snd).
Time Qed.
Time
Lemma max_suffix_snd_suffix_alt l1 l2 k1 k2 k3 :
  max_suffix l1 l2 = (k1, k2, k3) \226\134\146 k3 `suffix_of` l2.
Time Proof.
Time eexists.
Time eauto using max_suffix_snd_alt.
Time Qed.
Time
Lemma max_suffix_max l1 l2 k :
  k `suffix_of` l1 \226\134\146 k `suffix_of` l2 \226\134\146 k `suffix_of` (max_suffix l1 l2).2.
Time Proof.
Time (generalize (max_prefix_max (reverse l1) (reverse l2))).
Time (rewrite !suffix_prefix_reverse).
Time (unfold max_suffix).
Time (destruct (max_prefix (reverse l1) (reverse l2)) as ((?, ?), ?); simpl).
Time (rewrite reverse_involutive).
Time auto.
Time Qed.
Time
Lemma max_suffix_max_alt l1 l2 k1 k2 k3 k :
  max_suffix l1 l2 = (k1, k2, k3)
  \226\134\146 k `suffix_of` l1 \226\134\146 k `suffix_of` l2 \226\134\146 k `suffix_of` k3.
Time Proof.
Time intro.
Time (pose proof (max_suffix_max l1 l2 k)).
Time by destruct (max_suffix l1 l2) as [[] ?]; simplify_eq.
Time Qed.
Time
Lemma max_suffix_max_snoc l1 l2 k1 k2 k3 x1 x2 :
  max_suffix l1 l2 = (k1 ++ [x1], k2 ++ [x2], k3) \226\134\146 x1 \226\137\160 x2.
Time Proof.
Time (intros Hl ->).
Time (destruct (suffix_cons_not x2 k3)).
Time (eapply max_suffix_max_alt; eauto).
Time -
Time (rewrite (max_suffix_fst_alt _ _ _ _ _ Hl)).
Time by apply (suffix_app [x2]), suffix_app_r.
Time -
Time (rewrite (max_suffix_snd_alt _ _ _ _ _ Hl)).
Time by apply (suffix_app [x2]), suffix_app_r.
Time Qed.
Time End max_suffix.
Time Lemma sublist_length l1 l2 : l1 `sublist_of` l2 \226\134\146 length l1 \226\137\164 length l2.
Time Proof.
Time (induction 1; simpl; auto with arith).
Time Qed.
Time Lemma sublist_nil_l l : [] `sublist_of` l.
Time Proof.
Time (induction l; try constructor; auto).
Time Qed.
Time Lemma sublist_nil_r l : l `sublist_of` [] \226\134\148 l = [].
Time Proof.
Time split.
Time by inversion 1.
Time (intros ->).
Time constructor.
Time Qed.
Time
Lemma sublist_app l1 l2 k1 k2 :
  l1 `sublist_of` l2 \226\134\146 k1 `sublist_of` k2 \226\134\146 l1 ++ k1 `sublist_of` l2 ++ k2.
Time Proof.
Time (induction 1; simpl; try constructor; auto).
Time Qed.
Time
Lemma sublist_inserts_l k l1 l2 :
  l1 `sublist_of` l2 \226\134\146 l1 `sublist_of` k ++ l2.
Time Proof.
Time (induction k; try constructor; auto).
Time Qed.
Time
Lemma sublist_inserts_r k l1 l2 :
  l1 `sublist_of` l2 \226\134\146 l1 `sublist_of` l2 ++ k.
Time Proof.
Time (induction 1; simpl; try constructor; auto using sublist_nil_l).
Time Qed.
Time
Lemma sublist_cons_r x l k :
  l `sublist_of` x :: k
  \226\134\148 l `sublist_of` k \226\136\168 (\226\136\131 l', l = x :: l' \226\136\167 l' `sublist_of` k).
Time Proof.
Time split.
Time (inversion 1; eauto).
Time (intros [?| (?, (->, ?))]; constructor; auto).
Time Qed.
Time
Lemma sublist_cons_l x l k :
  x :: l `sublist_of` k \226\134\148 (\226\136\131 k1 k2, k = k1 ++ x :: k2 \226\136\167 l `sublist_of` k2).
Time Proof.
Time split.
Time -
Time (intros Hlk).
Time (induction k as [| y k IH]; inversion Hlk).
Time +
Time eexists [],k.
Time by repeat constructor.
Time +
Time (destruct IH as (k1, (k2, (->, ?))); auto).
Time by exists (y :: k1),k2.
Time -
Time (intros (k1, (k2, (->, ?)))).
Time by apply sublist_inserts_l, sublist_skip.
Time Qed.
Time
Lemma sublist_app_r l k1 k2 :
  l `sublist_of` k1 ++ k2
  \226\134\148 (\226\136\131 l1 l2, l = l1 ++ l2 \226\136\167 l1 `sublist_of` k1 \226\136\167 l2 `sublist_of` k2).
Time Proof.
Time split.
Time -
Time revert l k2.
Time (induction k1 as [| y k1 IH]; intros l k2; simpl).
Time {
Time eexists [],l.
Time by repeat constructor.
Time }
Time (rewrite sublist_cons_r).
Time (intros [?| (l', (?, ?))]; subst).
Time +
Time (destruct (IH l k2) as (l1, (l2, (?, (?, ?)))); trivial; subst).
Time exists l1,l2.
Time auto using sublist_cons.
Time +
Time (destruct (IH l' k2) as (l1, (l2, (?, (?, ?)))); trivial; subst).
Time exists (y :: l1),l2.
Time auto using sublist_skip.
Time -
Time (intros (?, (?, (?, (?, ?)))); subst).
Time auto using sublist_app.
Time Qed.
Time
Lemma sublist_app_l l1 l2 k :
  l1 ++ l2 `sublist_of` k
  \226\134\148 (\226\136\131 k1 k2, k = k1 ++ k2 \226\136\167 l1 `sublist_of` k1 \226\136\167 l2 `sublist_of` k2).
Time Proof.
Time split.
Time -
Time revert l2 k.
Time (induction l1 as [| x l1 IH]; intros l2 k; simpl).
Time {
Time eexists [],k.
Time by repeat constructor.
Time }
Time (rewrite sublist_cons_l).
Time (intros (k1, (k2, (?, ?))); subst).
Time (destruct (IH l2 k2) as (h1, (h2, (?, (?, ?)))); trivial; subst).
Time exists (k1 ++ x :: h1),h2.
Time (rewrite <- (assoc_L (++))).
Time auto using sublist_inserts_l, sublist_skip.
Time -
Time (intros (?, (?, (?, (?, ?)))); subst).
Time auto using sublist_app.
Time Qed.
Time
Lemma sublist_app_inv_l k l1 l2 :
  k ++ l1 `sublist_of` k ++ l2 \226\134\146 l1 `sublist_of` l2.
Time Proof.
Time (induction k as [| y k IH]; simpl; [ done |  ]).
Time (rewrite sublist_cons_r).
Time (intros [Hl12| (?, (?, ?))]; [  | simplify_eq; eauto ]).
Time (rewrite sublist_cons_l in Hl12).
Time (destruct Hl12 as (k1, (k2, (Hk, ?)))).
Time (apply IH).
Time (rewrite Hk).
Time eauto using sublist_inserts_l, sublist_cons.
Time Qed.
Time
Lemma sublist_app_inv_r k l1 l2 :
  l1 ++ k `sublist_of` l2 ++ k \226\134\146 l1 `sublist_of` l2.
Time Proof.
Time revert l1 l2.
Time (induction k as [| y k IH]; intros l1 l2).
Time {
Time by rewrite !(right_id_L [] (++)).
Time }
Time (intros).
Time feed pose proof IH (l1 ++ [y]) (l2 ++ [y]) as Hl12.
Time {
Time by rewrite <- !(assoc_L (++)).
Time }
Time (rewrite sublist_app_l in Hl12).
Time (destruct Hl12 as (k1, (k2, (E, (?, Hk2))))).
Time (destruct k2 as [| z k2] using rev_ind; [ inversion Hk2 |  ]).
Time (rewrite (assoc_L (++)) in E; simplify_list_eq).
Time eauto using sublist_inserts_r.
Time Qed.
Time #[global]Instance: (PartialOrder (@sublist A)).
Time Proof.
Time (split; [ split |  ]).
Time -
Time (intros l).
Time (induction l; constructor; auto).
Time -
Time (intros l1 l2 l3 Hl12).
Time revert l3.
Time (induction Hl12).
Time +
Time auto using sublist_nil_l.
Time +
Time (intros ?).
Time (rewrite sublist_cons_l).
Time (intros (?, (?, (?, ?))); subst).
Time eauto using sublist_inserts_l, sublist_skip.
Time +
Time (intros ?).
Time (rewrite sublist_cons_l).
Time (intros (?, (?, (?, ?))); subst).
Time eauto using sublist_inserts_l, sublist_cons.
Time -
Time (intros l1 l2 Hl12 Hl21).
Time (apply sublist_length in Hl21).
Time (induction Hl12; f_equal /=; auto with arith).
Time (apply sublist_length in Hl12).
Time lia.
Time Qed.
Time Lemma sublist_take l i : take i l `sublist_of` l.
Time Proof.
Time (rewrite <- (take_drop i l)  at 2).
Time by apply sublist_inserts_r.
Time Qed.
Time Lemma sublist_drop l i : drop i l `sublist_of` l.
Time Proof.
Time (rewrite <- (take_drop i l)  at 2).
Time by apply sublist_inserts_l.
Time Qed.
Time Lemma sublist_delete l i : delete i l `sublist_of` l.
Time Proof.
Time revert i.
Time by induction l; intros [| ?]; simpl; constructor.
Time Qed.
Time Lemma sublist_foldr_delete l is : foldr delete l is `sublist_of` l.
Time Proof.
Time (induction is as [| i is IH]; simpl; [ done |  ]).
Time (trans foldr delete l is; auto using sublist_delete).
Time Qed.
Time
Lemma sublist_alt l1 l2 :
  l1 `sublist_of` l2 \226\134\148 (\226\136\131 is, l1 = foldr delete l2 is).
Time Proof.
Time (split; [  | intros [is ->]; apply sublist_foldr_delete ]).
Time (intros Hl12).
Time (cut (\226\136\128 k, \226\136\131 is, k ++ l1 = foldr delete (k ++ l2) is)).
Time {
Time (intros help).
Time (apply (help [])).
Time }
Time (induction Hl12 as [| x l1 l2 _ IH| x l1 l2 _ IH]; intros k).
Time -
Time by eexists [].
Time -
Time (destruct (IH (k ++ [x])) as [is His]).
Time exists is.
Time by rewrite <- !(assoc_L (++)) in His.
Time -
Time (destruct (IH k) as [is His]).
Time exists (is ++ [length k]).
Time (rewrite fold_right_app).
Time (simpl).
Time by rewrite delete_middle.
Time Qed.
Time
Lemma Permutation_sublist l1 l2 l3 :
  l1 \226\137\161\226\130\154 l2 \226\134\146 l2 `sublist_of` l3 \226\134\146 \226\136\131 l4, l1 `sublist_of` l4 \226\136\167 l4 \226\137\161\226\130\154 l3.
Time Proof.
Time (intros Hl1l2).
Time revert l3.
Time (induction Hl1l2 as [| x l1 l2 ? IH| x y l1| l1 l1' l2 ? IH1 ? IH2]).
Time -
Time (intros l3).
Time by exists l3.
Time -
Time (intros l3).
Time (rewrite sublist_cons_l).
Time (intros (l3', (l3'', (?, ?))); subst).
Time (destruct (IH l3'') as (l4, (?, Hl4)); auto).
Time exists (l3' ++ x :: l4).
Time split.
Time by apply sublist_inserts_l, sublist_skip.
Time by rewrite Hl4.
Time -
Time (intros l3).
Time (rewrite sublist_cons_l).
Time (intros (l3', (l3'', (?, Hl3))); subst).
Time (rewrite sublist_cons_l in Hl3).
Time (destruct Hl3 as (l5', (l5'', (?, Hl5))); subst).
Time exists (l3' ++ y :: l5' ++ x :: l5'').
Time split.
Time +
Time by do 2 apply sublist_inserts_l, sublist_skip.
Time +
Time by rewrite !Permutation_middle, Permutation_swap.
Time -
Time (intros l3 ?).
Time (destruct (IH2 l3) as (l3', (?, ?)); trivial).
Time (destruct (IH1 l3') as (l3'', (?, ?)); trivial).
Time exists l3''.
Time split.
Time done.
Time (etrans; eauto).
Time Qed.
Time
Lemma sublist_Permutation l1 l2 l3 :
  l1 `sublist_of` l2 \226\134\146 l2 \226\137\161\226\130\154 l3 \226\134\146 \226\136\131 l4, l1 \226\137\161\226\130\154 l4 \226\136\167 l4 `sublist_of` l3.
Time Proof.
Time (intros Hl1l2 Hl2l3).
Time revert l1 Hl1l2.
Time (induction Hl2l3 as [| x l2 l3 ? IH| x y l2| l2 l2' l3 ? IH1 ? IH2]).
Time -
Time (intros l1).
Time by exists l1.
Time -
Time (intros l1).
Time (rewrite sublist_cons_r).
Time (intros [?| (l1', (l1'', ?))]; subst).
Time {
Time (destruct (IH l1) as (l4, (?, ?)); trivial).
Time exists l4.
Time split.
Time done.
Time by constructor.
Time }
Time (destruct (IH l1') as (l4, (?, Hl4)); auto).
Time exists (x :: l4).
Time split.
Time by constructor.
Time by constructor.
Time -
Time (intros l1).
Time (rewrite sublist_cons_r).
Time (intros [Hl1| (l1', (l1'', Hl1))]; subst).
Time {
Time exists l1.
Time (split; [ done |  ]).
Time (rewrite sublist_cons_r in Hl1).
Time (destruct Hl1 as [?| (l1', (?, ?))]; subst; by repeat constructor).
Time }
Time (rewrite sublist_cons_r in Hl1).
Time (destruct Hl1 as [?| (l1'', (?, ?))]; subst).
Time +
Time exists (y :: l1').
Time by repeat constructor.
Time +
Time exists (x :: y :: l1'').
Time by repeat constructor.
Time -
Time (intros l1 ?).
Time (destruct (IH1 l1) as (l3', (?, ?)); trivial).
Time (destruct (IH2 l3') as (l3'', (?, ?)); trivial).
Time exists l3''.
Time (split; [  | done ]).
Time (etrans; eauto).
Time Qed.
Time Lemma submseteq_length l1 l2 : l1 \226\138\134+ l2 \226\134\146 length l1 \226\137\164 length l2.
Time Proof.
Time (induction 1; simpl; auto with lia).
Time Qed.
Time Lemma submseteq_nil_l l : [] \226\138\134+ l.
Time Proof.
Time (induction l; constructor; auto).
Time Qed.
Time Lemma submseteq_nil_r l : l \226\138\134+ [] \226\134\148 l = [].
Time Proof.
Time (split; [  | intros ->; constructor ]).
Time (intros Hl).
Time (apply submseteq_length in Hl).
Time (destruct l; simpl in *; auto with lia).
Time Qed.
Time #[global]Instance: (PreOrder (@submseteq A)).
Time Proof.
Time split.
Time -
Time (intros l).
Time (induction l; constructor; auto).
Time -
Time (red).
Time (apply submseteq_trans).
Time Qed.
Time Lemma Permutation_submseteq l1 l2 : l1 \226\137\161\226\130\154 l2 \226\134\146 l1 \226\138\134+ l2.
Time Proof.
Time (induction 1; econstructor; eauto).
Time Qed.
Time Lemma sublist_submseteq l1 l2 : l1 `sublist_of` l2 \226\134\146 l1 \226\138\134+ l2.
Time Proof.
Time (induction 1; constructor; auto).
Time Qed.
Time Lemma submseteq_Permutation l1 l2 : l1 \226\138\134+ l2 \226\134\146 \226\136\131 k, l2 \226\137\161\226\130\154 l1 ++ k.
Time Proof.
Time
(induction 1
  as [| x y l ? [k Hk]| | x l1 l2 ? [k Hk]| l1 l2 l3 ? [k Hk] ? [k' Hk']]).
Time -
Time by eexists [].
Time -
Time exists k.
Time by rewrite Hk.
Time -
Time eexists [].
Time (rewrite (right_id_L [] (++))).
Time by constructor.
Time -
Time exists (x :: k).
Time by rewrite Hk, Permutation_middle.
Time -
Time exists (k ++ k').
Time by rewrite Hk', Hk, (assoc_L (++)).
Time Qed.
Time
Lemma submseteq_Permutation_length_le l1 l2 :
  length l2 \226\137\164 length l1 \226\134\146 l1 \226\138\134+ l2 \226\134\146 l1 \226\137\161\226\130\154 l2.
Time Proof.
Time (intros Hl21 Hl12).
Time (destruct (submseteq_Permutation l1 l2) as [[| ? ?] Hk]; auto).
Time -
Time by rewrite Hk, (right_id_L [] (++)).
Time -
Time (rewrite Hk, app_length in Hl21; simpl in Hl21; lia).
Time Qed.
Time
Lemma submseteq_Permutation_length_eq l1 l2 :
  length l2 = length l1 \226\134\146 l1 \226\138\134+ l2 \226\134\146 l1 \226\137\161\226\130\154 l2.
Time Proof.
Time intro.
Time (apply submseteq_Permutation_length_le).
Time lia.
Time Qed.
Time #[global]Instance: (Proper ((\226\137\161\226\130\154) ==> (\226\137\161\226\130\154) ==> iff) (@submseteq A)).
Time Proof.
Time (intros l1 l2 ? k1 k2 ?).
Time (split; intros).
Time -
Time trans l1.
Time by apply Permutation_submseteq.
Time trans k1.
Time done.
Time by apply Permutation_submseteq.
Time -
Time trans l2.
Time by apply Permutation_submseteq.
Time trans k2.
Time done.
Time by apply Permutation_submseteq.
Time Qed.
Time #[global]Instance: (AntiSymm (\226\137\161\226\130\154) (@submseteq A)).
Time Proof.
Time (red).
Time auto using submseteq_Permutation_length_le, submseteq_length.
Time Qed.
Time Lemma elem_of_submseteq l k x : x \226\136\136 l \226\134\146 l \226\138\134+ k \226\134\146 x \226\136\136 k.
Time Proof.
Time (intros ? [l' ->]%submseteq_Permutation).
Time (apply elem_of_app; auto).
Time Qed.
Time Lemma submseteq_take l i : take i l \226\138\134+ l.
Time Proof.
Time auto using sublist_take, sublist_submseteq.
Time Qed.
Time Lemma submseteq_drop l i : drop i l \226\138\134+ l.
Time Proof.
Time auto using sublist_drop, sublist_submseteq.
Time Qed.
Time Lemma submseteq_delete l i : delete i l \226\138\134+ l.
Time Proof.
Time auto using sublist_delete, sublist_submseteq.
Time Qed.
Time Lemma submseteq_foldr_delete l is : foldr delete l is `sublist_of` l.
Time Proof.
Time auto using sublist_foldr_delete, sublist_submseteq.
Time Qed.
Time
Lemma submseteq_sublist_l l1 l3 :
  l1 \226\138\134+ l3 \226\134\148 (\226\136\131 l2, l1 `sublist_of` l2 \226\136\167 l2 \226\137\161\226\130\154 l3).
Time Proof.
Time split.
Time {
Time (intros Hl13).
Time (elim Hl13; clear l1 l3 Hl13).
Time -
Time by eexists [].
Time -
Time (intros x l1 l3 ? (l2, (?, ?))).
Time exists (x :: l2).
Time by repeat constructor.
Time -
Time (intros x y l).
Time exists (y :: x :: l).
Time by repeat constructor.
Time -
Time (intros x l1 l3 ? (l2, (?, ?))).
Time exists (x :: l2).
Time by repeat constructor.
Time -
Time (intros l1 l3 l5 ? (l2, (?, ?)) ? (l4, (?, ?))).
Time (destruct (Permutation_sublist l2 l3 l4) as (l3', (?, ?)); trivial).
Time exists l3'.
Time (split; etrans; eauto).
Time }
Time (intros (l2, (?, ?))).
Time (trans l2; auto using sublist_submseteq, Permutation_submseteq).
Time Qed.
Time
Lemma submseteq_sublist_r l1 l3 :
  l1 \226\138\134+ l3 \226\134\148 (\226\136\131 l2, l1 \226\137\161\226\130\154 l2 \226\136\167 l2 `sublist_of` l3).
Time Proof.
Time (rewrite submseteq_sublist_l).
Time
(split; intros (l2, (?, ?)); eauto
  using sublist_Permutation, Permutation_sublist).
Time Qed.
Time Lemma submseteq_inserts_l k l1 l2 : l1 \226\138\134+ l2 \226\134\146 l1 \226\138\134+ k ++ l2.
Time Proof.
Time (induction k; try constructor; auto).
Time Qed.
Time Lemma submseteq_inserts_r k l1 l2 : l1 \226\138\134+ l2 \226\134\146 l1 \226\138\134+ l2 ++ k.
Time Proof.
Time (rewrite (comm (++))).
Time (apply submseteq_inserts_l).
Time Qed.
Time Lemma submseteq_skips_l k l1 l2 : l1 \226\138\134+ l2 \226\134\146 k ++ l1 \226\138\134+ k ++ l2.
Time Proof.
Time (induction k; try constructor; auto).
Time Qed.
Time Lemma submseteq_skips_r k l1 l2 : l1 \226\138\134+ l2 \226\134\146 l1 ++ k \226\138\134+ l2 ++ k.
Time Proof.
Time (rewrite !(comm (++) _ k)).
Time (apply submseteq_skips_l).
Time Qed.
Time
Lemma submseteq_app l1 l2 k1 k2 : l1 \226\138\134+ l2 \226\134\146 k1 \226\138\134+ k2 \226\134\146 l1 ++ k1 \226\138\134+ l2 ++ k2.
Time Proof.
Time (trans l1 ++ k2; auto using submseteq_skips_l, submseteq_skips_r).
Time Qed.
Time
Lemma submseteq_cons_r x l k :
  l \226\138\134+ x :: k \226\134\148 l \226\138\134+ k \226\136\168 (\226\136\131 l', l \226\137\161\226\130\154 x :: l' \226\136\167 l' \226\138\134+ k).
Time Proof.
Time split.
Time -
Time (rewrite submseteq_sublist_r).
Time (intros (l', (E, Hl'))).
Time (rewrite sublist_cons_r in Hl').
Time (destruct Hl' as [?| (?, (?, ?))]; subst).
Time +
Time left.
Time (rewrite E).
Time eauto using sublist_submseteq.
Time +
Time right.
Time eauto using sublist_submseteq.
Time -
Time (intros [?| (?, (E, ?))]; [  | rewrite E ]; by constructor).
Time Qed.
Time
Lemma submseteq_cons_l x l k : x :: l \226\138\134+ k \226\134\148 (\226\136\131 k', k \226\137\161\226\130\154 x :: k' \226\136\167 l \226\138\134+ k').
Time Proof.
Time split.
Time -
Time (rewrite submseteq_sublist_l).
Time (intros (l', (Hl', E))).
Time (rewrite sublist_cons_l in Hl').
Time (destruct Hl' as (k1, (k2, (?, ?))); subst).
Time exists (k1 ++ k2).
Time (split; eauto using submseteq_inserts_l, sublist_submseteq).
Time by rewrite Permutation_middle.
Time -
Time (intros (?, (E, ?))).
Time (rewrite E).
Time by constructor.
Time Qed.
Time
Lemma submseteq_app_r l k1 k2 :
  l \226\138\134+ k1 ++ k2 \226\134\148 (\226\136\131 l1 l2, l \226\137\161\226\130\154 l1 ++ l2 \226\136\167 l1 \226\138\134+ k1 \226\136\167 l2 \226\138\134+ k2).
Time Proof.
Time split.
Time -
Time (rewrite submseteq_sublist_r).
Time (intros (l', (E, Hl'))).
Time (rewrite sublist_app_r in Hl').
Time (destruct Hl' as (l1, (l2, (?, (?, ?)))); subst).
Time exists l1,l2.
Time eauto using sublist_submseteq.
Time -
Time (intros (?, (?, (E, (?, ?))))).
Time (rewrite E).
Time eauto using submseteq_app.
Time Qed.
Time
Lemma submseteq_app_l l1 l2 k :
  l1 ++ l2 \226\138\134+ k \226\134\148 (\226\136\131 k1 k2, k \226\137\161\226\130\154 k1 ++ k2 \226\136\167 l1 \226\138\134+ k1 \226\136\167 l2 \226\138\134+ k2).
Time Proof.
Time split.
Time -
Time (rewrite submseteq_sublist_l).
Time (intros (l', (Hl', E))).
Time (rewrite sublist_app_l in Hl').
Time (destruct Hl' as (k1, (k2, (?, (?, ?)))); subst).
Time exists k1,k2.
Time split.
Time done.
Time eauto using sublist_submseteq.
Time -
Time (intros (?, (?, (E, (?, ?))))).
Time (rewrite E).
Time eauto using submseteq_app.
Time Qed.
Time Lemma submseteq_app_inv_l l1 l2 k : k ++ l1 \226\138\134+ k ++ l2 \226\134\146 l1 \226\138\134+ l2.
Time Proof.
Time (induction k as [| y k IH]; simpl; [ done |  ]).
Time (rewrite submseteq_cons_l).
Time (intros (?, (E%(inj _), ?))).
Time (apply IH).
Time by rewrite E.
Time Qed.
Time Lemma submseteq_app_inv_r l1 l2 k : l1 ++ k \226\138\134+ l2 ++ k \226\134\146 l1 \226\138\134+ l2.
Time Proof.
Time revert l1 l2.
Time (induction k as [| y k IH]; intros l1 l2).
Time {
Time by rewrite !(right_id_L [] (++)).
Time }
Time (intros).
Time feed pose proof IH (l1 ++ [y]) (l2 ++ [y]) as Hl12.
Time {
Time by rewrite <- !(assoc_L (++)).
Time }
Time (rewrite submseteq_app_l in Hl12).
Time (destruct Hl12 as (k1, (k2, (E1, (?, Hk2))))).
Time (rewrite submseteq_cons_l in Hk2).
Time (destruct Hk2 as (k2', (E2, ?))).
Time (rewrite E2, (Permutation_cons_append k2'), (assoc_L (++)) in E1).
Time (apply Permutation_app_inv_r in E1).
Time (rewrite E1).
Time eauto using submseteq_inserts_r.
Time Qed.
Time
Lemma submseteq_cons_middle x l k1 k2 :
  l \226\138\134+ k1 ++ k2 \226\134\146 x :: l \226\138\134+ k1 ++ x :: k2.
Time Proof.
Time (rewrite <- Permutation_middle).
Time by apply submseteq_skip.
Time Qed.
Time
Lemma submseteq_app_middle l1 l2 k1 k2 :
  l2 \226\138\134+ k1 ++ k2 \226\134\146 l1 ++ l2 \226\138\134+ k1 ++ l1 ++ k2.
Time Proof.
Time (rewrite !(assoc (++)), (comm (++) k1 l1), <- (assoc_L (++))).
Time by apply submseteq_skips_l.
Time Qed.
Time Lemma submseteq_middle l k1 k2 : l \226\138\134+ k1 ++ l ++ k2.
Time Proof.
Time by apply submseteq_inserts_l, submseteq_inserts_r.
Time Qed.
Time
Lemma Permutation_alt l1 l2 : l1 \226\137\161\226\130\154 l2 \226\134\148 length l1 = length l2 \226\136\167 l1 \226\138\134+ l2.
Time Proof.
Time split.
Time -
Time by intros Hl; rewrite Hl.
Time -
Time (intros [? ?]; auto using submseteq_Permutation_length_eq).
Time Qed.
Time Lemma NoDup_submseteq l k : NoDup l \226\134\146 (\226\136\128 x, x \226\136\136 l \226\134\146 x \226\136\136 k) \226\134\146 l \226\138\134+ k.
Time Proof.
Time (intros Hl).
Time revert k.
Time (induction Hl as [| x l Hx ? IH]).
Time {
Time (intros k Hk).
Time by apply submseteq_nil_l.
Time }
Time (intros k Hlk).
Time (destruct (elem_of_list_split k x) as (l1, (l2, ?)); subst).
Time {
Time (apply Hlk).
Time by constructor.
Time }
Time (rewrite <- Permutation_middle).
Time (apply submseteq_skip, IH).
Time (intros y Hy).
Time (rewrite elem_of_app).
Time specialize (Hlk y).
Time (rewrite elem_of_app, !elem_of_cons in Hlk).
Time by destruct Hlk as [?| [?| ?]]; subst; eauto.
Time Qed.
Time
Lemma NoDup_Permutation l k :
  NoDup l \226\134\146 NoDup k \226\134\146 (\226\136\128 x, x \226\136\136 l \226\134\148 x \226\136\136 k) \226\134\146 l \226\137\161\226\130\154 k.
Time Proof.
Time (intros).
Time (apply (anti_symm submseteq); apply NoDup_submseteq; naive_solver).
Time Qed.
Time Section submseteq_dec.
Time Context `{!EqDecision A}.
Time
Lemma list_remove_Permutation l1 l2 k1 x :
  l1 \226\137\161\226\130\154 l2
  \226\134\146 list_remove x l1 = Some k1 \226\134\146 \226\136\131 k2, list_remove x l2 = Some k2 \226\136\167 k1 \226\137\161\226\130\154 k2.
Time Proof.
Time (intros Hl).
Time revert k1.
Time
(induction Hl as [| y l1 l2 ? IH| y1 y2 l| l1 l2 l3 ? IH1 ? IH2]; simpl;
  intros k1 Hk1).
Time -
Time done.
Time -
Time (case_decide; simplify_eq; eauto).
Time (destruct (list_remove x l1) as [l| ] eqn:?; simplify_eq).
Time (destruct (IH l) as (?, (?, ?)); simplify_option_eq; eauto).
Time -
Time (simplify_option_eq; eauto using Permutation_swap).
Time -
Time (destruct (IH1 k1) as (k2, (?, ?)); trivial).
Time (destruct (IH2 k2) as (k3, (?, ?)); trivial).
Time exists k3.
Time (split; eauto).
Time by trans k2.
Time Qed.
Time Lemma list_remove_Some l k x : list_remove x l = Some k \226\134\146 l \226\137\161\226\130\154 x :: k.
Time Proof.
Time revert k.
Time (induction l as [| y l IH]; simpl; intros k ?; [ done |  ]).
Time (simplify_option_eq; auto).
Time by rewrite Permutation_swap, <- IH.
Time Qed.
Time
Lemma list_remove_Some_inv l k x :
  l \226\137\161\226\130\154 x :: k \226\134\146 \226\136\131 k', list_remove x l = Some k' \226\136\167 k \226\137\161\226\130\154 k'.
Time Proof.
Time (intros).
Time (destruct (list_remove_Permutation (x :: k) l k x) as (k', (?, ?))).
Time -
Time done.
Time -
Time (simpl; by case_decide).
Time -
Time by exists k'.
Time Qed.
Time
Lemma list_remove_list_submseteq l1 l2 :
  l1 \226\138\134+ l2 \226\134\148 is_Some (list_remove_list l1 l2).
Time Proof.
Time split.
Time -
Time revert l2.
Time (induction l1 as [| x l1 IH]; simpl).
Time {
Time (intros l2 _).
Time by exists l2.
Time }
Time (intros l2).
Time (rewrite submseteq_cons_l).
Time (intros (k, (Hk, ?))).
Time (destruct (list_remove_Some_inv l2 k x) as (k2, (?, Hk2)); trivial).
Time simplify_option_eq.
Time (apply IH).
Time by rewrite <- Hk2.
Time -
Time (intros [k Hk]).
Time revert l2 k Hk.
Time (induction l1 as [| x l1 IH]; simpl; intros l2 k).
Time {
Time (intros).
Time (apply submseteq_nil_l).
Time }
Time (destruct (list_remove x l2) as [k'| ] eqn:?; intros; simplify_eq).
Time (rewrite submseteq_cons_l).
Time eauto using list_remove_Some.
Time Qed.
Time #[global]
Instance submseteq_dec : (RelDecision (submseteq : relation (list A))).
Time Proof.
Time
(refine (\206\187 l1 l2, cast_if (decide (is_Some (list_remove_list l1 l2))));
  abstract (rewrite list_remove_list_submseteq; tauto)).
Time Defined.
Time #[global]Instance Permutation_dec : (RelDecision (\226\137\161\226\130\154@{A} )).
Time Proof.
Time
(refine
  (\206\187 l1 l2, cast_if_and (decide (length l1 = length l2)) (decide (l1 \226\138\134+ l2)));
  abstract (rewrite Permutation_alt; tauto)).
Time Defined.
Time End submseteq_dec.
Time #[global]Instance list_subseteq_po : (PreOrder (\226\138\134@{list A} )).
Time Proof.
Time (split; firstorder).
Time Qed.
Time Lemma list_subseteq_nil l : [] \226\138\134 l.
Time Proof.
Time (intros x).
Time by rewrite elem_of_nil.
Time Qed.
Time #[global]
Instance list_subseteq_Permutation :
 (Proper ((\226\137\161\226\130\154) ==> (\226\137\161\226\130\154) ==> (\226\134\148)) (\226\138\134@{list A} )).
Time Proof.
Time (intros l1 l2 Hl k1 k2 Hk).
Time (apply forall_proper; intros x).
Time by rewrite Hl, Hk.
Time Qed.
Time
Lemma Forall_Exists_dec (P Q : A \226\134\146 Prop) (dec : \226\136\128 x, {P x} + {Q x}) :
  \226\136\128 l, {Forall P l} + {Exists Q l}.
Time Proof.
Time
(refine
  (fix go l :=
     match l return ({Forall P l} + {Exists Q l}) with
     | [] => left _
     | x :: l => cast_if_and (dec x) (go l)
     end); clear go; intuition).
Time Defined.
Time Definition Forall_nil_2 := @Forall_nil A.
Time Definition Forall_cons_2 := @Forall_cons A.
Time #[global]
Instance Forall_proper :
 (Proper (pointwise_relation _ (\226\134\148) ==> (=) ==> (\226\134\148)) (@Forall A)).
Time Proof.
Time (split; subst; induction 1; constructor; by firstorder  auto).
Time Qed.
Time #[global]
Instance Exists_proper :
 (Proper (pointwise_relation _ (\226\134\148) ==> (=) ==> (\226\134\148)) (@Exists A)).
Time Proof.
Time (split; subst; induction 1; constructor; by firstorder  auto).
Time Qed.
Time Section Forall_Exists.
Time Context (P : A \226\134\146 Prop).
Time Lemma Forall_forall l : Forall P l \226\134\148 (\226\136\128 x, x \226\136\136 l \226\134\146 P x).
Time Proof.
Time (split; [ induction 1; inversion 1; subst; auto |  ]).
Time
(intros Hin; induction l as [| x l IH]; constructor;
  [ apply Hin; constructor |  ]).
Time (apply IH).
Time (intros ? ?).
Time (apply Hin).
Time by constructor.
Time Qed.
Time Lemma Forall_nil : Forall P [] \226\134\148 True.
Time Proof.
Time done.
Time Qed.
Time Lemma Forall_cons_1 x l : Forall P (x :: l) \226\134\146 P x \226\136\167 Forall P l.
Time Proof.
Time by inversion 1.
Time Qed.
Time Lemma Forall_cons x l : Forall P (x :: l) \226\134\148 P x \226\136\167 Forall P l.
Time Proof.
Time split.
Time by inversion 1.
Time (intros [? ?]).
Time by constructor.
Time Qed.
Time Lemma Forall_singleton x : Forall P [x] \226\134\148 P x.
Time Proof.
Time (rewrite Forall_cons, Forall_nil; tauto).
Time Qed.
Time
Lemma Forall_app_2 l1 l2 : Forall P l1 \226\134\146 Forall P l2 \226\134\146 Forall P (l1 ++ l2).
Time Proof.
Time (induction 1; simpl; auto).
Time Qed.
Time
Lemma Forall_app l1 l2 : Forall P (l1 ++ l2) \226\134\148 Forall P l1 \226\136\167 Forall P l2.
Time Proof.
Time (split; [ induction l1; inversion 1; intuition |  ]).
Time (intros [? ?]; auto using Forall_app_2).
Time Qed.
Time Lemma Forall_true l : (\226\136\128 x, P x) \226\134\146 Forall P l.
Time Proof.
Time (intros ?).
Time (induction l; auto).
Time Defined.
Time
Lemma Forall_impl (Q : A \226\134\146 Prop) l :
  Forall P l \226\134\146 (\226\136\128 x, P x \226\134\146 Q x) \226\134\146 Forall Q l.
Time Proof.
Time (intros H ?).
Time (induction H; auto).
Time Defined.
Time
Lemma Forall_iff l (Q : A \226\134\146 Prop) :
  (\226\136\128 x, P x \226\134\148 Q x) \226\134\146 Forall P l \226\134\148 Forall Q l.
Time Proof.
Time (intros H).
Time (apply Forall_proper).
Time (red; apply H).
Time done.
Time Qed.
Time Lemma Forall_not l : length l \226\137\160 0 \226\134\146 Forall (not \226\136\152 P) l \226\134\146 \194\172 Forall P l.
Time Proof.
Time by destruct 2; inversion 1.
Time Qed.
Time
Lemma Forall_and {Q} l : Forall (\206\187 x, P x \226\136\167 Q x) l \226\134\148 Forall P l \226\136\167 Forall Q l.
Time Proof.
Time (split; [ induction 1; constructor; naive_solver |  ]).
Time (intros [Hl Hl']; revert Hl'; induction Hl; inversion_clear 1; auto).
Time Qed.
Time Lemma Forall_and_l {Q} l : Forall (\206\187 x, P x \226\136\167 Q x) l \226\134\146 Forall P l.
Time Proof.
Time (rewrite Forall_and; tauto).
Time Qed.
Time Lemma Forall_and_r {Q} l : Forall (\206\187 x, P x \226\136\167 Q x) l \226\134\146 Forall Q l.
Time Proof.
Time (rewrite Forall_and; tauto).
Time Qed.
Time Lemma Forall_delete l i : Forall P l \226\134\146 Forall P (delete i l).
Time Proof.
Time (intros H).
Time revert i.
Time by induction H; intros [| i]; try constructor.
Time Qed.
Time Lemma Forall_lookup l : Forall P l \226\134\148 (\226\136\128 i x, l !! i = Some x \226\134\146 P x).
Time Proof.
Time (rewrite Forall_forall).
Time setoid_rewrite elem_of_list_lookup.
Time naive_solver.
Time Qed.
Time Lemma Forall_lookup_1 l i x : Forall P l \226\134\146 l !! i = Some x \226\134\146 P x.
Time Proof.
Time (rewrite Forall_lookup).
Time eauto.
Time Qed.
Time Lemma Forall_lookup_2 l : (\226\136\128 i x, l !! i = Some x \226\134\146 P x) \226\134\146 Forall P l.
Time Proof.
Time by rewrite Forall_lookup.
Time Qed.
Time Lemma Forall_reverse l : Forall P (reverse l) \226\134\148 Forall P l.
Time Proof.
Time (induction l as [| x l IH]; simpl; [ done |  ]).
Time (rewrite reverse_cons, Forall_cons, Forall_app, Forall_singleton).
Time naive_solver.
Time Qed.
Time Lemma Forall_tail l : Forall P l \226\134\146 Forall P (tail l).
Time Proof.
Time (destruct 1; simpl; auto).
Time Qed.
Time Lemma Forall_nth d l : Forall P l \226\134\148 (\226\136\128 i, i < length l \226\134\146 P (nth i l d)).
Time Proof.
Time (rewrite Forall_lookup).
Time split.
Time -
Time (intros Hl ? [x Hl']%lookup_lt_is_Some_2).
Time (rewrite (nth_lookup_Some _ _ _ _ Hl')).
Time by eapply Hl.
Time -
Time (intros Hl i x Hl').
Time specialize (Hl _ (lookup_lt_Some _ _ _ Hl')).
Time by rewrite (nth_lookup_Some _ _ _ _ Hl') in Hl.
Time Qed.
Time
Lemma Forall_alter f l i :
  Forall P l
  \226\134\146 (\226\136\128 x, l !! i = Some x \226\134\146 P x \226\134\146 P (f x)) \226\134\146 Forall P (alter f i l).
Time Proof.
Time (intros Hl).
Time revert i.
Time (induction Hl; simpl; intros [| i]; constructor; auto).
Time Qed.
Time
Lemma Forall_alter_inv f l i :
  Forall P (alter f i l)
  \226\134\146 (\226\136\128 x, l !! i = Some x \226\134\146 P (f x) \226\134\146 P x) \226\134\146 Forall P l.
Time Proof.
Time revert i.
Time
(induction l; intros [| ?]; simpl; inversion_clear 1; constructor; eauto).
Time Qed.
Time Lemma Forall_insert l i x : Forall P l \226\134\146 P x \226\134\146 Forall P (<[i:=x]> l).
Time Proof.
Time (rewrite list_insert_alter; auto using Forall_alter).
Time Qed.
Time
Lemma Forall_inserts l i k :
  Forall P l \226\134\146 Forall P k \226\134\146 Forall P (list_inserts i k l).
Time Proof.
Time (intros Hl Hk; revert i).
Time (induction Hk; simpl; auto using Forall_insert).
Time Qed.
Time Lemma Forall_replicate n x : P x \226\134\146 Forall P (replicate n x).
Time Proof.
Time (induction n; simpl; constructor; auto).
Time Qed.
Time Lemma Forall_replicate_eq n (x : A) : Forall (x =) (replicate n x).
Time Proof  using -(P).
Time (induction n; simpl; constructor; auto).
Time Qed.
Time Lemma Forall_take n l : Forall P l \226\134\146 Forall P (take n l).
Time Proof.
Time (intros Hl).
Time revert n.
Time (induction Hl; intros [| ?]; simpl; auto).
Time Qed.
Time Lemma Forall_drop n l : Forall P l \226\134\146 Forall P (drop n l).
Time Proof.
Time (intros Hl).
Time revert n.
Time (induction Hl; intros [| ?]; simpl; auto).
Time Qed.
Time Lemma Forall_resize n x l : P x \226\134\146 Forall P l \226\134\146 Forall P (resize n x l).
Time Proof.
Time (intros ? Hl).
Time revert n.
Time (induction Hl; intros [| ?]; simpl; auto using Forall_replicate).
Time Qed.
Time
Lemma Forall_resize_inv n x l :
  length l \226\137\164 n \226\134\146 Forall P (resize n x l) \226\134\146 Forall P l.
Time Proof.
Time (intros ?).
Time (rewrite resize_ge, Forall_app by done).
Time by intros [].
Time Qed.
Time
Lemma Forall_sublist_lookup l i n k :
  sublist_lookup i n l = Some k \226\134\146 Forall P l \226\134\146 Forall P k.
Time Proof.
Time (unfold sublist_lookup).
Time (intros; simplify_option_eq).
Time auto using Forall_take, Forall_drop.
Time Qed.
Time
Lemma Forall_sublist_alter f l i n k :
  Forall P l
  \226\134\146 sublist_lookup i n l = Some k
    \226\134\146 Forall P (f k) \226\134\146 Forall P (sublist_alter f i n l).
Time Proof.
Time (unfold sublist_alter, sublist_lookup).
Time (intros; simplify_option_eq).
Time auto using Forall_app_2, Forall_drop, Forall_take.
Time Qed.
Time
Lemma Forall_sublist_alter_inv f l i n k :
  sublist_lookup i n l = Some k
  \226\134\146 Forall P (sublist_alter f i n l) \226\134\146 Forall P (f k).
Time Proof.
Time (unfold sublist_alter, sublist_lookup).
Time (intros ?; simplify_option_eq).
Time (rewrite !Forall_app; tauto).
Time Qed.
Time
Lemma Forall_reshape l szs : Forall P l \226\134\146 Forall (Forall P) (reshape szs l).
Time Proof.
Time revert l.
Time (induction szs; simpl; auto using Forall_take, Forall_drop).
Time Qed.
Time
Lemma Forall_rev_ind (Q : list A \226\134\146 Prop) :
  Q []
  \226\134\146 (\226\136\128 x l, P x \226\134\146 Forall P l \226\134\146 Q l \226\134\146 Q (l ++ [x])) \226\134\146 \226\136\128 l, Forall P l \226\134\146 Q l.
Time Proof.
Time (intros ? ? l).
Time (induction l using rev_ind; auto).
Time (rewrite Forall_app, Forall_singleton; intros [? ?]; auto).
Time Qed.
Time #[global]
Instance Forall_Permutation : (Proper ((\226\137\161\226\130\154) ==> (\226\134\148)) (Forall P)).
Time Proof.
Time (intros l1 l2 Hl).
Time (rewrite !Forall_forall).
Time by setoid_rewrite Hl.
Time Qed.
Time Lemma Exists_exists l : Exists P l \226\134\148 (\226\136\131 x, x \226\136\136 l \226\136\167 P x).
Time Proof.
Time split.
Time -
Time (induction 1 as [x| y ? ? [x [? ?]]]; exists x; by repeat constructor).
Time -
Time (intros [x [Hin ?]]).
Time (induction l; [ by destruct (not_elem_of_nil x) |  ]).
Time (inversion Hin; subst).
Time by left.
Time (right; auto).
Time Qed.
Time Lemma Exists_inv x l : Exists P (x :: l) \226\134\146 P x \226\136\168 Exists P l.
Time Proof.
Time (inversion 1; intuition trivial).
Time Qed.
Time
Lemma Exists_app l1 l2 : Exists P (l1 ++ l2) \226\134\148 Exists P l1 \226\136\168 Exists P l2.
Time Proof.
Time split.
Time -
Time (induction l1; inversion 1; intuition).
Time -
Time (intros [H| H]; [ induction H | induction l1 ]; simpl; intuition).
Time Qed.
Time
Lemma Exists_impl (Q : A \226\134\146 Prop) l :
  Exists P l \226\134\146 (\226\136\128 x, P x \226\134\146 Q x) \226\134\146 Exists Q l.
Time Proof.
Time (intros H ?).
Time (induction H; auto).
Time Defined.
Time #[global]
Instance Exists_Permutation : (Proper ((\226\137\161\226\130\154) ==> (\226\134\148)) (Exists P)).
Time Proof.
Time (intros l1 l2 Hl).
Time (rewrite !Exists_exists).
Time by setoid_rewrite Hl.
Time Qed.
Time Lemma Exists_not_Forall l : Exists (not \226\136\152 P) l \226\134\146 \194\172 Forall P l.
Time Proof.
Time (induction 1; inversion_clear 1; contradiction).
Time Qed.
Time Lemma Forall_not_Exists l : Forall (not \226\136\152 P) l \226\134\146 \194\172 Exists P l.
Time Proof.
Time (induction 1; inversion_clear 1; contradiction).
Time Qed.
Time
Lemma Forall_list_difference `{!EqDecision A} l k :
  Forall P l \226\134\146 Forall P (list_difference l k).
Time Proof.
Time (rewrite !Forall_forall).
Time (intros ? x; rewrite elem_of_list_difference; naive_solver).
Time Qed.
Time
Lemma Forall_list_union `{!EqDecision A} l k :
  Forall P l \226\134\146 Forall P k \226\134\146 Forall P (list_union l k).
Time Proof.
Time (intros).
Time (apply Forall_app; auto using Forall_list_difference).
Time Qed.
Time
Lemma Forall_list_intersection `{!EqDecision A} l 
  k : Forall P l \226\134\146 Forall P (list_intersection l k).
Time Proof.
Time (rewrite !Forall_forall).
Time (intros ? x; rewrite elem_of_list_intersection; naive_solver).
Time Qed.
Time Context {dec : \226\136\128 x, Decision (P x)}.
Time Lemma not_Forall_Exists l : \194\172 Forall P l \226\134\146 Exists (not \226\136\152 P) l.
Time Proof.
Time intro.
Time by destruct (Forall_Exists_dec P (not \226\136\152 P) dec l).
Time Qed.
Time Lemma not_Exists_Forall l : \194\172 Exists P l \226\134\146 Forall (not \226\136\152 P) l.
Time Proof.
Time
by
 destruct (Forall_Exists_dec (not \226\136\152 P) P (\206\187 x : A, swap_if (decide (P x))) l).
Time Qed.
Time #[global]
Instance Forall_dec  l: (Decision (Forall P l)) :=
 match Forall_Exists_dec P (not \226\136\152 P) dec l with
 | left H => left H
 | right H => right (Exists_not_Forall _ H)
 end.
Time #[global]
Instance Exists_dec  l: (Decision (Exists P l)) :=
 match Forall_Exists_dec (not \226\136\152 P) P (\206\187 x, swap_if (decide (P x))) l with
 | left H => right (Forall_not_Exists _ H)
 | right H => left H
 end.
Time End Forall_Exists.
Time Lemma forallb_True (f : A \226\134\146 bool) xs : forallb f xs \226\134\148 Forall f xs.
Time Proof.
Time split.
Time (induction xs; naive_solver).
Time (induction 1; naive_solver).
Time Qed.
Time Lemma existb_True (f : A \226\134\146 bool) xs : existsb f xs \226\134\148 Exists f xs.
Time Proof.
Time split.
Time (induction xs; naive_solver).
Time (induction 1; naive_solver).
Time Qed.
Time
Lemma replicate_as_Forall (x : A) n l :
  replicate n x = l \226\134\148 length l = n \226\136\167 Forall (x =) l.
Time Proof.
Time (rewrite replicate_as_elem_of, Forall_forall).
Time naive_solver.
Time Qed.
Time
Lemma replicate_as_Forall_2 (x : A) n l :
  length l = n \226\134\146 Forall (x =) l \226\134\146 replicate n x = l.
Time Proof.
Time by rewrite replicate_as_Forall.
Time Qed.
Time End more_general_properties.
Time
Lemma Forall_swap {A} {B} (Q : A \226\134\146 B \226\134\146 Prop) l1 l2 :
  Forall (\206\187 y, Forall (Q y) l1) l2 \226\134\148 Forall (\206\187 x, Forall (flip Q x) l2) l1.
Time Proof.
Time (repeat setoid_rewrite Forall_forall).
Time (simpl).
Time (split; eauto).
Time Qed.
Time
Lemma Forall_seq (P : nat \226\134\146 Prop) i n :
  Forall P (seq i n) \226\134\148 (\226\136\128 j, i \226\137\164 j < i + n \226\134\146 P j).
Time Proof.
Time (rewrite Forall_lookup).
Time split.
Time -
Time (intros H j [? ?]).
Time (apply (H (j - i))).
Time (rewrite lookup_seq; auto with f_equal lia).
Time -
Time (intros H j x Hj).
Time (apply lookup_seq_inv in Hj).
Time (destruct Hj; subst).
Time auto with lia.
Time Qed.
Time
Lemma Forall2_same_length {A} {B} (l : list A) (k : list B) :
  Forall2 (\206\187 _ _, True) l k \226\134\148 length l = length k.
Time Proof.
Time (split; [ by induction 1; f_equal /= |  ]).
Time revert k.
Time (induction l; intros [| ? ?] ?; simplify_eq /=; auto).
Time Qed.
Time
Lemma Forall_Forall2 {A} (Q : A \226\134\146 A \226\134\146 Prop) l :
  Forall (\206\187 x, Q x x) l \226\134\146 Forall2 Q l l.
Time Proof.
Time (induction 1; constructor; auto).
Time Qed.
Time
Lemma Forall2_forall `{Inhabited A} B C (Q : A \226\134\146 B \226\134\146 C \226\134\146 Prop) 
  l k : Forall2 (\206\187 x y, \226\136\128 z, Q z x y) l k \226\134\148 (\226\136\128 z, Forall2 (Q z) l k).
Time Proof.
Time (split; [ induction 1; constructor; auto |  ]).
Time (intros Hlk).
Time (induction (Hlk inhabitant) as [| x y l k _ _ IH]; constructor).
Time -
Time (intros z).
Time by feed inversion Hlk z.
Time -
Time (apply IH).
Time (intros z).
Time by feed inversion Hlk z.
Time Qed.
Time
Lemma Forall2_Forall {A} P (l1 l2 : list A) :
  Forall2 P l1 l2 \226\134\146 Forall (curry P) (zip l1 l2).
Time Proof.
Time (induction 1; constructor; auto).
Time Qed.
Time Section Forall2.
Time Context {A} {B} (P : A \226\134\146 B \226\134\146 Prop).
Time Implicit Type x : A.
Time Implicit Type y : B.
Time Implicit Type l : list A.
Time Implicit Type k : list B.
Time Lemma Forall2_length l k : Forall2 P l k \226\134\146 length l = length k.
Time Proof.
Time by induction 1; f_equal /=.
Time Qed.
Time
Lemma Forall2_length_l l k n : Forall2 P l k \226\134\146 length l = n \226\134\146 length k = n.
Time Proof.
Time (intros ? <-; symmetry).
Time by apply Forall2_length.
Time Qed.
Time
Lemma Forall2_length_r l k n : Forall2 P l k \226\134\146 length k = n \226\134\146 length l = n.
Time Proof.
Time (intros ? <-).
Time by apply Forall2_length.
Time Qed.
Time
Lemma Forall2_true l k : (\226\136\128 x y, P x y) \226\134\146 length l = length k \226\134\146 Forall2 P l k.
Time Proof.
Time (rewrite <- Forall2_same_length).
Time (induction 2; naive_solver).
Time Qed.
Time Lemma Forall2_flip l k : Forall2 (flip P) k l \226\134\148 Forall2 P l k.
Time Proof.
Time (split; induction 1; constructor; auto).
Time Qed.
Time
Lemma Forall2_transitive {C} (Q : B \226\134\146 C \226\134\146 Prop) (R : A \226\134\146 C \226\134\146 Prop) 
  l k lC :
  (\226\136\128 x y z, P x y \226\134\146 Q y z \226\134\146 R x z)
  \226\134\146 Forall2 P l k \226\134\146 Forall2 Q k lC \226\134\146 Forall2 R l lC.
Time Proof.
Time (intros ? Hl).
Time revert lC.
Time (induction Hl; inversion_clear 1; eauto).
Time Qed.
Time
Lemma Forall2_impl (Q : A \226\134\146 B \226\134\146 Prop) l k :
  Forall2 P l k \226\134\146 (\226\136\128 x y, P x y \226\134\146 Q x y) \226\134\146 Forall2 Q l k.
Time Proof.
Time (intros H ?).
Time (induction H; auto).
Time Defined.
Time
Lemma Forall2_unique l k1 k2 :
  Forall2 P l k1
  \226\134\146 Forall2 P l k2 \226\134\146 (\226\136\128 x y1 y2, P x y1 \226\134\146 P x y2 \226\134\146 y1 = y2) \226\134\146 k1 = k2.
Time Proof.
Time (intros H).
Time revert k2.
Time (induction H; inversion_clear 1; intros; f_equal; eauto).
Time Qed.
Time
Lemma Forall_Forall2_l l k :
  length l = length k \226\134\146 Forall (\206\187 x, \226\136\128 y, P x y) l \226\134\146 Forall2 P l k.
Time Proof.
Time (rewrite <- Forall2_same_length).
Time (induction 1; inversion 1; auto).
Time Qed.
Time
Lemma Forall_Forall2_r l k :
  length l = length k \226\134\146 Forall (\206\187 y, \226\136\128 x, P x y) k \226\134\146 Forall2 P l k.
Time Proof.
Time (rewrite <- Forall2_same_length).
Time (induction 1; inversion 1; auto).
Time Qed.
Time
Lemma Forall2_Forall_l (Q : A \226\134\146 Prop) l k :
  Forall2 P l k \226\134\146 Forall (\206\187 y, \226\136\128 x, P x y \226\134\146 Q x) k \226\134\146 Forall Q l.
Time Proof.
Time (induction 1; inversion_clear 1; eauto).
Time Qed.
Time
Lemma Forall2_Forall_r (Q : B \226\134\146 Prop) l k :
  Forall2 P l k \226\134\146 Forall (\206\187 x, \226\136\128 y, P x y \226\134\146 Q y) l \226\134\146 Forall Q k.
Time Proof.
Time (induction 1; inversion_clear 1; eauto).
Time Qed.
Time Lemma Forall2_nil_inv_l k : Forall2 P [] k \226\134\146 k = [].
Time Proof.
Time by inversion 1.
Time Qed.
Time Lemma Forall2_nil_inv_r l : Forall2 P l [] \226\134\146 l = [].
Time Proof.
Time by inversion 1.
Time Qed.
Time
Lemma Forall2_cons_inv x l y k :
  Forall2 P (x :: l) (y :: k) \226\134\146 P x y \226\136\167 Forall2 P l k.
Time Proof.
Time by inversion 1.
Time Qed.
Time
Lemma Forall2_cons_inv_l x l k :
  Forall2 P (x :: l) k \226\134\146 \226\136\131 y k', P x y \226\136\167 Forall2 P l k' \226\136\167 k = y :: k'.
Time Proof.
Time (inversion 1; subst; eauto).
Time Qed.
Time
Lemma Forall2_cons_inv_r l k y :
  Forall2 P l (y :: k) \226\134\146 \226\136\131 x l', P x y \226\136\167 Forall2 P l' k \226\136\167 l = x :: l'.
Time Proof.
Time (inversion 1; subst; eauto).
Time Qed.
Time Lemma Forall2_cons_nil_inv x l : Forall2 P (x :: l) [] \226\134\146 False.
Time Proof.
Time by inversion 1.
Time Qed.
Time Lemma Forall2_nil_cons_inv y k : Forall2 P [] (y :: k) \226\134\146 False.
Time Proof.
Time by inversion 1.
Time Qed.
Time
Lemma Forall2_app_l l1 l2 k :
  Forall2 P l1 (take (length l1) k)
  \226\134\146 Forall2 P l2 (drop (length l1) k) \226\134\146 Forall2 P (l1 ++ l2) k.
Time Proof.
Time (intros).
Time (rewrite <- (take_drop (length l1) k)).
Time by apply Forall2_app.
Time Qed.
Time
Lemma Forall2_app_r l k1 k2 :
  Forall2 P (take (length k1) l) k1
  \226\134\146 Forall2 P (drop (length k1) l) k2 \226\134\146 Forall2 P l (k1 ++ k2).
Time Proof.
Time (intros).
Time (rewrite <- (take_drop (length k1) l)).
Time by apply Forall2_app.
Time Qed.
Time
Lemma Forall2_app_inv l1 l2 k1 k2 :
  length l1 = length k1
  \226\134\146 Forall2 P (l1 ++ l2) (k1 ++ k2) \226\134\146 Forall2 P l1 k1 \226\136\167 Forall2 P l2 k2.
Time Proof.
Time (rewrite <- Forall2_same_length).
Time (induction 1; inversion 1; naive_solver).
Time Qed.
Time
Lemma Forall2_app_inv_l l1 l2 k :
  Forall2 P (l1 ++ l2) k
  \226\134\148 (\226\136\131 k1 k2, Forall2 P l1 k1 \226\136\167 Forall2 P l2 k2 \226\136\167 k = k1 ++ k2).
Time Proof.
Time (split; [  | intros (?, (?, (?, (?, ->)))); by apply Forall2_app ]).
Time revert k.
Time (induction l1; inversion 1; naive_solver).
Time Qed.
Time
Lemma Forall2_app_inv_r l k1 k2 :
  Forall2 P l (k1 ++ k2)
  \226\134\148 (\226\136\131 l1 l2, Forall2 P l1 k1 \226\136\167 Forall2 P l2 k2 \226\136\167 l = l1 ++ l2).
Time Proof.
Time (split; [  | intros (?, (?, (?, (?, ->)))); by apply Forall2_app ]).
Time revert l.
Time (induction k1; inversion 1; naive_solver).
Time Qed.
Time Lemma Forall2_tail l k : Forall2 P l k \226\134\146 Forall2 P (tail l) (tail k).
Time Proof.
Time (destruct 1; simpl; auto).
Time Qed.
Time
Lemma Forall2_take l k n : Forall2 P l k \226\134\146 Forall2 P (take n l) (take n k).
Time Proof.
Time (intros Hl).
Time revert n.
Time (induction Hl; intros [| ?]; simpl; auto).
Time Qed.
Time
Lemma Forall2_drop l k n : Forall2 P l k \226\134\146 Forall2 P (drop n l) (drop n k).
Time Proof.
Time (intros Hl).
Time revert n.
Time (induction Hl; intros [| ?]; simpl; auto).
Time Qed.
Time
Lemma Forall2_lookup l k :
  Forall2 P l k \226\134\148 (\226\136\128 i, option_Forall2 P (l !! i) (k !! i)).
Time Proof.
Time
(split; [ induction 1; intros [| ?]; simpl; try constructor; eauto |  ]).
Time revert k.
Time (induction l as [| x l IH]; intros [| y k] H).
Time -
Time done.
Time -
Time feed inversion H 0.
Time -
Time feed inversion H 0.
Time -
Time (constructor; [ by feed inversion H 0 |  ]).
Time (apply (IH _ $ (\206\187 i, H (S i)))).
Time Qed.
Time
Lemma Forall2_lookup_lr l k i x y :
  Forall2 P l k \226\134\146 l !! i = Some x \226\134\146 k !! i = Some y \226\134\146 P x y.
Time Proof.
Time (rewrite Forall2_lookup; intros H; destruct (H i); naive_solver).
Time Qed.
Time
Lemma Forall2_lookup_l l k i x :
  Forall2 P l k \226\134\146 l !! i = Some x \226\134\146 \226\136\131 y, k !! i = Some y \226\136\167 P x y.
Time Proof.
Time (rewrite Forall2_lookup; intros H; destruct (H i); naive_solver).
Time Qed.
Time
Lemma Forall2_lookup_r l k i y :
  Forall2 P l k \226\134\146 k !! i = Some y \226\134\146 \226\136\131 x, l !! i = Some x \226\136\167 P x y.
Time Proof.
Time (rewrite Forall2_lookup; intros H; destruct (H i); naive_solver).
Time Qed.
Time
Lemma Forall2_same_length_lookup_2 l k :
  length l = length k
  \226\134\146 (\226\136\128 i x y, l !! i = Some x \226\134\146 k !! i = Some y \226\134\146 P x y) \226\134\146 Forall2 P l k.
Time Proof.
Time (rewrite <- Forall2_same_length).
Time (intros Hl Hlookup).
Time
(induction Hl as [| ? ? ? ? ? ? IH]; constructor; [ by apply (Hlookup 0) |  ]).
Time (apply IH).
Time (apply (\206\187 i, Hlookup (S i))).
Time Qed.
Time
Lemma Forall2_same_length_lookup l k :
  Forall2 P l k
  \226\134\148 length l = length k
    \226\136\167 (\226\136\128 i x y, l !! i = Some x \226\134\146 k !! i = Some y \226\134\146 P x y).
Time Proof.
Time
naive_solver eauto
 using Forall2_length, Forall2_lookup_lr, Forall2_same_length_lookup_2.
Time Qed.
Time
Lemma Forall2_alter_l f l k i :
  Forall2 P l k
  \226\134\146 (\226\136\128 x y, l !! i = Some x \226\134\146 k !! i = Some y \226\134\146 P x y \226\134\146 P (f x) y)
    \226\134\146 Forall2 P (alter f i l) k.
Time Proof.
Time (intros Hl).
Time revert i.
Time (induction Hl; intros [| ]; constructor; auto).
Time Qed.
Time
Lemma Forall2_alter_r f l k i :
  Forall2 P l k
  \226\134\146 (\226\136\128 x y, l !! i = Some x \226\134\146 k !! i = Some y \226\134\146 P x y \226\134\146 P x (f y))
    \226\134\146 Forall2 P l (alter f i k).
Time Proof.
Time (intros Hl).
Time revert i.
Time (induction Hl; intros [| ]; constructor; auto).
Time Qed.
Time
Lemma Forall2_alter f g l k i :
  Forall2 P l k
  \226\134\146 (\226\136\128 x y, l !! i = Some x \226\134\146 k !! i = Some y \226\134\146 P x y \226\134\146 P (f x) (g y))
    \226\134\146 Forall2 P (alter f i l) (alter g i k).
Time Proof.
Time (intros Hl).
Time revert i.
Time (induction Hl; intros [| ]; constructor; auto).
Time Qed.
Time
Lemma Forall2_insert l k x y i :
  Forall2 P l k \226\134\146 P x y \226\134\146 Forall2 P (<[i:=x]> l) (<[i:=y]> k).
Time Proof.
Time (intros Hl).
Time revert i.
Time (induction Hl; intros [| ]; constructor; auto).
Time Qed.
Time
Lemma Forall2_inserts l k l' k' i :
  Forall2 P l k
  \226\134\146 Forall2 P l' k' \226\134\146 Forall2 P (list_inserts i l' l) (list_inserts i k' k).
Time Proof.
Time (intros ? H).
Time revert i.
Time (induction H; eauto using Forall2_insert).
Time Qed.
Time
Lemma Forall2_delete l k i :
  Forall2 P l k \226\134\146 Forall2 P (delete i l) (delete i k).
Time Proof.
Time (intros Hl).
Time revert i.
Time (induction Hl; intros [| ]; simpl; intuition).
Time Qed.
Time
Lemma Forall2_option_list mx my :
  option_Forall2 P mx my \226\134\146 Forall2 P (option_list mx) (option_list my).
Time Proof.
Time (destruct 1; by constructor).
Time Qed.
Time
Lemma Forall2_filter Q1 Q2 `{\226\136\128 x, Decision (Q1 x)} 
  `{\226\136\128 y, Decision (Q2 y)} l k :
  (\226\136\128 x y, P x y \226\134\146 Q1 x \226\134\148 Q2 y)
  \226\134\146 Forall2 P l k \226\134\146 Forall2 P (filter Q1 l) (filter Q2 k).
Time Proof.
Time (intros HP; induction 1 as [| x y l k]; unfold filter; simpl; auto).
Time
(simplify_option_eq by by rewrite <- (HP x y); repeat constructor; auto).
Time Qed.
Time
Lemma Forall2_replicate_l k n x :
  length k = n \226\134\146 Forall (P x) k \226\134\146 Forall2 P (replicate n x) k.
Time Proof.
Time (intros <-).
Time (induction 1; simpl; auto).
Time Qed.
Time
Lemma Forall2_replicate_r l n y :
  length l = n \226\134\146 Forall (flip P y) l \226\134\146 Forall2 P l (replicate n y).
Time Proof.
Time (intros <-).
Time (induction 1; simpl; auto).
Time Qed.
Time
Lemma Forall2_replicate n x y :
  P x y \226\134\146 Forall2 P (replicate n x) (replicate n y).
Time Proof.
Time (induction n; simpl; constructor; auto).
Time Qed.
Time
Lemma Forall2_reverse l k : Forall2 P l k \226\134\146 Forall2 P (reverse l) (reverse k).
Time Proof.
Time
(induction 1; rewrite ?reverse_nil, ?reverse_cons; eauto using Forall2_app).
Time Qed.
Time
Lemma Forall2_last l k : Forall2 P l k \226\134\146 option_Forall2 P (last l) (last k).
Time Proof.
Time (induction 1 as [| ? ? ? ? ? []]; simpl; repeat constructor; auto).
Time Qed.
Time
Lemma Forall2_resize l k x y n :
  P x y \226\134\146 Forall2 P l k \226\134\146 Forall2 P (resize n x l) (resize n y k).
Time Proof.
Time (intros).
Time (rewrite !resize_spec, (Forall2_length l k) by done).
Time auto using Forall2_app, Forall2_take, Forall2_replicate.
Time Qed.
Time
Lemma Forall2_resize_l l k x y n m :
  P x y
  \226\134\146 Forall (flip P y) l
    \226\134\146 Forall2 P (resize n x l) k \226\134\146 Forall2 P (resize m x l) (resize m y k).
Time Proof.
Time (intros).
Time (destruct (decide (m \226\137\164 n))).
Time {
Time (rewrite <- (resize_resize l m n) by done).
Time by apply Forall2_resize.
Time }
Time (intros).
Time (assert (n = length k); subst).
Time {
Time by rewrite <- (Forall2_length (resize n x l) k), resize_length.
Time }
Time
(rewrite (le_plus_minus (length k) m), !resize_plus, resize_all, drop_all,
  resize_nil by lia).
Time
auto
 using Forall2_app, Forall2_replicate_r, Forall_resize, Forall_drop,
   resize_length.
Time Qed.
Time
Lemma Forall2_resize_r l k x y n m :
  P x y
  \226\134\146 Forall (P x) k
    \226\134\146 Forall2 P l (resize n y k) \226\134\146 Forall2 P (resize m x l) (resize m y k).
Time Proof.
Time (intros).
Time (destruct (decide (m \226\137\164 n))).
Time {
Time (rewrite <- (resize_resize k m n) by done).
Time by apply Forall2_resize.
Time }
Time (assert (n = length l); subst).
Time {
Time by rewrite (Forall2_length l (resize n y k)), resize_length.
Time }
Time
(rewrite (le_plus_minus (length l) m), !resize_plus, resize_all, drop_all,
  resize_nil by lia).
Time
auto
 using Forall2_app, Forall2_replicate_l, Forall_resize, Forall_drop,
   resize_length.
Time Qed.
Time
Lemma Forall2_resize_r_flip l k x y n m :
  P x y
  \226\134\146 Forall (P x) k
    \226\134\146 length k = m \226\134\146 Forall2 P l (resize n y k) \226\134\146 Forall2 P (resize m x l) k.
Time Proof.
Time (intros ? ? <- ?).
Time (rewrite <- (resize_all k y)  at 2).
Time (apply Forall2_resize_r with n; auto using Forall_true).
Time Qed.
Time
Lemma Forall2_sublist_lookup_l l k n i l' :
  Forall2 P l k
  \226\134\146 sublist_lookup n i l = Some l'
    \226\134\146 \226\136\131 k', sublist_lookup n i k = Some k' \226\136\167 Forall2 P l' k'.
Time Proof.
Time (unfold sublist_lookup).
Time (intros Hlk Hl).
Time (exists (take i (drop n k)); simplify_option_eq).
Time -
Time auto using Forall2_take, Forall2_drop.
Time -
Time (apply Forall2_length in Hlk; lia).
Time Qed.
Time
Lemma Forall2_sublist_lookup_r l k n i k' :
  Forall2 P l k
  \226\134\146 sublist_lookup n i k = Some k'
    \226\134\146 \226\136\131 l', sublist_lookup n i l = Some l' \226\136\167 Forall2 P l' k'.
Time Proof.
Time intro.
Time (unfold sublist_lookup).
Time (erewrite Forall2_length by eauto; intros; simplify_option_eq).
Time eauto using Forall2_take, Forall2_drop.
Time Qed.
Time
Lemma Forall2_sublist_alter f g l k i n l' k' :
  Forall2 P l k
  \226\134\146 sublist_lookup i n l = Some l'
    \226\134\146 sublist_lookup i n k = Some k'
      \226\134\146 Forall2 P (f l') (g k')
        \226\134\146 Forall2 P (sublist_alter f i n l) (sublist_alter g i n k).
Time Proof.
Time intro.
Time (unfold sublist_alter, sublist_lookup).
Time (erewrite Forall2_length by eauto; intros; simplify_option_eq).
Time auto using Forall2_app, Forall2_drop, Forall2_take.
Time Qed.
Time
Lemma Forall2_sublist_alter_l f l k i n l' k' :
  Forall2 P l k
  \226\134\146 sublist_lookup i n l = Some l'
    \226\134\146 sublist_lookup i n k = Some k'
      \226\134\146 Forall2 P (f l') k' \226\134\146 Forall2 P (sublist_alter f i n l) k.
Time Proof.
Time intro.
Time (unfold sublist_lookup, sublist_alter).
Time (erewrite <- Forall2_length by eauto; intros; simplify_option_eq).
Time
(apply Forall2_app_l; rewrite ?take_length_le by lia; auto using Forall2_take).
Time
(apply Forall2_app_l;
  erewrite Forall2_length, take_length, drop_length, <- Forall2_length,
   Min.min_l by eauto with lia; [ done |  ]).
Time (rewrite drop_drop; auto using Forall2_drop).
Time Qed.
Time #[global]
Instance Forall2_dec  `{dec : \226\136\128 x y, Decision (P x y)}:
 (RelDecision (Forall2 P)).
Time Proof.
Time
(refine
  (fix go l k : Decision (Forall2 P l k) :=
     match l, k with
     | [], [] => left _
     | x :: l, y :: k => cast_if_and (decide (P x y)) (go l k)
     | _, _ => right _
     end); clear dec go; abstract (first [ by constructor | by inversion 1 ])).
Time Defined.
Time End Forall2.
Time Section Forall2_proper.
Time Context {A} (R : relation A).
Time #[global]Instance: (Reflexive R \226\134\146 Reflexive (Forall2 R)).
Time Proof.
Time (intros ? l).
Time (induction l; by constructor).
Time Qed.
Time #[global]Instance: (Symmetric R \226\134\146 Symmetric (Forall2 R)).
Time Proof.
Time (intros).
Time (induction 1; constructor; auto).
Time Qed.
Time #[global]Instance: (Transitive R \226\134\146 Transitive (Forall2 R)).
Time Proof.
Time (intros ? ? ? ?).
Time (apply Forall2_transitive).
Time by apply @transitivity.
Time Qed.
Time #[global]Instance: (Equivalence R \226\134\146 Equivalence (Forall2 R)).
Time Proof.
Time (split; apply _).
Time Qed.
Time #[global]Instance: (PreOrder R \226\134\146 PreOrder (Forall2 R)).
Time Proof.
Time (split; apply _).
Time Qed.
Time #[global]Instance: (AntiSymm (=) R \226\134\146 AntiSymm (=) (Forall2 R)).
Time Proof.
Time (induction 2; inversion_clear 1; f_equal; auto).
Time Qed.
Time #[global]Instance: (Proper (R ==> Forall2 R ==> Forall2 R) (::)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]
Instance: (Proper (Forall2 R ==> Forall2 R ==> Forall2 R) (++)).
Time Proof.
Time (repeat intro).
Time by apply Forall2_app.
Time Qed.
Time #[global]Instance: (Proper (Forall2 R ==> (=)) length).
Time Proof.
Time (repeat intro).
Time eauto using Forall2_length.
Time Qed.
Time #[global]Instance: (Proper (Forall2 R ==> Forall2 R) tail).
Time Proof.
Time (repeat intro).
Time eauto using Forall2_tail.
Time Qed.
Time #[global]Instance: (Proper (Forall2 R ==> Forall2 R) (take n)).
Time Proof.
Time (repeat intro).
Time eauto using Forall2_take.
Time Qed.
Time #[global]Instance: (Proper (Forall2 R ==> Forall2 R) (drop n)).
Time Proof.
Time (repeat intro).
Time eauto using Forall2_drop.
Time Qed.
Time #[global]Instance: (Proper (Forall2 R ==> option_Forall2 R) (lookup i)).
Time Proof.
Time (repeat intro).
Time by apply Forall2_lookup.
Time Qed.
Time #[global]
Instance: (Proper (R ==> R) f \226\134\146 Proper (Forall2 R ==> Forall2 R) (alter f i)).
Time Proof.
Time (repeat intro).
Time eauto using Forall2_alter.
Time Qed.
Time #[global]Instance: (Proper (R ==> Forall2 R ==> Forall2 R) (insert i)).
Time Proof.
Time (repeat intro).
Time eauto using Forall2_insert.
Time Qed.
Time #[global]
Instance: (Proper (Forall2 R ==> Forall2 R ==> Forall2 R) (list_inserts i)).
Time Proof.
Time (repeat intro).
Time eauto using Forall2_inserts.
Time Qed.
Time #[global]Instance: (Proper (Forall2 R ==> Forall2 R) (delete i)).
Time Proof.
Time (repeat intro).
Time eauto using Forall2_delete.
Time Qed.
Time #[global]
Instance: (Proper (option_Forall2 R ==> Forall2 R) option_list).
Time Proof.
Time (repeat intro).
Time eauto using Forall2_option_list.
Time Qed.
Time #[global]
Instance:
 (\226\136\128 P `{\226\136\128 x, Decision (P x)},
    Proper (R ==> iff) P \226\134\146 Proper (Forall2 R ==> Forall2 R) (filter P)).
Time Proof.
Time (repeat intro; eauto using Forall2_filter).
Time Qed.
Time #[global]Instance: (Proper (R ==> Forall2 R) (replicate n)).
Time Proof.
Time (repeat intro).
Time eauto using Forall2_replicate.
Time Qed.
Time #[global]Instance: (Proper (Forall2 R ==> Forall2 R) reverse).
Time Proof.
Time (repeat intro).
Time eauto using Forall2_reverse.
Time Qed.
Time #[global]Instance: (Proper (Forall2 R ==> option_Forall2 R) last).
Time Proof.
Time (repeat intro).
Time eauto using Forall2_last.
Time Qed.
Time #[global]Instance: (Proper (R ==> Forall2 R ==> Forall2 R) (resize n)).
Time Proof.
Time (repeat intro).
Time eauto using Forall2_resize.
Time Qed.
Time End Forall2_proper.
Time Section Forall3.
Time Context {A} {B} {C} (P : A \226\134\146 B \226\134\146 C \226\134\146 Prop).
Time Hint Extern 0 (Forall3 _ _ _ _) => constructor: core.
Time
Lemma Forall3_app l1 l2 k1 k2 k1' k2' :
  Forall3 P l1 k1 k1'
  \226\134\146 Forall3 P l2 k2 k2' \226\134\146 Forall3 P (l1 ++ l2) (k1 ++ k2) (k1' ++ k2').
Time Proof.
Time (induction 1; simpl; auto).
Time Qed.
Time
Lemma Forall3_cons_inv_l x l k k' :
  Forall3 P (x :: l) k k'
  \226\134\146 \226\136\131 y k2 z k2', k = y :: k2 \226\136\167 k' = z :: k2' \226\136\167 P x y z \226\136\167 Forall3 P l k2 k2'.
Time Proof.
Time (inversion_clear 1; naive_solver).
Time Qed.
Time
Lemma Forall3_app_inv_l l1 l2 k k' :
  Forall3 P (l1 ++ l2) k k'
  \226\134\146 \226\136\131 k1 k2 k1' k2',
      k = k1 ++ k2
      \226\136\167 k' = k1' ++ k2' \226\136\167 Forall3 P l1 k1 k1' \226\136\167 Forall3 P l2 k2 k2'.
Time Proof.
Time revert k k'.
Time (induction l1 as [| x l1 IH]; simpl; inversion_clear 1).
Time -
Time by repeat eexists; eauto.
Time -
Time by repeat eexists; eauto.
Time -
Time
(edestruct IH as (?, (?, (?, (?, (?, (?, (?, ?))))))); eauto; naive_solver).
Time Qed.
Time
Lemma Forall3_cons_inv_m l y k k' :
  Forall3 P l (y :: k) k'
  \226\134\146 \226\136\131 x l2 z k2', l = x :: l2 \226\136\167 k' = z :: k2' \226\136\167 P x y z \226\136\167 Forall3 P l2 k k2'.
Time Proof.
Time (inversion_clear 1; naive_solver).
Time Qed.
Time
Lemma Forall3_app_inv_m l k1 k2 k' :
  Forall3 P l (k1 ++ k2) k'
  \226\134\146 \226\136\131 l1 l2 k1' k2',
      l = l1 ++ l2
      \226\136\167 k' = k1' ++ k2' \226\136\167 Forall3 P l1 k1 k1' \226\136\167 Forall3 P l2 k2 k2'.
Time Proof.
Time revert l k'.
Time (induction k1 as [| x k1 IH]; simpl; inversion_clear 1).
Time -
Time by repeat eexists; eauto.
Time -
Time by repeat eexists; eauto.
Time -
Time
(edestruct IH as (?, (?, (?, (?, (?, (?, (?, ?))))))); eauto; naive_solver).
Time Qed.
Time
Lemma Forall3_cons_inv_r l k z k' :
  Forall3 P l k (z :: k')
  \226\134\146 \226\136\131 x l2 y k2, l = x :: l2 \226\136\167 k = y :: k2 \226\136\167 P x y z \226\136\167 Forall3 P l2 k2 k'.
Time Proof.
Time (inversion_clear 1; naive_solver).
Time Qed.
Time
Lemma Forall3_app_inv_r l k k1' k2' :
  Forall3 P l k (k1' ++ k2')
  \226\134\146 \226\136\131 l1 l2 k1 k2,
      l = l1 ++ l2 \226\136\167 k = k1 ++ k2 \226\136\167 Forall3 P l1 k1 k1' \226\136\167 Forall3 P l2 k2 k2'.
Time Proof.
Time revert l k.
Time (induction k1' as [| x k1' IH]; simpl; inversion_clear 1).
Time -
Time by repeat eexists; eauto.
Time -
Time by repeat eexists; eauto.
Time -
Time
(edestruct IH as (?, (?, (?, (?, (?, (?, (?, ?))))))); eauto; naive_solver).
Time Qed.
Time
Lemma Forall3_impl (Q : A \226\134\146 B \226\134\146 C \226\134\146 Prop) l k k' :
  Forall3 P l k k' \226\134\146 (\226\136\128 x y z, P x y z \226\134\146 Q x y z) \226\134\146 Forall3 Q l k k'.
Time Proof.
Time (intros Hl ?; induction Hl; auto).
Time Defined.
Time Lemma Forall3_length_lm l k k' : Forall3 P l k k' \226\134\146 length l = length k.
Time Proof.
Time by induction 1; f_equal /=.
Time Qed.
Time
Lemma Forall3_length_lr l k k' : Forall3 P l k k' \226\134\146 length l = length k'.
Time Proof.
Time by induction 1; f_equal /=.
Time Qed.
Time
Lemma Forall3_lookup_lmr l k k' i x y z :
  Forall3 P l k k'
  \226\134\146 l !! i = Some x \226\134\146 k !! i = Some y \226\134\146 k' !! i = Some z \226\134\146 P x y z.
Time Proof.
Time (intros H).
Time revert i.
Time (induction H; intros [| ?] ? ? ?; simplify_eq /=; eauto).
Time Qed.
Time
Lemma Forall3_lookup_l l k k' i x :
  Forall3 P l k k'
  \226\134\146 l !! i = Some x \226\134\146 \226\136\131 y z, k !! i = Some y \226\136\167 k' !! i = Some z \226\136\167 P x y z.
Time Proof.
Time (intros H).
Time revert i.
Time (induction H; intros [| ?] ?; simplify_eq /=; eauto).
Time Qed.
Time
Lemma Forall3_lookup_m l k k' i y :
  Forall3 P l k k'
  \226\134\146 k !! i = Some y \226\134\146 \226\136\131 x z, l !! i = Some x \226\136\167 k' !! i = Some z \226\136\167 P x y z.
Time Proof.
Time (intros H).
Time revert i.
Time (induction H; intros [| ?] ?; simplify_eq /=; eauto).
Time Qed.
Time
Lemma Forall3_lookup_r l k k' i z :
  Forall3 P l k k'
  \226\134\146 k' !! i = Some z \226\134\146 \226\136\131 x y, l !! i = Some x \226\136\167 k !! i = Some y \226\136\167 P x y z.
Time Proof.
Time (intros H).
Time revert i.
Time (induction H; intros [| ?] ?; simplify_eq /=; eauto).
Time Qed.
Time
Lemma Forall3_alter_lm f g l k k' i :
  Forall3 P l k k'
  \226\134\146 (\226\136\128 x y z,
       l !! i = Some x
       \226\134\146 k !! i = Some y \226\134\146 k' !! i = Some z \226\134\146 P x y z \226\134\146 P (f x) (g y) z)
    \226\134\146 Forall3 P (alter f i l) (alter g i k) k'.
Time Proof.
Time (intros Hl).
Time revert i.
Time (induction Hl; intros [| ]; auto).
Time Qed.
Time End Forall3.
Time Section setoid.
Time Context `{Equiv A}.
Time Implicit Types l k : list A.
Time Lemma equiv_Forall2 l k : l \226\137\161 k \226\134\148 Forall2 (\226\137\161) l k.
Time Proof.
Time (split; induction 1; constructor; auto).
Time Qed.
Time Lemma list_equiv_lookup l k : l \226\137\161 k \226\134\148 (\226\136\128 i, l !! i \226\137\161 k !! i).
Time Proof.
Time (rewrite equiv_Forall2, Forall2_lookup).
Time by setoid_rewrite equiv_option_Forall2.
Time Qed.
Time #[global]
Instance list_equivalence :
 (Equivalence (\226\137\161@{A} ) \226\134\146 Equivalence (\226\137\161@{list A} )).
Time Proof.
Time split.
Time -
Time (intros l).
Time by apply equiv_Forall2.
Time -
Time (intros l k; rewrite !equiv_Forall2; by intros).
Time -
Time (intros l1 l2 l3; rewrite !equiv_Forall2; intros; by trans l2).
Time Qed.
Time #[global]
Instance list_leibniz  `{!LeibnizEquiv A}: (LeibnizEquiv (list A)).
Time Proof.
Time (induction 1; f_equal; fold_leibniz; auto).
Time Qed.
Time #[global]
Instance cons_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161@{list A} )) cons).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]
Instance app_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161@{list A} )) app).
Time Proof.
Time (induction 1; intros ? ? ?; simpl; try constructor; auto).
Time Qed.
Time #[global]
Instance length_proper : (Proper ((\226\137\161@{list A} ) ==> (=)) length).
Time Proof.
Time (induction 1; f_equal /=; auto).
Time Qed.
Time #[global]Instance tail_proper : (Proper ((\226\137\161@{list A} ) ==> (\226\137\161)) tail).
Time Proof.
Time (destruct 1; try constructor; auto).
Time Qed.
Time #[global]
Instance take_proper  n: (Proper ((\226\137\161@{list A} ) ==> (\226\137\161)) (take n)).
Time Proof.
Time (induction n; destruct 1; constructor; auto).
Time Qed.
Time #[global]
Instance drop_proper  n: (Proper ((\226\137\161@{list A} ) ==> (\226\137\161)) (drop n)).
Time Proof.
Time (induction n; destruct 1; simpl; try constructor; auto).
Time Qed.
Time #[global]
Instance list_lookup_proper  i: (Proper ((\226\137\161@{list A} ) ==> (\226\137\161)) (lookup i)).
Time Proof.
Time (induction i; destruct 1; simpl; try constructor; auto).
Time Qed.
Time #[global]
Instance list_alter_proper  f i:
 (Proper ((\226\137\161) ==> (\226\137\161)) f \226\134\146 Proper ((\226\137\161) ==> (\226\137\161@{list A} )) (alter f i)).
Time Proof.
Time (intros).
Time (induction i; destruct 1; constructor; eauto).
Time Qed.
Time #[global]
Instance list_insert_proper  i:
 (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161@{list A} )) (insert i)).
Time Proof.
Time (intros ? ? ?; induction i; destruct 1; constructor; eauto).
Time Qed.
Time #[global]
Instance list_inserts_proper  i:
 (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161@{list A} )) (list_inserts i)).
Time Proof.
Time (intros k1 k2 Hk; revert i).
Time (induction Hk; intros ? ? ? ?; simpl; try f_equiv; naive_solver).
Time Qed.
Time #[global]
Instance list_delete_proper  i: (Proper ((\226\137\161) ==> (\226\137\161@{list A} )) (delete i)).
Time Proof.
Time (induction i; destruct 1; try constructor; eauto).
Time Qed.
Time #[global]
Instance option_list_proper : (Proper ((\226\137\161) ==> (\226\137\161@{list A} )) option_list).
Time Proof.
Time (destruct 1; repeat constructor; auto).
Time Qed.
Time #[global]
Instance list_filter_proper  P `{\226\136\128 x, Decision (P x)}:
 (Proper ((\226\137\161) ==> iff) P \226\134\146 Proper ((\226\137\161) ==> (\226\137\161@{list A} )) (filter P)).
Time Proof.
Time (intros ? ? ?).
Time (rewrite !equiv_Forall2).
Time by apply Forall2_filter.
Time Qed.
Time #[global]
Instance replicate_proper  n: (Proper ((\226\137\161@{A} ) ==> (\226\137\161)) (replicate n)).
Time Proof.
Time (induction n; constructor; auto).
Time Qed.
Time #[global]
Instance reverse_proper : (Proper ((\226\137\161) ==> (\226\137\161@{list A} )) reverse).
Time Proof.
Time (induction 1; rewrite ?reverse_cons; simpl; [ constructor |  ]).
Time (apply app_proper; repeat constructor; auto).
Time Qed.
Time #[global]Instance last_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (@last A)).
Time Proof.
Time (induction 1 as [| ? ? ? ? ? []]; simpl; repeat constructor; auto).
Time Qed.
Time #[global]
Instance resize_proper  n:
 (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161@{list A} )) (resize n)).
Time Proof.
Time (induction n; destruct 2; simpl; repeat constructor || f_equiv; auto).
Time Qed.
Time End setoid.
Time Lemma list_fmap_id {A} (l : list A) : id <$> l = l.
Time Proof.
Time (induction l; f_equal /=; auto).
Time Qed.
Time Section fmap.
Time Context {A B : Type} (f : A \226\134\146 B).
Time Implicit Type l : list A.
Time
Lemma list_fmap_compose {C} (g : B \226\134\146 C) l : g \226\136\152 f <$> l = g <$> (f <$> l).
Time Proof.
Time (induction l; f_equal /=; auto).
Time Qed.
Time
Lemma list_fmap_ext (g : A \226\134\146 B) (l1 l2 : list A) :
  (\226\136\128 x, f x = g x) \226\134\146 l1 = l2 \226\134\146 fmap f l1 = fmap g l2.
Time Proof.
Time (intros ? <-).
Time (induction l1; f_equal /=; auto).
Time Qed.
Time
Lemma list_fmap_equiv_ext `{Equiv B} (g : A \226\134\146 B) l :
  (\226\136\128 x, f x \226\137\161 g x) \226\134\146 f <$> l \226\137\161 g <$> l.
Time Proof.
Time (induction l; constructor; auto).
Time Qed.
Time #[global]Instance fmap_inj : (Inj (=) (=) f \226\134\146 Inj (=) (=) (fmap f)).
Time Proof.
Time (intros ? l1).
Time (induction l1 as [| x l1 IH]; [ by intros [| ? ?] |  ]).
Time (intros [| ? ?]; intros; f_equal /=; simplify_eq; auto).
Time Qed.
Time Definition fmap_nil : f <$> [] = [] := eq_refl.
Time Definition fmap_cons x l : f <$> x :: l = f x :: (f <$> l) := eq_refl.
Time Lemma fmap_app l1 l2 : f <$> l1 ++ l2 = (f <$> l1) ++ (f <$> l2).
Time Proof.
Time by induction l1; f_equal /=.
Time Qed.
Time Lemma fmap_nil_inv k : f <$> k = [] \226\134\146 k = [].
Time Proof.
Time by destruct k.
Time Qed.
Time
Lemma fmap_cons_inv y l k :
  f <$> l = y :: k \226\134\146 \226\136\131 x l', y = f x \226\136\167 k = f <$> l' \226\136\167 l = x :: l'.
Time Proof.
Time (intros).
Time (destruct l; simplify_eq /=; eauto).
Time Qed.
Time
Lemma fmap_app_inv l k1 k2 :
  f <$> l = k1 ++ k2 \226\134\146 \226\136\131 l1 l2, k1 = f <$> l1 \226\136\167 k2 = f <$> l2 \226\136\167 l = l1 ++ l2.
Time Proof.
Time revert l.
Time
(induction k1 as [| y k1 IH]; simpl; [ intros l ?; by eexists [],l |  ]).
Time (intros [| x l] ?; simplify_eq /=).
Time (destruct (IH l) as (l1, (l2, (->, (->, ->)))); [ done |  ]).
Time by exists (x :: l1),l2.
Time Qed.
Time Lemma fmap_length l : length (f <$> l) = length l.
Time Proof.
Time by induction l; f_equal /=.
Time Qed.
Time Lemma fmap_reverse l : f <$> reverse l = reverse (f <$> l).
Time Proof.
Time
(induction l as [| ? ? IH]; csimpl; by rewrite ?reverse_cons, ?fmap_app, ?IH).
Time Qed.
Time Lemma fmap_tail l : f <$> tail l = tail (f <$> l).
Time Proof.
Time by destruct l.
Time Qed.
Time Lemma fmap_last l : last (f <$> l) = f <$> last l.
Time Proof.
Time (induction l as [| ? []]; simpl; auto).
Time Qed.
Time Lemma fmap_replicate n x : f <$> replicate n x = replicate n (f x).
Time Proof.
Time by induction n; f_equal /=.
Time Qed.
Time Lemma fmap_take n l : f <$> take n l = take n (f <$> l).
Time Proof.
Time revert n.
Time by induction l; intros [| ?]; f_equal /=.
Time Qed.
Time Lemma fmap_drop n l : f <$> drop n l = drop n (f <$> l).
Time Proof.
Time revert n.
Time by induction l; intros [| ?]; f_equal /=.
Time Qed.
Time Lemma fmap_resize n x l : f <$> resize n x l = resize n (f x) (f <$> l).
Time Proof.
Time revert n.
Time (induction l; intros [| ?]; f_equal /=; auto using fmap_replicate).
Time Qed.
Time
Lemma const_fmap (l : list A) (y : B) :
  (\226\136\128 x, f x = y) \226\134\146 f <$> l = replicate (length l) y.
Time Proof.
Time (intros; induction l; f_equal /=; auto).
Time Qed.
Time Lemma list_lookup_fmap l i : (f <$> l) !! i = f <$> l !! i.
Time Proof.
Time revert i.
Time (induction l; intros [| n]; by try revert n).
Time Qed.
Time
Lemma list_lookup_fmap_inv l i x :
  (f <$> l) !! i = Some x \226\134\146 \226\136\131 y, x = f y \226\136\167 l !! i = Some y.
Time Proof.
Time (intros Hi).
Time (rewrite list_lookup_fmap in Hi).
Time (destruct (l !! i) eqn:?; simplify_eq /=; eauto).
Time Qed.
Time Lemma list_fmap_insert l i x : f <$> <[i:=x]> l = <[i:=f x]> (f <$> l).
Time Proof.
Time revert i.
Time by induction l; intros [| i]; f_equal /=.
Time Qed.
Time
Lemma list_alter_fmap (g : A \226\134\146 A) (h : B \226\134\146 B) l i :
  Forall (\206\187 x, f (g x) = h (f x)) l \226\134\146 f <$> alter g i l = alter h i (f <$> l).
Time Proof.
Time (intros Hl).
Time revert i.
Time by induction Hl; intros [| i]; f_equal /=.
Time Qed.
Time Lemma elem_of_list_fmap_1 l x : x \226\136\136 l \226\134\146 f x \226\136\136 f <$> l.
Time Proof.
Time (induction 1; csimpl; rewrite elem_of_cons; intuition).
Time Qed.
Time Lemma elem_of_list_fmap_1_alt l x y : x \226\136\136 l \226\134\146 y = f x \226\134\146 y \226\136\136 f <$> l.
Time Proof.
Time (intros).
Time subst.
Time by apply elem_of_list_fmap_1.
Time Qed.
Time Lemma elem_of_list_fmap_2 l x : x \226\136\136 f <$> l \226\134\146 \226\136\131 y, x = f y \226\136\167 y \226\136\136 l.
Time Proof.
Time (induction l as [| y l IH]; simpl; inversion_clear 1).
Time -
Time exists y.
Time (split; [ done | by left ]).
Time -
Time (destruct IH as [z [? ?]]).
Time done.
Time exists z.
Time (split; [ done | by right ]).
Time Qed.
Time Lemma elem_of_list_fmap l x : x \226\136\136 f <$> l \226\134\148 (\226\136\131 y, x = f y \226\136\167 y \226\136\136 l).
Time Proof.
Time naive_solver eauto using elem_of_list_fmap_1_alt, elem_of_list_fmap_2.
Time Qed.
Time Lemma NoDup_fmap_1 l : NoDup (f <$> l) \226\134\146 NoDup l.
Time Proof.
Time (induction l; simpl; inversion_clear 1; constructor; auto).
Time (rewrite elem_of_list_fmap in *).
Time naive_solver.
Time Qed.
Time Lemma NoDup_fmap_2 `{!Inj (=) (=) f} l : NoDup l \226\134\146 NoDup (f <$> l).
Time Proof.
Time (induction 1; simpl; constructor; trivial).
Time (rewrite elem_of_list_fmap).
Time (intros [y [Hxy ?]]).
Time (apply (inj f) in Hxy).
Time by subst.
Time Qed.
Time Lemma NoDup_fmap `{!Inj (=) (=) f} l : NoDup (f <$> l) \226\134\148 NoDup l.
Time Proof.
Time (split; auto using NoDup_fmap_1, NoDup_fmap_2).
Time Qed.
Time #[global]
Instance fmap_sublist : (Proper (sublist ==> sublist) (fmap f)).
Time Proof.
Time (induction 1; simpl; econstructor; eauto).
Time Qed.
Time #[global]
Instance fmap_submseteq : (Proper (submseteq ==> submseteq) (fmap f)).
Time Proof.
Time (induction 1; simpl; econstructor; eauto).
Time Qed.
Time #[global]Instance fmap_Permutation : (Proper ((\226\137\161\226\130\154) ==> (\226\137\161\226\130\154)) (fmap f)).
Time Proof.
Time (induction 1; simpl; econstructor; eauto).
Time Qed.
Time
Lemma Forall_fmap_ext_1 (g : A \226\134\146 B) (l : list A) :
  Forall (\206\187 x, f x = g x) l \226\134\146 fmap f l = fmap g l.
Time Proof.
Time by induction 1; f_equal /=.
Time Qed.
Time
Lemma Forall_fmap_ext (g : A \226\134\146 B) (l : list A) :
  Forall (\206\187 x, f x = g x) l \226\134\148 fmap f l = fmap g l.
Time Proof.
Time (split; [ auto using Forall_fmap_ext_1 |  ]).
Time (induction l; simpl; constructor; simplify_eq; auto).
Time Qed.
Time
Lemma Forall_fmap (P : B \226\134\146 Prop) l : Forall P (f <$> l) \226\134\148 Forall (P \226\136\152 f) l.
Time Proof.
Time (split; induction l; inversion_clear 1; constructor; auto).
Time Qed.
Time
Lemma Exists_fmap (P : B \226\134\146 Prop) l : Exists P (f <$> l) \226\134\148 Exists (P \226\136\152 f) l.
Time Proof.
Time (split; induction l; inversion 1; constructor; by auto).
Time Qed.
Time
Lemma Forall2_fmap_l {C} (P : B \226\134\146 C \226\134\146 Prop) l k :
  Forall2 P (f <$> l) k \226\134\148 Forall2 (P \226\136\152 f) l k.
Time Proof.
Time (split; revert k; induction l; inversion_clear 1; constructor; auto).
Time Qed.
Time
Lemma Forall2_fmap_r {C} (P : C \226\134\146 B \226\134\146 Prop) k l :
  Forall2 P k (f <$> l) \226\134\148 Forall2 (\206\187 x, P x \226\136\152 f) k l.
Time Proof.
Time (split; revert k; induction l; inversion_clear 1; constructor; auto).
Time Qed.
Time
Lemma Forall2_fmap_1 {C} {D} (g : C \226\134\146 D) (P : B \226\134\146 D \226\134\146 Prop) 
  l k :
  Forall2 P (f <$> l) (g <$> k) \226\134\146 Forall2 (\206\187 x1 x2, P (f x1) (g x2)) l k.
Time Proof.
Time (revert k; induction l; intros [| ? ?]; inversion_clear 1; auto).
Time Qed.
Time
Lemma Forall2_fmap_2 {C} {D} (g : C \226\134\146 D) (P : B \226\134\146 D \226\134\146 Prop) 
  l k :
  Forall2 (\206\187 x1 x2, P (f x1) (g x2)) l k \226\134\146 Forall2 P (f <$> l) (g <$> k).
Time Proof.
Time (induction 1; csimpl; auto).
Time Qed.
Time
Lemma Forall2_fmap {C} {D} (g : C \226\134\146 D) (P : B \226\134\146 D \226\134\146 Prop) 
  l k :
  Forall2 P (f <$> l) (g <$> k) \226\134\148 Forall2 (\206\187 x1 x2, P (f x1) (g x2)) l k.
Time Proof.
Time (split; auto using Forall2_fmap_1, Forall2_fmap_2).
Time Qed.
Time
Lemma list_fmap_bind {C} (g : B \226\134\146 list C) l : (f <$> l) \226\137\171= g = l \226\137\171= g \226\136\152 f.
Time Proof.
Time by induction l; f_equal /=.
Time Qed.
Time End fmap.
Time
Lemma list_alter_fmap_mono {A} (f : A \226\134\146 A) (g : A \226\134\146 A) 
  l i :
  Forall (\206\187 x, f (g x) = g (f x)) l \226\134\146 f <$> alter g i l = alter g i (f <$> l).
Time Proof.
Time auto using list_alter_fmap.
Time Qed.
Time
Lemma NoDup_fmap_fst {A} {B} (l : list (A * B)) :
  (\226\136\128 x y1 y2, (x, y1) \226\136\136 l \226\134\146 (x, y2) \226\136\136 l \226\134\146 y1 = y2) \226\134\146 NoDup l \226\134\146 NoDup l.*1.
Time Proof.
Time (intros Hunique).
Time (induction 1 as [| [x1 y1] l Hin Hnodup IH]; csimpl; constructor).
Time -
Time (rewrite elem_of_list_fmap).
Time (intros [[x2 y2] [? ?]]; simpl in *; subst).
Time (destruct Hin).
Time (rewrite (Hunique x2 y1 y2); rewrite ?elem_of_cons; auto).
Time -
Time (apply IH).
Time (intros).
Time (eapply Hunique; rewrite ?elem_of_cons; eauto).
Time Qed.
Time #[global]
Instance omap_Permutation  {A} {B} (f : A \226\134\146 option B):
 (Proper ((\226\137\161\226\130\154) ==> (\226\137\161\226\130\154)) (omap f)).
Time Proof.
Time (induction 1; simpl; repeat case_match; econstructor; eauto).
Time Qed.
Time Section bind.
Time Context {A B : Type} (f : A \226\134\146 list B).
Time
Lemma list_bind_ext (g : A \226\134\146 list B) l1 l2 :
  (\226\136\128 x, f x = g x) \226\134\146 l1 = l2 \226\134\146 l1 \226\137\171= f = l2 \226\137\171= g.
Time Proof.
Time (intros ? <-).
Time by induction l1; f_equal /=.
Time Qed.
Time
Lemma Forall_bind_ext (g : A \226\134\146 list B) (l : list A) :
  Forall (\206\187 x, f x = g x) l \226\134\146 l \226\137\171= f = l \226\137\171= g.
Time Proof.
Time by induction 1; f_equal /=.
Time Qed.
Time #[global]
Instance bind_sublist : (Proper (sublist ==> sublist) (mbind f)).
Time Proof.
Time
(induction 1; simpl; auto;
  [ by apply sublist_app | by apply sublist_inserts_l ]).
Time Qed.
Time #[global]
Instance bind_submseteq : (Proper (submseteq ==> submseteq) (mbind f)).
Time Proof.
Time (induction 1; csimpl; auto).
Time -
Time by apply submseteq_app.
Time -
Time by rewrite !(assoc_L (++)), (comm (++) (f _)).
Time -
Time by apply submseteq_inserts_l.
Time -
Time (etrans; eauto).
Time Qed.
Time #[global]Instance bind_Permutation : (Proper ((\226\137\161\226\130\154) ==> (\226\137\161\226\130\154)) (mbind f)).
Time Proof.
Time (induction 1; csimpl; auto).
Time -
Time by f_equiv.
Time -
Time by rewrite !(assoc_L (++)), (comm (++) (f _)).
Time -
Time (etrans; eauto).
Time Qed.
Time Lemma bind_cons x l : (x :: l) \226\137\171= f = f x ++ l \226\137\171= f.
Time Proof.
Time done.
Time Qed.
Time Lemma bind_singleton x : [x] \226\137\171= f = f x.
Time Proof.
Time csimpl.
Time by rewrite (right_id_L _ (++)).
Time Qed.
Time Lemma bind_app l1 l2 : (l1 ++ l2) \226\137\171= f = (l1 \226\137\171= f) ++ l2 \226\137\171= f.
Time Proof.
Time by induction l1; csimpl; rewrite <- ?(assoc_L (++)); f_equal.
Time Qed.
Time
Lemma elem_of_list_bind (x : B) (l : list A) :
  x \226\136\136 l \226\137\171= f \226\134\148 (\226\136\131 y, x \226\136\136 f y \226\136\167 y \226\136\136 l).
Time Proof.
Time split.
Time -
Time (induction l as [| y l IH]; csimpl; [ inversion 1 |  ]).
Time (rewrite elem_of_app).
Time (intros [?| ?]).
Time +
Time exists y.
Time (split; [ done | by left ]).
Time +
Time (destruct IH as [z [? ?]]).
Time done.
Time exists z.
Time (split; [ done | by right ]).
Time -
Time (intros [y [Hx Hy]]).
Time (induction Hy; csimpl; rewrite elem_of_app; intuition).
Time Qed.
Time
Lemma Forall_bind (P : B \226\134\146 Prop) l :
  Forall P (l \226\137\171= f) \226\134\148 Forall (Forall P \226\136\152 f) l.
Time Proof.
Time split.
Time -
Time
(induction l; csimpl; rewrite ?Forall_app; constructor; csimpl; intuition).
Time -
Time (induction 1; csimpl; rewrite ?Forall_app; auto).
Time Qed.
Time
Lemma Forall2_bind {C} {D} (g : C \226\134\146 list D) (P : B \226\134\146 D \226\134\146 Prop) 
  l1 l2 :
  Forall2 (\206\187 x1 x2, Forall2 P (f x1) (g x2)) l1 l2
  \226\134\146 Forall2 P (l1 \226\137\171= f) (l2 \226\137\171= g).
Time Proof.
Time (induction 1; csimpl; auto using Forall2_app).
Time Qed.
Time End bind.
Time Section ret_join.
Time Context {A : Type}.
Time Lemma list_join_bind (ls : list (list A)) : mjoin ls = ls \226\137\171= id.
Time Proof.
Time by induction ls; f_equal /=.
Time Qed.
Time #[global]
Instance mjoin_Permutation : (Proper ((\226\137\161\226\130\154@{list A} ) ==> (\226\137\161\226\130\154)) mjoin).
Time Proof.
Time (intros ? ? E).
Time by rewrite !list_join_bind, E.
Time Qed.
Time Lemma elem_of_list_ret (x y : A) : x \226\136\136 @mret list _ A y \226\134\148 x = y.
Time Proof.
Time (apply elem_of_list_singleton).
Time Qed.
Time
Lemma elem_of_list_join (x : A) (ls : list (list A)) :
  x \226\136\136 mjoin ls \226\134\148 (\226\136\131 l : list A, x \226\136\136 l \226\136\167 l \226\136\136 ls).
Time Proof.
Time by rewrite list_join_bind, elem_of_list_bind.
Time Qed.
Time Lemma join_nil (ls : list (list A)) : mjoin ls = [] \226\134\148 Forall (=[]) ls.
Time Proof.
Time (split; [  | by induction 1 as [| [| ? ?] ?] ]).
Time by induction ls as [| [| ? ?] ?]; constructor; auto.
Time Qed.
Time Lemma join_nil_1 (ls : list (list A)) : mjoin ls = [] \226\134\146 Forall (=[]) ls.
Time Proof.
Time by rewrite join_nil.
Time Qed.
Time Lemma join_nil_2 (ls : list (list A)) : Forall (=[]) ls \226\134\146 mjoin ls = [].
Time Proof.
Time by rewrite join_nil.
Time Qed.
Time
Lemma Forall_join (P : A \226\134\146 Prop) (ls : list (list A)) :
  Forall (Forall P) ls \226\134\146 Forall P (mjoin ls).
Time Proof.
Time (induction 1; simpl; auto using Forall_app_2).
Time Qed.
Time
Lemma Forall2_join {B} (P : A \226\134\146 B \226\134\146 Prop) ls1 ls2 :
  Forall2 (Forall2 P) ls1 ls2 \226\134\146 Forall2 P (mjoin ls1) (mjoin ls2).
Time Proof.
Time (induction 1; simpl; auto using Forall2_app).
Time Qed.
Time End ret_join.
Time Section mapM.
Time Context {A B : Type} (f : A \226\134\146 option B).
Time
Lemma mapM_ext (g : A \226\134\146 option B) l : (\226\136\128 x, f x = g x) \226\134\146 mapM f l = mapM g l.
Time Proof.
Time (intros Hfg).
Time by induction l; simpl; rewrite ?Hfg, ?IHl.
Time Qed.
Time
Lemma Forall2_mapM_ext (g : A \226\134\146 option B) l k :
  Forall2 (\206\187 x y, f x = g y) l k \226\134\146 mapM f l = mapM g k.
Time Proof.
Time (induction 1 as [| ? ? ? ? Hfg ? IH]; simpl).
Time done.
Time by rewrite Hfg, IH.
Time Qed.
Time
Lemma Forall_mapM_ext (g : A \226\134\146 option B) l :
  Forall (\206\187 x, f x = g x) l \226\134\146 mapM f l = mapM g l.
Time Proof.
Time (induction 1 as [| ? ? Hfg ? IH]; simpl).
Time done.
Time by rewrite Hfg, IH.
Time Qed.
Time
Lemma mapM_Some_1 l k : mapM f l = Some k \226\134\146 Forall2 (\206\187 x y, f x = Some y) l k.
Time Proof.
Time revert k.
Time (induction l as [| x l]; intros [| y k]; simpl; try done).
Time -
Time (destruct (f x); simpl; [  | discriminate ]).
Time by destruct (mapM f l).
Time -
Time (destruct (f x) eqn:?; intros; simplify_option_eq; auto).
Time Qed.
Time
Lemma mapM_Some_2 l k : Forall2 (\206\187 x y, f x = Some y) l k \226\134\146 mapM f l = Some k.
Time Proof.
Time (induction 1 as [| ? ? ? ? Hf ? IH]; simpl; [ done |  ]).
Time (rewrite Hf).
Time (simpl).
Time by rewrite IH.
Time Qed.
Time
Lemma mapM_Some l k : mapM f l = Some k \226\134\148 Forall2 (\206\187 x y, f x = Some y) l k.
Time Proof.
Time (split; auto using mapM_Some_1, mapM_Some_2).
Time Qed.
Time Lemma mapM_length l k : mapM f l = Some k \226\134\146 length l = length k.
Time Proof.
Time (intros).
Time by eapply Forall2_length, mapM_Some_1.
Time Qed.
Time Lemma mapM_None_1 l : mapM f l = None \226\134\146 Exists (\206\187 x, f x = None) l.
Time Proof.
Time (induction l as [| x l IH]; simpl; [ done |  ]).
Time (destruct (f x) eqn:?; simpl; eauto).
Time by destruct (mapM f l); eauto.
Time Qed.
Time Lemma mapM_None_2 l : Exists (\206\187 x, f x = None) l \226\134\146 mapM f l = None.
Time Proof.
Time (induction 1 as [x l Hx| x l ? IH]; simpl; [ by rewrite Hx |  ]).
Time by destruct (f x); simpl; rewrite ?IH.
Time Qed.
Time Lemma mapM_None l : mapM f l = None \226\134\148 Exists (\206\187 x, f x = None) l.
Time Proof.
Time (split; auto using mapM_None_1, mapM_None_2).
Time Qed.
Time Lemma mapM_is_Some_1 l : is_Some (mapM f l) \226\134\146 Forall (is_Some \226\136\152 f) l.
Time Proof.
Time (unfold compose).
Time setoid_rewrite  <- not_eq_None_Some.
Time (rewrite mapM_None).
Time (apply (not_Exists_Forall _)).
Time Qed.
Time Lemma mapM_is_Some_2 l : Forall (is_Some \226\136\152 f) l \226\134\146 is_Some (mapM f l).
Time Proof.
Time (unfold compose).
Time setoid_rewrite  <- not_eq_None_Some.
Time (rewrite mapM_None).
Time (apply (Forall_not_Exists _)).
Time Qed.
Time Lemma mapM_is_Some l : is_Some (mapM f l) \226\134\148 Forall (is_Some \226\136\152 f) l.
Time Proof.
Time (split; auto using mapM_is_Some_1, mapM_is_Some_2).
Time Qed.
Time
Lemma mapM_fmap_Forall_Some (g : B \226\134\146 A) (l : list B) :
  Forall (\206\187 x, f (g x) = Some x) l \226\134\146 mapM f (g <$> l) = Some l.
Time Proof.
Time by induction 1; simpl; simplify_option_eq.
Time Qed.
Time
Lemma mapM_fmap_Some (g : B \226\134\146 A) (l : list B) :
  (\226\136\128 x, f (g x) = Some x) \226\134\146 mapM f (g <$> l) = Some l.
Time Proof.
Time (intros).
Time by apply mapM_fmap_Forall_Some, Forall_true.
Time Qed.
Time
Lemma mapM_fmap_Forall2_Some_inv (g : B \226\134\146 A) (l : list A) 
  (k : list B) :
  mapM f l = Some k
  \226\134\146 Forall2 (\206\187 x y, f x = Some y \226\134\146 g y = x) l k \226\134\146 g <$> k = l.
Time Proof.
Time (induction 2; simplify_option_eq; naive_solver).
Time Qed.
Time
Lemma mapM_fmap_Some_inv (g : B \226\134\146 A) (l : list A) 
  (k : list B) :
  mapM f l = Some k \226\134\146 (\226\136\128 x y, f x = Some y \226\134\146 g y = x) \226\134\146 g <$> k = l.
Time Proof.
Time eauto using mapM_fmap_Forall2_Some_inv, Forall2_true, mapM_length.
Time Qed.
Time End mapM.
Time Section seqZ.
Time Implicit Types (m n : Z) (i j : nat).
Time #[local]Open Scope Z.
Time Lemma seqZ_nil m n : n \226\137\164 0 \226\134\146 seqZ m n = [].
Time Proof.
Time by destruct n.
Time Qed.
Time
Lemma seqZ_cons m n : 0 < n \226\134\146 seqZ m n = m :: seqZ (Z.succ m) (Z.pred n).
Time Proof.
Time (intros H).
Time (unfold seqZ).
Time replace n with Z.succ (Z.pred n)  at 1 by lia.
Time (rewrite Z2Nat.inj_succ by lia).
Time f_equal /=.
Time (rewrite <- fmap_seq, <- list_fmap_compose).
Time (apply map_ext; naive_solver lia).
Time Qed.
Time Lemma seqZ_length m n : length (seqZ m n) = Z.to_nat n.
Time Proof.
Time (unfold seqZ; by rewrite fmap_length, seq_length).
Time Qed.
Time Lemma seqZ_fmap m m' n : Z.add m <$> seqZ m' n = seqZ (m + m') n.
Time Proof.
Time revert m'.
Time
(induction n as [| n ? IH| ] using (Z_succ_pred_induction 0); intros m').
Time -
Time by rewrite seqZ_nil.
Time -
Time (rewrite (seqZ_cons m') by lia).
Time (rewrite (seqZ_cons (m + m')) by lia).
Time f_equal /=.
Time (rewrite Z.pred_succ, IH; simpl).
Time (f_equal; lia).
Time -
Time by rewrite !seqZ_nil by lia.
Time Qed.
Time Lemma seqZ_lookup_lt m n i : i < n \226\134\146 seqZ m n !! i = Some (m + i).
Time Proof.
Time revert m i.
Time
(induction n as [| n ? IH| ] using (Z_succ_pred_induction 0); intros m i Hi;
  try lia).
Time (rewrite seqZ_cons by lia).
Time (destruct i as [| i]; simpl).
Time -
Time (f_equal; lia).
Time -
Time (rewrite Z.pred_succ, IH by lia).
Time (f_equal; lia).
Time Qed.
Time Lemma seqZ_lookup_ge m n i : n \226\137\164 i \226\134\146 seqZ m n !! i = None.
Time Proof.
Time revert m i.
Time
(induction n as [| n ? IH| ] using (Z_succ_pred_induction 0); intros m i Hi;
  try lia).
Time -
Time by rewrite seqZ_nil.
Time -
Time (rewrite seqZ_cons by lia).
Time (destruct i as [| i]; simpl; [ lia |  ]).
Time by rewrite Z.pred_succ, IH by lia.
Time -
Time by rewrite seqZ_nil by lia.
Time Qed.
Time
Lemma seqZ_lookup m n i m' : seqZ m n !! i = Some m' \226\134\148 m' = m + i \226\136\167 i < n.
Time Proof.
Time (destruct (Z_le_gt_dec n i)).
Time {
Time (rewrite seqZ_lookup_ge by lia).
Time naive_solver lia.
Time }
Time (rewrite seqZ_lookup_lt by lia).
Time naive_solver lia.
Time Qed.
Time End seqZ.
Time Section permutations.
Time Context {A : Type}.
Time Implicit Types x y z : A.
Time Implicit Type l : list A.
Time Lemma interleave_cons x l : x :: l \226\136\136 interleave x l.
Time Proof.
Time (destruct l; simpl; rewrite elem_of_cons; auto).
Time Qed.
Time
Lemma interleave_Permutation x l l' : l' \226\136\136 interleave x l \226\134\146 l' \226\137\161\226\130\154 x :: l.
Time Proof.
Time revert l'.
Time (induction l as [| y l IH]; intros l'; simpl).
Time -
Time (rewrite elem_of_list_singleton).
Time by intros ->.
Time -
Time (rewrite elem_of_cons, elem_of_list_fmap).
Time (intros [->| [? [-> H]]]; [ done |  ]).
Time (rewrite (IH _ H)).
Time constructor.
Time Qed.
Time Lemma permutations_refl l : l \226\136\136 permutations l.
Time Proof.
Time (induction l; simpl; [ by apply elem_of_list_singleton |  ]).
Time (apply elem_of_list_bind).
Time eauto using interleave_cons.
Time Qed.
Time
Lemma permutations_skip x l l' :
  l \226\136\136 permutations l' \226\134\146 x :: l \226\136\136 permutations (x :: l').
Time Proof.
Time intro.
Time (apply elem_of_list_bind; eauto using interleave_cons).
Time Qed.
Time
Lemma permutations_swap x y l : y :: x :: l \226\136\136 permutations (x :: y :: l).
Time Proof.
Time (simpl).
Time (apply elem_of_list_bind).
Time exists (y :: l).
Time (split; simpl).
Time -
Time (destruct l; csimpl; rewrite !elem_of_cons; auto).
Time -
Time (apply elem_of_list_bind).
Time (simpl).
Time eauto using interleave_cons, permutations_refl.
Time Qed.
Time Lemma permutations_nil l : l \226\136\136 permutations [] \226\134\148 l = [].
Time Proof.
Time (simpl).
Time by rewrite elem_of_list_singleton.
Time Qed.
Time
Lemma interleave_interleave_toggle x1 x2 l1 l2 l3 :
  l1 \226\136\136 interleave x1 l2
  \226\134\146 l2 \226\136\136 interleave x2 l3
    \226\134\146 \226\136\131 l4, l1 \226\136\136 interleave x2 l4 \226\136\167 l4 \226\136\136 interleave x1 l3.
Time Proof.
Time revert l1 l2.
Time (induction l3 as [| y l3 IH]; intros l1 l2; simpl).
Time {
Time (rewrite !elem_of_list_singleton).
Time (intros ? ->).
Time exists [x1].
Time (change_no_check (interleave x2 [x1]) with ([[x2; x1]] ++ [[x1; x2]])).
Time by rewrite (comm (++)), elem_of_list_singleton.
Time }
Time (rewrite elem_of_cons, elem_of_list_fmap).
Time (intros Hl1 [?| [l2' [? ?]]]; simplify_eq /=).
Time -
Time (rewrite !elem_of_cons, elem_of_list_fmap in Hl1).
Time (destruct Hl1 as [?| [?| [l4 [? ?]]]]; subst).
Time +
Time exists (x1 :: y :: l3).
Time csimpl.
Time (rewrite !elem_of_cons).
Time tauto.
Time +
Time exists (x1 :: y :: l3).
Time csimpl.
Time (rewrite !elem_of_cons).
Time tauto.
Time +
Time exists l4.
Time (simpl).
Time (rewrite elem_of_cons).
Time auto using interleave_cons.
Time -
Time (rewrite elem_of_cons, elem_of_list_fmap in Hl1).
Time (destruct Hl1 as [?| [l1' [? ?]]]; subst).
Time +
Time exists (x1 :: y :: l3).
Time csimpl.
Time (rewrite !elem_of_cons, !elem_of_list_fmap).
Time (split; [  | by auto ]).
Time right.
Time right.
Time exists (y :: l2').
Time (rewrite elem_of_list_fmap).
Time naive_solver.
Time +
Time (destruct (IH l1' l2') as [l4 [? ?]]; auto).
Time exists (y :: l4).
Time (simpl).
Time (rewrite !elem_of_cons, !elem_of_list_fmap).
Time naive_solver.
Time Qed.
Time
Lemma permutations_interleave_toggle x l1 l2 l3 :
  l1 \226\136\136 permutations l2
  \226\134\146 l2 \226\136\136 interleave x l3 \226\134\146 \226\136\131 l4, l1 \226\136\136 interleave x l4 \226\136\167 l4 \226\136\136 permutations l3.
Time Proof.
Time revert l1 l2.
Time (induction l3 as [| y l3 IH]; intros l1 l2; simpl).
Time {
Time (rewrite elem_of_list_singleton).
Time (intros Hl1 ->).
Time eexists [].
Time by rewrite elem_of_list_singleton.
Time }
Time (rewrite elem_of_cons, elem_of_list_fmap).
Time (intros Hl1 [?| [l2' [? Hl2']]]; simplify_eq /=).
Time -
Time (rewrite elem_of_list_bind in Hl1).
Time (destruct Hl1 as [l1' [? ?]]).
Time by exists l1'.
Time -
Time (rewrite elem_of_list_bind in Hl1).
Time setoid_rewrite elem_of_list_bind.
Time (destruct Hl1 as [l1' [? ?]]).
Time (destruct (IH l1' l2') as (l1'', (?, ?)); auto).
Time
(destruct (interleave_interleave_toggle y x l1 l1' l1'') as (?, (?, ?));
  eauto).
Time Qed.
Time
Lemma permutations_trans l1 l2 l3 :
  l1 \226\136\136 permutations l2 \226\134\146 l2 \226\136\136 permutations l3 \226\134\146 l1 \226\136\136 permutations l3.
Time Proof.
Time revert l1 l2.
Time (induction l3 as [| x l3 IH]; intros l1 l2; simpl).
Time -
Time (rewrite !elem_of_list_singleton).
Time (intros Hl1 ->; simpl in *).
Time by rewrite elem_of_list_singleton in Hl1.
Time -
Time (rewrite !elem_of_list_bind).
Time (intros Hl1 [l2' [Hl2 Hl2']]).
Time
(destruct (permutations_interleave_toggle x l1 l2 l2') as [? [? ?]]; eauto).
Time Qed.
Time Lemma permutations_Permutation l l' : l' \226\136\136 permutations l \226\134\148 l \226\137\161\226\130\154 l'.
Time Proof.
Time split.
Time -
Time revert l'.
Time (induction l; simpl; intros l'').
Time +
Time (rewrite elem_of_list_singleton).
Time by intros ->.
Time +
Time (rewrite elem_of_list_bind).
Time (intros [l' [Hl'' ?]]).
Time (rewrite (interleave_Permutation _ _ _ Hl'')).
Time (constructor; auto).
Time -
Time
(induction 1; eauto
  using permutations_refl, permutations_skip, permutations_swap,
    permutations_trans).
Time Qed.
Time End permutations.
Time Definition foldr_app := @fold_right_app.
Time
Lemma foldl_app {A} {B} (f : A \226\134\146 B \226\134\146 A) (l k : list B) 
  (a : A) : foldl f a (l ++ k) = foldl f (foldl f a l) k.
Time Proof.
Time revert a.
Time (induction l; simpl; auto).
Time Qed.
Time
Lemma foldr_permutation {A} {B} (R : relation B) `{!PreOrder R}
  (f : A \226\134\146 B \226\134\146 B) (b : B) `{Hf : !\226\136\128 x, Proper (R ==> R) (f x)}
  (l1 l2 : list A) :
  (\226\136\128 j1 a1 j2 a2 b,
     j1 \226\137\160 j2
     \226\134\146 l1 !! j1 = Some a1
       \226\134\146 l1 !! j2 = Some a2 \226\134\146 R (f a1 (f a2 b)) (f a2 (f a1 b)))
  \226\134\146 l1 \226\137\161\226\130\154 l2 \226\134\146 R (foldr f b l1) (foldr f b l2).
Time Proof.
Time (intros Hf').
Time (induction 1 as [| x l1 l2 _ IH| x y l| l1 l2 l3 Hl12 IH _ IH']; simpl).
Time -
Time done.
Time -
Time (apply Hf, IH; eauto).
Time -
Time (apply (Hf' 0 _ 1); eauto).
Time -
Time (etrans; [ eapply IH, Hf' |  ]).
Time (apply IH'; intros j1 a1 j2 a2 b' ? ? ?).
Time (symmetry in Hl12; apply Permutation_inj in Hl12 as [_ (g, (?, Hg))]).
Time (apply (Hf' (g j1) _ (g j2)); [ naive_solver | by rewrite <- Hg.. ]).
Time Qed.
Time
Lemma foldr_permutation_proper {A} {B} (R : relation B) 
  `{!PreOrder R} (f : A \226\134\146 B \226\134\146 B) (b : B) `{!\226\136\128 x, Proper (R ==> R) (f x)}
  (Hf : \226\136\128 a1 a2 b, R (f a1 (f a2 b)) (f a2 (f a1 b))) :
  Proper ((\226\137\161\226\130\154) ==> R) (foldr f b).
Time Proof.
Time (intros l1 l2 Hl).
Time (apply foldr_permutation; auto).
Time Qed.
Time
Instance foldr_permutation_proper'  {A} (R : relation A) 
 `{!PreOrder R} (f : A \226\134\146 A \226\134\146 A) (a : A) `{!\226\136\128 a, Proper (R ==> R) (f a)}
 `{!Assoc R f} `{!Comm R f}: (Proper ((\226\137\161\226\130\154) ==> R) (foldr f a)).
Time Proof.
Time (apply (foldr_permutation_proper R f); [ solve_proper |  ]).
Time (assert (Proper (R ==> R ==> R) f)).
Time {
Time (intros a1 a2 Ha b1 b2 Hb).
Time by rewrite Hb, (comm f a1), Ha, (comm f).
Time }
Time (intros a1 a2 b).
Time
by rewrite (assoc f), (comm f _ b), (assoc f), (comm f b), (comm f _ a2).
Time Qed.
Time Section zip_with.
Time Context {A B C : Type} (f : A \226\134\146 B \226\134\146 C).
Time Implicit Type x : A.
Time Implicit Type y : B.
Time Implicit Type l : list A.
Time Implicit Type k : list B.
Time Lemma zip_with_nil_r l : zip_with f l [] = [].
Time Proof.
Time by destruct l.
Time Qed.
Time
Lemma zip_with_app l1 l2 k1 k2 :
  length l1 = length k1
  \226\134\146 zip_with f (l1 ++ l2) (k1 ++ k2) = zip_with f l1 k1 ++ zip_with f l2 k2.
Time Proof.
Time (rewrite <- Forall2_same_length).
Time (induction 1; f_equal /=; auto).
Time Qed.
Time
Lemma zip_with_app_l l1 l2 k :
  zip_with f (l1 ++ l2) k =
  zip_with f l1 (take (length l1) k) ++ zip_with f l2 (drop (length l1) k).
Time Proof.
Time revert k.
Time (induction l1; intros [| ? ?]; f_equal /=; auto).
Time by destruct l2.
Time Qed.
Time
Lemma zip_with_app_r l k1 k2 :
  zip_with f l (k1 ++ k2) =
  zip_with f (take (length k1) l) k1 ++ zip_with f (drop (length k1) l) k2.
Time Proof.
Time revert l.
Time (induction k1; intros [| ? ?]; f_equal /=; auto).
Time Qed.
Time Lemma zip_with_flip l k : zip_with (flip f) k l = zip_with f l k.
Time Proof.
Time revert k.
Time (induction l; intros [| ? ?]; f_equal /=; auto).
Time Qed.
Time
Lemma zip_with_ext (g : A \226\134\146 B \226\134\146 C) l1 l2 k1 k2 :
  (\226\136\128 x y, f x y = g x y)
  \226\134\146 l1 = l2 \226\134\146 k1 = k2 \226\134\146 zip_with f l1 k1 = zip_with g l2 k2.
Time Proof.
Time (intros ? <- <-).
Time revert k1.
Time by induction l1; intros [| ? ?]; f_equal /=.
Time Qed.
Time
Lemma Forall_zip_with_ext_l (g : A \226\134\146 B \226\134\146 C) l k1 k2 :
  Forall (\206\187 x, \226\136\128 y, f x y = g x y) l
  \226\134\146 k1 = k2 \226\134\146 zip_with f l k1 = zip_with g l k2.
Time Proof.
Time (intros Hl <-).
Time revert k1.
Time by induction Hl; intros [| ? ?]; f_equal /=.
Time Qed.
Time
Lemma Forall_zip_with_ext_r (g : A \226\134\146 B \226\134\146 C) l1 l2 
  k :
  l1 = l2
  \226\134\146 Forall (\206\187 y, \226\136\128 x, f x y = g x y) k \226\134\146 zip_with f l1 k = zip_with g l2 k.
Time Proof.
Time (intros <- Hk).
Time revert l1.
Time by induction Hk; intros [| ? ?]; f_equal /=.
Time Qed.
Time
Lemma zip_with_fmap_l {D} (g : D \226\134\146 A) lD k :
  zip_with f (g <$> lD) k = zip_with (\206\187 z, f (g z)) lD k.
Time Proof.
Time revert k.
Time by induction lD; intros [| ? ?]; f_equal /=.
Time Qed.
Time
Lemma zip_with_fmap_r {D} (g : D \226\134\146 B) l kD :
  zip_with f l (g <$> kD) = zip_with (\206\187 x z, f x (g z)) l kD.
Time Proof.
Time revert kD.
Time by induction l; intros [| ? ?]; f_equal /=.
Time Qed.
Time Lemma zip_with_nil_inv l k : zip_with f l k = [] \226\134\146 l = [] \226\136\168 k = [].
Time Proof.
Time (destruct l, k; intros; simplify_eq /=; auto).
Time Qed.
Time
Lemma zip_with_cons_inv l k z lC :
  zip_with f l k = z :: lC
  \226\134\146 \226\136\131 x y l' k',
      z = f x y \226\136\167 lC = zip_with f l' k' \226\136\167 l = x :: l' \226\136\167 k = y :: k'.
Time Proof.
Time (intros).
Time (destruct l, k; simplify_eq /=; repeat eexists).
Time Qed.
Time
Lemma zip_with_app_inv l k lC1 lC2 :
  zip_with f l k = lC1 ++ lC2
  \226\134\146 \226\136\131 l1 k1 l2 k2,
      lC1 = zip_with f l1 k1
      \226\136\167 lC2 = zip_with f l2 k2
        \226\136\167 l = l1 ++ l2 \226\136\167 k = k1 ++ k2 \226\136\167 length l1 = length k1.
Time Proof.
Time revert l k.
Time (induction lC1 as [| z lC1 IH]; simpl).
Time {
Time (intros l k ?).
Time by eexists [],[],l,k.
Time }
Time (intros [| x l] [| y k] ?; simplify_eq /=).
Time
(destruct (IH l k) as (l1, (k1, (l2, (k2, (->, (->, (->, (->, ?))))))));
  [ done |  ]).
Time (exists (x :: l1),(y :: k1),l2,k2; simpl; auto with congruence).
Time Qed.
Time
Lemma zip_with_inj `{!Inj2 (=) (=) (=) f} l1 l2 k1 
  k2 :
  length l1 = length k1
  \226\134\146 length l2 = length k2
    \226\134\146 zip_with f l1 k1 = zip_with f l2 k2 \226\134\146 l1 = l2 \226\136\167 k1 = k2.
Time Proof.
Time (rewrite <- !Forall2_same_length).
Time (intros Hl).
Time revert l2 k2.
Time (induction Hl; intros ? ? [] ?; f_equal; naive_solver).
Time Qed.
Time
Lemma zip_with_length l k :
  length (zip_with f l k) = min (length l) (length k).
Time Proof.
Time revert k.
Time (induction l; intros [| ? ?]; simpl; auto with lia).
Time Qed.
Time
Lemma zip_with_length_l l k :
  length l \226\137\164 length k \226\134\146 length (zip_with f l k) = length l.
Time Proof.
Time (rewrite zip_with_length; lia).
Time Qed.
Time
Lemma zip_with_length_l_eq l k :
  length l = length k \226\134\146 length (zip_with f l k) = length l.
Time Proof.
Time (rewrite zip_with_length; lia).
Time Qed.
Time
Lemma zip_with_length_r l k :
  length k \226\137\164 length l \226\134\146 length (zip_with f l k) = length k.
Time Proof.
Time (rewrite zip_with_length; lia).
Time Qed.
Time
Lemma zip_with_length_r_eq l k :
  length k = length l \226\134\146 length (zip_with f l k) = length k.
Time Proof.
Time (rewrite zip_with_length; lia).
Time Qed.
Time
Lemma zip_with_length_same_l P l k :
  Forall2 P l k \226\134\146 length (zip_with f l k) = length l.
Time Proof.
Time (induction 1; simpl; auto).
Time Qed.
Time
Lemma zip_with_length_same_r P l k :
  Forall2 P l k \226\134\146 length (zip_with f l k) = length k.
Time Proof.
Time (induction 1; simpl; auto).
Time Qed.
Time
Lemma lookup_zip_with l k i :
  zip_with f l k !! i = x \226\134\144 l !! i; y \226\134\144 k !! i; Some (f x y).
Time Proof.
Time revert k i.
Time (induction l; intros [| ? ?] [| ?]; f_equal /=; auto).
Time by destruct (_ !! _).
Time Qed.
Time
Lemma insert_zip_with l k i x y :
  <[i:=f x y]> (zip_with f l k) = zip_with f (<[i:=x]> l) (<[i:=y]> k).
Time Proof.
Time revert i k.
Time (induction l; intros [| ?] [| ? ?]; f_equal /=; auto).
Time Qed.
Time
Lemma fmap_zip_with_l (g : C \226\134\146 A) l k :
  (\226\136\128 x y, g (f x y) = x) \226\134\146 length l \226\137\164 length k \226\134\146 g <$> zip_with f l k = l.
Time Proof.
Time revert k.
Time (induction l; intros [| ? ?] ? ?; f_equal /=; auto with lia).
Time Qed.
Time
Lemma fmap_zip_with_r (g : C \226\134\146 B) l k :
  (\226\136\128 x y, g (f x y) = y) \226\134\146 length k \226\137\164 length l \226\134\146 g <$> zip_with f l k = k.
Time Proof.
Time revert l.
Time (induction k; intros [| ? ?] ? ?; f_equal /=; auto with lia).
Time Qed.
Time Lemma zip_with_zip l k : zip_with f l k = curry f <$> zip l k.
Time Proof.
Time revert k.
Time by induction l; intros [| ? ?]; f_equal /=.
Time Qed.
Time Lemma zip_with_fst_snd lk : zip_with f lk.*1 lk.*2 = curry f <$> lk.
Time Proof.
Time by induction lk as [| []]; f_equal /=.
Time Qed.
Time
Lemma zip_with_replicate n x y :
  zip_with f (replicate n x) (replicate n y) = replicate n (f x y).
Time Proof.
Time by induction n; f_equal /=.
Time Qed.
Time
Lemma zip_with_replicate_l n x k :
  length k \226\137\164 n \226\134\146 zip_with f (replicate n x) k = f x <$> k.
Time Proof.
Time revert n.
Time (induction k; intros [| ?] ?; f_equal /=; auto with lia).
Time Qed.
Time
Lemma zip_with_replicate_r n y l :
  length l \226\137\164 n \226\134\146 zip_with f l (replicate n y) = flip f y <$> l.
Time Proof.
Time revert n.
Time (induction l; intros [| ?] ?; f_equal /=; auto with lia).
Time Qed.
Time
Lemma zip_with_replicate_r_eq n y l :
  length l = n \226\134\146 zip_with f l (replicate n y) = flip f y <$> l.
Time Proof.
Time (intros; apply zip_with_replicate_r; lia).
Time Qed.
Time
Lemma zip_with_take n l k :
  take n (zip_with f l k) = zip_with f (take n l) (take n k).
Time Proof.
Time revert n k.
Time by induction l; intros [| ?] [| ? ?]; f_equal /=.
Time Qed.
Time
Lemma zip_with_drop n l k :
  drop n (zip_with f l k) = zip_with f (drop n l) (drop n k).
Time Proof.
Time revert n k.
Time (induction l; intros [] []; f_equal /=; auto using zip_with_nil_r).
Time Qed.
Time
Lemma zip_with_take_l n l k :
  length k \226\137\164 n \226\134\146 zip_with f (take n l) k = zip_with f l k.
Time Proof.
Time revert n k.
Time (induction l; intros [] [] ?; f_equal /=; auto with lia).
Time Qed.
Time
Lemma zip_with_take_r n l k :
  length l \226\137\164 n \226\134\146 zip_with f l (take n k) = zip_with f l k.
Time Proof.
Time revert n k.
Time (induction l; intros [] [] ?; f_equal /=; auto with lia).
Time Qed.
Time
Lemma Forall_zip_with_fst (P : A \226\134\146 Prop) (Q : C \226\134\146 Prop) 
  l k :
  Forall P l
  \226\134\146 Forall (\206\187 y, \226\136\128 x, P x \226\134\146 Q (f x y)) k \226\134\146 Forall Q (zip_with f l k).
Time Proof.
Time (intros Hl).
Time revert k.
Time (induction Hl; destruct 1; simpl in *; auto).
Time Qed.
Time
Lemma Forall_zip_with_snd (P : B \226\134\146 Prop) (Q : C \226\134\146 Prop) 
  l k :
  Forall (\206\187 x, \226\136\128 y, P y \226\134\146 Q (f x y)) l
  \226\134\146 Forall P k \226\134\146 Forall Q (zip_with f l k).
Time Proof.
Time (intros Hl).
Time revert k.
Time (induction Hl; destruct 1; simpl in *; auto).
Time Qed.
Time
Lemma elem_of_lookup_zip_with_1 l k (z : C) :
  z \226\136\136 zip_with f l k \226\134\146 \226\136\131 i x y, z = f x y \226\136\167 l !! i = Some x \226\136\167 k !! i = Some y.
Time Proof.
Time (intros [i Hin]%elem_of_list_lookup).
Time (rewrite lookup_zip_with in Hin).
Time (simplify_option_eq; naive_solver).
Time Qed.
Time
Lemma elem_of_lookup_zip_with_2 l k x y (z : C) i :
  l !! i = Some x \226\134\146 k !! i = Some y \226\134\146 f x y \226\136\136 zip_with f l k.
Time Proof.
Time (intros Hl Hk).
Time (rewrite elem_of_list_lookup).
Time exists i.
Time by rewrite lookup_zip_with, Hl, Hk.
Time Qed.
Time
Lemma elem_of_lookup_zip_with l k (z : C) :
  z \226\136\136 zip_with f l k
  \226\134\148 (\226\136\131 i x y, z = f x y \226\136\167 l !! i = Some x \226\136\167 k !! i = Some y).
Time Proof.
Time
naive_solver eauto using elem_of_lookup_zip_with_1, elem_of_lookup_zip_with_2.
Time Qed.
Time
Lemma elem_of_zip_with l k (z : C) :
  z \226\136\136 zip_with f l k \226\134\146 \226\136\131 x y, z = f x y \226\136\167 x \226\136\136 l \226\136\167 y \226\136\136 k.
Time Proof.
Time (intros ?%elem_of_lookup_zip_with).
Time naive_solver eauto using elem_of_list_lookup_2.
Time Qed.
Time End zip_with.
Time
Lemma zip_with_sublist_alter {A} {B} (f : A \226\134\146 B \226\134\146 A) 
  g l k i n l' k' :
  length l = length k
  \226\134\146 sublist_lookup i n l = Some l'
    \226\134\146 sublist_lookup i n k = Some k'
      \226\134\146 length (g l') = length k'
        \226\134\146 zip_with f (g l') k' = g (zip_with f l' k')
          \226\134\146 zip_with f (sublist_alter g i n l) k =
            sublist_alter g i n (zip_with f l k).
Time Proof.
Time (unfold sublist_lookup, sublist_alter).
Time (intros Hlen; rewrite Hlen).
Time (intros ? ? Hl' Hk').
Time simplify_option_eq.
Time
by
 rewrite !zip_with_app_l, !zip_with_drop, Hl', drop_drop, !zip_with_take,
  !take_length_le, Hk' by (rewrite ?drop_length; auto with lia).
Time Qed.
Time Section zip.
Time Context {A B : Type}.
Time Implicit Type l : list A.
Time Implicit Type k : list B.
Time Lemma fst_zip l k : length l \226\137\164 length k \226\134\146 (zip l k).*1 = l.
Time Proof.
Time by apply fmap_zip_with_l.
Time Qed.
Time Lemma snd_zip l k : length k \226\137\164 length l \226\134\146 (zip l k).*2 = k.
Time Proof.
Time by apply fmap_zip_with_r.
Time Qed.
Time Lemma zip_fst_snd (lk : list (A * B)) : zip lk.*1 lk.*2 = lk.
Time Proof.
Time by induction lk as [| []]; f_equal /=.
Time Qed.
Time
Lemma Forall2_fst P l1 l2 k1 k2 :
  length l2 = length k2
  \226\134\146 Forall2 P l1 k1 \226\134\146 Forall2 (\206\187 x y, P x.1 y.1) (zip l1 l2) (zip k1 k2).
Time Proof.
Time (rewrite <- Forall2_same_length).
Time (intros Hlk2 Hlk1).
Time revert l2 k2 Hlk2.
Time (induction Hlk1; intros ? ? [| ? ? ? ? ? ?]; simpl; auto).
Time Qed.
Time
Lemma Forall2_snd P l1 l2 k1 k2 :
  length l1 = length k1
  \226\134\146 Forall2 P l2 k2 \226\134\146 Forall2 (\206\187 x y, P x.2 y.2) (zip l1 l2) (zip k1 k2).
Time Proof.
Time (rewrite <- Forall2_same_length).
Time (intros Hlk1 Hlk2).
Time revert l1 k1 Hlk1.
Time (induction Hlk2; intros ? ? [| ? ? ? ? ? ?]; simpl; auto).
Time Qed.
Time Lemma elem_of_zip_l x1 x2 l k : (x1, x2) \226\136\136 zip l k \226\134\146 x1 \226\136\136 l.
Time Proof.
Time (intros ?%elem_of_zip_with).
Time naive_solver.
Time Qed.
Time Lemma elem_of_zip_r x1 x2 l k : (x1, x2) \226\136\136 zip l k \226\134\146 x2 \226\136\136 k.
Time Proof.
Time (intros ?%elem_of_zip_with).
Time naive_solver.
Time Qed.
Time End zip.
Time
Lemma elem_of_zipped_map {A} {B} (f : list A \226\134\146 list A \226\134\146 A \226\134\146 B) 
  l k x :
  x \226\136\136 zipped_map f l k
  \226\134\148 (\226\136\131 k' k'' y, k = k' ++ [y] ++ k'' \226\136\167 x = f (reverse k' ++ l) k'' y).
Time Proof.
Time split.
Time -
Time revert l.
Time (induction k as [| z k IH]; simpl; intros l; inversion_clear 1).
Time {
Time by eexists [],k,z.
Time }
Time (destruct (IH (z :: l)) as (k', (k'', (y, (->, ->)))); [ done |  ]).
Time eexists (z :: k'),k'',y.
Time by rewrite reverse_cons, <- (assoc_L (++)).
Time -
Time (intros (k', (k'', (y, (->, ->))))).
Time revert l.
Time (induction k' as [| z k' IH]; [ by left |  ]).
Time (intros l; right).
Time by rewrite reverse_cons, <- !(assoc_L (++)).
Time Qed.
Time Section zipped_list_ind.
Time Context {A} (P : list A \226\134\146 list A \226\134\146 Prop).
Time
Context (Pnil : \226\136\128 l, P l []) (Pcons : \226\136\128 l k x, P (x :: l) k \226\134\146 P l (x :: k)).
Time
Fixpoint zipped_list_ind l k : P l k :=
  match k with
  | [] => Pnil _
  | x :: k => Pcons _ _ _ (zipped_list_ind (x :: l) k)
  end.
Time End zipped_list_ind.
Time
Lemma zipped_Forall_app {A} (P : list A \226\134\146 list A \226\134\146 A \226\134\146 Prop) 
  l k k' : zipped_Forall P l (k ++ k') \226\134\146 zipped_Forall P (reverse k ++ l) k'.
Time Proof.
Time revert l.
Time (induction k as [| x k IH]; simpl; [ done |  ]).
Time (inversion_clear 1).
Time (rewrite reverse_cons, <- (assoc_L (++))).
Time by apply IH.
Time Qed.
Time
Lemma TCForall_Forall {A} (P : A \226\134\146 Prop) xs : TCForall P xs \226\134\148 Forall P xs.
Time Proof.
Time (split; induction 1; constructor; auto).
Time Qed.
Time
Instance TCForall_app  {A} (P : A \226\134\146 Prop) xs ys:
 (TCForall P xs \226\134\146 TCForall P ys \226\134\146 TCForall P (xs ++ ys)).
Time Proof.
Time (rewrite !TCForall_Forall).
Time (apply Forall_app_2).
Time Qed.
Time Section positives_flatten_unflatten.
Time #[local]Open Scope positive_scope.
Time
Lemma positives_flatten_go_app xs acc :
  positives_flatten_go xs acc = acc ++ positives_flatten_go xs 1.
Time Proof.
Time revert acc.
Time (induction xs as [| x xs IH]; intros acc; simpl).
Time -
Time reflexivity.
Time -
Time (rewrite IH).
Time (rewrite (IH (6 ++ _))).
Time (rewrite 2!(assoc_L (++))).
Time reflexivity.
Time Qed.
Time
Lemma positives_unflatten_go_app p suffix xs acc :
  positives_unflatten_go (suffix ++ Preverse (Pdup p)) xs acc =
  positives_unflatten_go suffix xs (acc ++ p).
Time Proof.
Time revert suffix acc.
Time (induction p as [p IH| p IH| ]; intros acc suffix; simpl).
Time -
Time (rewrite 2!Preverse_xI).
Time (rewrite 2!(assoc_L (++))).
Time (rewrite IH).
Time reflexivity.
Time -
Time (rewrite 2!Preverse_xO).
Time (rewrite 2!(assoc_L (++))).
Time (rewrite IH).
Time reflexivity.
Time -
Time reflexivity.
Time Qed.
Time
Lemma positives_unflatten_flatten_go suffix xs acc :
  positives_unflatten_go (suffix ++ positives_flatten_go xs 1) acc 1 =
  positives_unflatten_go suffix (xs ++ acc) 1.
Time Proof.
Time revert suffix acc.
Time (induction xs as [| x xs IH]; intros suffix acc; simpl).
Time -
Time reflexivity.
Time -
Time (rewrite positives_flatten_go_app).
Time (rewrite (assoc_L (++))).
Time (rewrite IH).
Time (rewrite (assoc_L (++))).
Time (rewrite positives_unflatten_go_app).
Time (simpl).
Time (rewrite (left_id_L 1 (++))).
Time reflexivity.
Time Qed.
Time
Lemma positives_unflatten_flatten xs :
  positives_unflatten (positives_flatten xs) = Some xs.
Time Proof.
Time (unfold positives_flatten, positives_unflatten).
Time
replace (positives_flatten_go xs 1) with 1 ++ positives_flatten_go xs 1
 by apply (left_id_L 1 (++)).
Time (rewrite positives_unflatten_flatten_go).
Time (simpl).
Time (rewrite (right_id_L [] (++)%list)).
Time reflexivity.
Time Qed.
Time
Lemma positives_flatten_app xs ys :
  positives_flatten (xs ++ ys) = positives_flatten xs ++ positives_flatten ys.
Time Proof.
Time (unfold positives_flatten).
Time revert ys.
Time (induction xs as [| x xs IH]; intros ys; simpl).
Time -
Time (rewrite (left_id_L 1 (++))).
Time reflexivity.
Time -
Time (rewrite positives_flatten_go_app, (positives_flatten_go_app xs)).
Time (rewrite IH).
Time (rewrite (assoc_L (++))).
Time reflexivity.
Time Qed.
Time
Lemma positives_flatten_cons x xs :
  positives_flatten (x :: xs) =
  1~1~0 ++ Preverse (Pdup x) ++ positives_flatten xs.
Time Proof.
Time (change_no_check (x :: xs) with ([x] ++ xs)%list).
Time (rewrite positives_flatten_app).
Time (rewrite (assoc_L (++))).
Time reflexivity.
Time Qed.
Time
Lemma positives_flatten_suffix (l k : list positive) :
  l `suffix_of` k \226\134\146 \226\136\131 q, positives_flatten k = q ++ positives_flatten l.
Time Proof.
Time (intros [l' ->]).
Time exists (positives_flatten l').
Time (apply positives_flatten_app).
Time Qed.
Time
Lemma positives_flatten_suffix_eq p1 p2 (xs ys : list positive) :
  length xs = length ys
  \226\134\146 p1 ++ positives_flatten xs = p2 ++ positives_flatten ys \226\134\146 xs = ys.
Time Proof.
Time
(revert p1 p2 ys; induction xs as [| x xs IH]; intros p1 p2 [| y ys] ?;
  simplify_eq /=; auto).
Time (rewrite !positives_flatten_cons, !(assoc _); intros Hl).
Time (assert (xs = ys) as <- by eauto; clear IH H; f_equal).
Time (apply (inj (++positives_flatten xs)) in Hl).
Time (rewrite 2!Preverse_Pdup in Hl).
Time (apply (Pdup_suffix_eq _ _ p1 p2) in Hl).
Time by apply (inj Preverse).
Time Qed.
Time End positives_flatten_unflatten.
Time
Inductive rlist (A : Type) :=
  | rnil : rlist A
  | rnode : A \226\134\146 rlist A
  | rapp : rlist A \226\134\146 rlist A \226\134\146 rlist A.
Time Arguments rnil {_} : assert.
Time Arguments rnode {_} _ : assert.
Time Arguments rapp {_} _ _ : assert.
Time Module rlist.
Time
Fixpoint to_list {A} (t : rlist A) : list A :=
  match t with
  | rnil => []
  | rnode l => [l]
  | rapp t1 t2 => to_list t1 ++ to_list t2
  end.
Time Notation env A:= (list (list A)) (only parsing).
Time
Definition eval {A} (E : env A) : rlist nat \226\134\146 list A :=
  fix go t :=
    match t with
    | rnil => []
    | rnode i => default [] (E !! i)
    | rapp t1 t2 => go t1 ++ go t2
    end.
Time Section quote_lookup.
Time Context {A : Type}.
Time Class QuoteLookup (E1 E2 : list A) (x : A) (i : nat) :={}.
Time #[global]
Instance quote_lookup_here  E x: (QuoteLookup (x :: E) (x :: E) x 0) := { }.
Time #[global]Instance quote_lookup_end  x: (QuoteLookup [] [x] x 0) := { }.
Time #[global]
Instance quote_lookup_further  E1 E2 x i y:
 (QuoteLookup E1 E2 x i \226\134\146 QuoteLookup (y :: E1) (y :: E2) x (S i)) |1000 := {
 }.
Time End quote_lookup.
Time Section quote.
Time Context {A : Type}.
Time Class Quote (E1 E2 : env A) (l : list A) (t : rlist nat) :={}.
Time #[global]Instance quote_nil : (Quote E1 E1 [] rnil) := { }.
Time #[global]
Instance quote_node  E1 E2 l i:
 (QuoteLookup E1 E2 l i \226\134\146 Quote E1 E2 l (rnode i)) |1000 := { }.
Time #[global]
Instance quote_cons  E1 E2 E3 x l i t:
 (QuoteLookup E1 E2 [x] i
  \226\134\146 Quote E2 E3 l t \226\134\146 Quote E1 E3 (x :: l) (rapp (rnode i) t)) := { }.
Time #[global]
Instance quote_app  E1 E2 E3 l1 l2 t1 t2:
 (Quote E1 E2 l1 t1 \226\134\146 Quote E2 E3 l2 t2 \226\134\146 Quote E1 E3 (l1 ++ l2) (rapp t1 t2))
 := { }.
Time End quote.
Time Section eval.
Time Context {A} (E : env A).
Time Lemma eval_alt t : eval E t = to_list t \226\137\171= default [] \226\136\152 (E!!).
Time Proof.
Time (induction t; csimpl).
Time -
Time done.
Time -
Time by rewrite (right_id_L [] (++)).
Time -
Time (rewrite bind_app).
Time by f_equal.
Time Qed.
Time Lemma eval_eq t1 t2 : to_list t1 = to_list t2 \226\134\146 eval E t1 = eval E t2.
Time Proof.
Time (intros Ht).
Time by rewrite !eval_alt, Ht.
Time Qed.
Time
Lemma eval_Permutation t1 t2 :
  to_list t1 \226\137\161\226\130\154 to_list t2 \226\134\146 eval E t1 \226\137\161\226\130\154 eval E t2.
Time Proof.
Time (intros Ht).
Time by rewrite !eval_alt, Ht.
Time Qed.
Time
Lemma eval_submseteq t1 t2 :
  to_list t1 \226\138\134+ to_list t2 \226\134\146 eval E t1 \226\138\134+ eval E t2.
Time Proof.
Time (intros Ht).
Time by rewrite !eval_alt, Ht.
Time Qed.
Time End eval.
Time End rlist.
Time
Ltac
 quote_Permutation :=
  match goal with
  | |- ?l1 \226\137\161\226\130\154 ?l2 =>
        match type of (_ : rlist.Quote [] _ l1 _)
        with
        | rlist.Quote _ ?E2 _ ?t1 =>
            match type of (_ : rlist.Quote E2 _ l2 _)
            with
            | rlist.Quote _ ?E3 _ ?t2 =>
                change_no_check (rlist.eval E3 t1 \226\137\161\226\130\154 rlist.eval E3 t2)
            end
        end
  end.
Time
Ltac
 solve_Permutation :=
  quote_Permutation; apply rlist.eval_Permutation;
   apply (bool_decide_unpack _); by vm_compute.
Time
Ltac
 quote_submseteq :=
  match goal with
  | |- ?l1 \226\138\134+ ?l2 =>
        match type of (_ : rlist.Quote [] _ l1 _)
        with
        | rlist.Quote _ ?E2 _ ?t1 =>
            match type of (_ : rlist.Quote E2 _ l2 _)
            with
            | rlist.Quote _ ?E3 _ ?t2 =>
                change_no_check (rlist.eval E3 t1 \226\138\134+ rlist.eval E3 t2)
            end
        end
  end.
Time
Ltac
 solve_submseteq :=
  quote_submseteq; apply rlist.eval_submseteq; apply (bool_decide_unpack _);
   by vm_compute.
Time
Ltac
 decompose_elem_of_list :=
  repeat
   match goal with
   | H:?x \226\136\136 [] |- _ => by destruct (not_elem_of_nil x)
   | H:_ \226\136\136 _ :: _ |- _ => apply elem_of_cons in H; destruct H
   | H:_ \226\136\136 _ ++ _ |- _ => apply elem_of_app in H; destruct H
   end.
Time
Ltac
 solve_length :=
  simplify_eq /=; repeat rewrite fmap_length || rewrite app_length;
   repeat
    match goal with
    | H:_ =@{ list _} _ |- _ => apply (f_equal length) in H
    | H:Forall2 _ _ _ |- _ => apply Forall2_length in H
    | H:context [ length (_ <$> _) ] |- _ => rewrite fmap_length in H
    end; done || congruence.
Time
Ltac
 simplify_list_eq ::=
  repeat
   match goal with
   | _ =>
       progress simplify_eq /=
   | H:[?x] !! ?i = Some ?y
     |- _ =>
         destruct i;
          [ change_no_check (Some x = Some y) in H | discriminate ]
   | H:_ <$> _ = [] |- _ => apply fmap_nil_inv in H
   | H:[] = _ <$> _ |- _ => symmetry in H; apply fmap_nil_inv in H
   | H:zip_with _ _ _ = [] |- _ => apply zip_with_nil_inv in H; destruct H
   | H:[] = zip_with _ _ _ |- _ => symmetry in H
   | |- context [ (_ ++ _) ++ _ ] => rewrite <- (assoc_L (++))
   | H:context [ (_ ++ _) ++ _ ] |- _ => rewrite <- (assoc_L (++)) in H
   | H:context [ _ <$> _ ++ _ ] |- _ => rewrite fmap_app in H
   | |- context [ _ <$> _ ++ _ ] => rewrite fmap_app
   | |- context [ _ ++ [] ] => rewrite (right_id_L [] (++))
   | H:context [ _ ++ [] ] |- _ => rewrite (right_id_L [] (++)) in H
   | |- context [ take _ (_ <$> _) ] => rewrite <- fmap_take
   | H:context [ take _ (_ <$> _) ] |- _ => rewrite <- fmap_take in H
   | |- context [ drop _ (_ <$> _) ] => rewrite <- fmap_drop
   | H:context [ drop _ (_ <$> _) ] |- _ => rewrite <- fmap_drop in H
   | H:_ ++ _ = _ ++ _
     |- _ =>
         repeat
          rewrite <- app_comm_cons in H || rewrite <- (assoc_L (++)) in H;
          apply app_inj_1 in H; [ destruct H | solve_length ]
   | H:_ ++ _ = _ ++ _
     |- _ =>
         repeat rewrite app_comm_cons in H || rewrite (assoc_L (++)) in H;
          apply app_inj_2 in H; [ destruct H | solve_length ]
   | |- context [ zip_with _ (_ ++ _) (_ ++ _) ] =>
         rewrite zip_with_app by solve_length
   | |- context [ take _ (_ ++ _) ] => rewrite take_app_alt by solve_length
   | |- context [ drop _ (_ ++ _) ] => rewrite drop_app_alt by solve_length
   | H:context [ zip_with _ (_ ++ _) (_ ++ _) ]
     |- _ => rewrite zip_with_app in H by solve_length
   | H:context [ take _ (_ ++ _) ]
     |- _ => rewrite take_app_alt in H by solve_length
   | H:context [ drop _ (_ ++ _) ]
     |- _ => rewrite drop_app_alt in H by solve_length
   | H:?l !! ?i = _, H2:context [ (_ <$> ?l) !! ?i ]
     |- _ => rewrite list_lookup_fmap, H in H2
   end.
Time
Ltac
 decompose_Forall_hyps :=
  repeat
   match goal with
   | H:Forall _ [] |- _ => clear H
   | H:Forall _ (_ :: _) |- _ => rewrite Forall_cons in H; destruct H
   | H:Forall _ (_ ++ _) |- _ => rewrite Forall_app in H; destruct H
   | H:Forall2 _ [] [] |- _ => clear H
   | H:Forall2 _ (_ :: _) [] |- _ => destruct (Forall2_cons_nil_inv _ _ _ H)
   | H:Forall2 _ [] (_ :: _) |- _ => destruct (Forall2_nil_cons_inv _ _ _ H)
   | H:Forall2 _ [] ?k |- _ => apply Forall2_nil_inv_l in H
   | H:Forall2 _ ?l [] |- _ => apply Forall2_nil_inv_r in H
   | H:Forall2 _ (_ :: _) (_ :: _)
     |- _ => apply Forall2_cons_inv in H; destruct H
   | H:Forall2 _ (_ :: _) ?k
     |- _ =>
         let k_hd := fresh k "_hd" in
         let k_tl := fresh k "_tl" in
         apply Forall2_cons_inv_l in H;
          destruct H as (k_hd, (k_tl, (?, (?, ->)))); rename k_tl into k
   | H:Forall2 _ ?l (_ :: _)
     |- _ =>
         let l_hd := fresh l "_hd" in
         let l_tl := fresh l "_tl" in
         apply Forall2_cons_inv_r in H;
          destruct H as (l_hd, (l_tl, (?, (?, ->)))); rename l_tl into l
   | H:Forall2 _ (_ ++ _) ?k
     |- _ =>
         let k1 := fresh k "_1" in
         let k2 := fresh k "_2" in
         apply Forall2_app_inv_l in H; destruct H as (k1, (k2, (?, (?, ->))))
   | H:Forall2 _ ?l (_ ++ _)
     |- _ =>
         let l1 := fresh l "_1" in
         let l2 := fresh l "_2" in
         apply Forall2_app_inv_r in H; destruct H as (l1, (l2, (?, (?, ->))))
   | _ =>
       progress simplify_eq /=
   | H:Forall3 _ _ (_ :: _) _
     |- _ =>
         apply Forall3_cons_inv_m in H;
          destruct H as (?, (?, (?, (?, (?, (?, (?, ?)))))))
   | H:Forall2 _ (_ :: _) ?k
     |- _ =>
         apply Forall2_cons_inv_l in H; destruct H as (?, (?, (?, (?, ?))))
   | H:Forall2 _ ?l (_ :: _)
     |- _ =>
         apply Forall2_cons_inv_r in H; destruct H as (?, (?, (?, (?, ?))))
   | H:Forall2 _ (_ ++ _) (_ ++ _)
     |- _ => apply Forall2_app_inv in H; [ destruct H | solve_length ]
   | H:Forall2 _ ?l (_ ++ _)
     |- _ =>
         apply Forall2_app_inv_r in H; destruct H as (?, (?, (?, (?, ?))))
   | H:Forall2 _ (_ ++ _) ?k
     |- _ =>
         apply Forall2_app_inv_l in H; destruct H as (?, (?, (?, (?, ?))))
   | H:Forall3 _ _ (_ ++ _) _
     |- _ =>
         apply Forall3_app_inv_m in H;
          destruct H as (?, (?, (?, (?, (?, (?, (?, ?)))))))
   | H:Forall ?P ?l, H1:?l !! _ = Some ?x
     |- _ =>
         unless P x by auto using Forall_app_2, Forall_nil_2;
          (let E := fresh in
           assert (E : P x) by apply (Forall_lookup_1 P _ _ _ H H1);
            lazy beta in E)
   | H:Forall2 ?P ?l ?k
     |- _ =>
         match goal with
         | H1:l !! ?i = Some ?x, H2:k !! ?i = Some ?y
           |- _ =>
               unless P x y by done;
                (let E := fresh in
                 assert (E : P x y) by by
                  apply (Forall2_lookup_lr P l k i x y); 
                  lazy beta in E)
         | H1:l !! ?i = Some ?x
           |- _ =>
               try match goal with
                   | _:k !! i = Some _ |- _ => fail 2
                   end;
                destruct (Forall2_lookup_l P _ _ _ _ H H1) as (?, (?, ?))
         | H2:k !! ?i = Some ?y
           |- _ =>
               try match goal with
                   | _:l !! i = Some _ |- _ => fail 2
                   end;
                destruct (Forall2_lookup_r P _ _ _ _ H H2) as (?, (?, ?))
         end
   | H:Forall3 ?P ?l ?l' ?k
     |- _ =>
         lazymatch goal with
         | H1:l !! ?i = Some ?x, H2:l' !! ?i = Some ?y, H3:k !! ?i = Some ?z
           |- _ =>
               unless P x y z by done;
                (let E := fresh in
                 assert (E : P x y z) by by
                  apply (Forall3_lookup_lmr P l l' k i x y z); 
                  lazy beta in E)
         | H1:l !! _ = Some ?x
           |- _ =>
               destruct (Forall3_lookup_l P _ _ _ _ _ H H1)
                as (?, (?, (?, (?, ?))))
         | H2:l' !! _ = Some ?y
           |- _ =>
               destruct (Forall3_lookup_m P _ _ _ _ _ H H2)
                as (?, (?, (?, (?, ?))))
         | H3:k !! _ = Some ?z
           |- _ =>
               destruct (Forall3_lookup_r P _ _ _ _ _ H H3)
                as (?, (?, (?, (?, ?))))
         end
   end.
Time
Ltac
 list_simplifier :=
  simplify_eq /=;
   repeat
    match goal with
    | _ => progress decompose_Forall_hyps
    | _ =>
        progress simplify_list_eq
    | H:_ <$> _ = _ :: _
      |- _ => apply fmap_cons_inv in H; destruct H as (?, (?, (?, (?, ?))))
    | H:_ :: _ = _ <$> _ |- _ => symmetry in H
    | H:_ <$> _ = _ ++ _
      |- _ => apply fmap_app_inv in H; destruct H as (?, (?, (?, (?, ?))))
    | H:_ ++ _ = _ <$> _ |- _ => symmetry in H
    | H:zip_with _ _ _ = _ :: _
      |- _ =>
          apply zip_with_cons_inv in H;
           destruct H as (?, (?, (?, (?, (?, (?, (?, ?)))))))
    | H:_ :: _ = zip_with _ _ _ |- _ => symmetry in H
    | H:zip_with _ _ _ = _ ++ _
      |- _ =>
          apply zip_with_app_inv in H;
           destruct H as (?, (?, (?, (?, (?, (?, (?, (?, ?))))))))
    | H:_ ++ _ = zip_with _ _ _ |- _ => symmetry in H
    end.
Time
Ltac
 decompose_Forall :=
  repeat
   match goal with
   | |- Forall _ _ => by apply Forall_true
   | |- Forall _ [] => constructor
   | |- Forall _ (_ :: _) => constructor
   | |- Forall _ (_ ++ _) => apply Forall_app_2
   | |- Forall _ (_ <$> _) => apply Forall_fmap
   | |- Forall _ (_ \226\137\171= _) => apply Forall_bind
   | |- Forall2 _ _ _ => apply Forall_Forall2
   | |- Forall2 _ [] [] => constructor
   | |- Forall2 _ (_ :: _) (_ :: _) => constructor
   | |- Forall2 _ (_ ++ _) (_ ++ _) => first
     [ apply Forall2_app; [ by decompose_Forall |  ]
     | apply Forall2_app; [  | by decompose_Forall ] ]
   | |- Forall2 _ (_ <$> _) _ => apply Forall2_fmap_l
   | |- Forall2 _ _ (_ <$> _) => apply Forall2_fmap_r
   | _ =>
       progress decompose_Forall_hyps
   | H:Forall _ (_ <$> _) |- _ => rewrite Forall_fmap in H
   | H:Forall _ (_ \226\137\171= _) |- _ => rewrite Forall_bind in H
   | |- Forall _ _ =>
         apply Forall_lookup_2; intros ? ? ?; progress decompose_Forall_hyps
   | |- Forall2 _ _ _ =>
         apply Forall2_same_length_lookup_2; [ solve_length |  ];
          intros ? ? ? ? ?; progress decompose_Forall_hyps
   end.
Time
Ltac
 simplify_suffix :=
  repeat
   match goal with
   | H:suffix (_ :: _) _ |- _ => destruct (suffix_cons_not _ _ H)
   | H:suffix (_ :: _) [] |- _ => apply suffix_nil_inv in H
   | H:suffix (_ ++ _) (_ ++ _) |- _ => apply suffix_app_inv in H
   | H:suffix (_ :: _) (_ :: _)
     |- _ => destruct (suffix_cons_inv _ _ _ _ H); clear H
   | H:suffix ?x ?x |- _ => clear H
   | H:suffix ?x (_ :: ?x) |- _ => clear H
   | H:suffix ?x (_ ++ ?x) |- _ => clear H
   | _ => progress simplify_eq /=
   end.
Time
Ltac
 solve_suffix := by intuition
 repeat
  match goal with
  | _ => done
  | _ =>
      progress simplify_suffix
  | |- suffix [] _ => apply suffix_nil
  | |- suffix _ _ => reflexivity
  | |- suffix _ (_ :: _) => apply suffix_cons_r
  | |- suffix _ (_ ++ _) => apply suffix_app_r
  | H:suffix _ _ \226\134\146 False |- _ => destruct H
  end.

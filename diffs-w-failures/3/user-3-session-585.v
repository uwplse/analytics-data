Time From stdpp Require Import numbers.
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
Time Class NatCancel (m n m' n' : nat) :=
         nat_cancel : m' + n = m + n'.
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
Time Hint Mode NatCancel ! ! - -: typeclass_instances.
Time Module nat_cancel.
Time Class NatCancelL (m n m' n' : nat) :=
         nat_cancel_l : m' + n = m + n'.
Time Hint Mode NatCancelL ! ! - -: typeclass_instances.
Time
Class NatCancelR (m n m' n' : nat) :=
    nat_cancel_r : NatCancelL m n m' n'.
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
Time Hint Mode NatCancelR ! ! - -: typeclass_instances.
Time Existing Instance nat_cancel_r |100.
Time
Instance nat_cancel_start  m n m' n':
 (TCNoBackTrack (NatCancelL m n m' n') \226\134\146 NatCancel m n m' n').
Time Proof.
Time by intros [?].
Time Qed.
Time Class MakeNatS (n1 n2 m : nat) :=
         make_nat_S : m = n1 + n2.
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
Time Instance make_nat_S_0_l  n: (MakeNatS 0 n n).
Time Proof.
Time done.
Time Qed.
Time Instance make_nat_S_1  n: (MakeNatS 1 n (S n)).
Time Proof.
Time done.
Time Qed.
Time Class MakeNatPlus (n1 n2 m : nat) :=
         make_nat_plus : m = n1 + n2.
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
Time Instance make_nat_plus_0_l  n: (MakeNatPlus 0 n n).
Time Proof.
Time done.
Time Qed.
Time Instance make_nat_plus_0_r  n: (MakeNatPlus n 0 n).
Time Proof.
Time (unfold MakeNatPlus).
Time by rewrite Nat.add_0_r.
Time Qed.
Time
Instance make_nat_plus_default  n1 n2: (MakeNatPlus n1 n2 (n1 + n2)) |100.
Time Proof.
Time done.
Time Qed.
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
Time Instance nat_cancel_leaf_here  m: (NatCancelR m m 0 0) |0.
Time Proof.
Time by unfold NatCancelR, NatCancelL.
Time Qed.
Time Instance nat_cancel_leaf_else  m n: (NatCancelR m n m n) |100.
Time Proof.
Time by unfold NatCancelR.
Time Qed.
Time
Instance nat_cancel_leaf_plus  m m' m'' n1 n2 n1' 
 n2' n1'n2':
 (NatCancelR m n1 m' n1'
  \226\134\146 NatCancelR m' n2 m'' n2'
    \226\134\146 MakeNatPlus n1' n2' n1'n2' \226\134\146 NatCancelR m (n1 + n2) m'' n1'n2') |2.
Time Proof.
Time (unfold NatCancelR, NatCancelL, MakeNatPlus).
Time lia.
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
Time Qed.
Time Defined.
Time
Fixpoint remove_dups (l : list A) : list A :=
  match l with
  | [] => []
  | x :: l =>
      if decide_rel (\226\136\136) x l then remove_dups l else x :: remove_dups l
  end.
Time
Instance nat_cancel_leaf_S_here  m n m' n':
 (NatCancelR m n m' n' \226\134\146 NatCancelR (S m) (S n) m' n') |3.
Time Proof.
Time (unfold NatCancelR, NatCancelL).
Time lia.
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
Instance nat_cancel_leaf_S_else  m n m' n':
 (NatCancelR m n m' n' \226\134\146 NatCancelR m (S n) m' (S n')) |4.
Time Proof.
Time (unfold NatCancelR, NatCancelL).
Time lia.
Time Qed.
Time
Instance nat_cancel_S_both  m n m' n':
 (NatCancelL m n m' n' \226\134\146 NatCancelL (S m) (S n) m' n') |1.
Time Proof.
Time (unfold NatCancelL).
Time lia.
Time Qed.
Time
Instance nat_cancel_plus  m1 m2 m1' m2' m1'm2' n n' 
 n'':
 (NatCancelL m1 n m1' n'
  \226\134\146 NatCancelL m2 n' m2' n''
    \226\134\146 MakeNatPlus m1' m2' m1'm2' \226\134\146 NatCancelL (m1 + m2) n m1'm2' n'') |2.
Time Proof.
Time (unfold NatCancelL, MakeNatPlus).
Time lia.
Time Qed.
Time Qed.
Time
Instance nat_cancel_S  m m' m'' Sm' n n' n'':
 (NatCancelL m n m' n'
  \226\134\146 NatCancelR 1 n' m'' n''
    \226\134\146 MakeNatS m'' m' Sm' \226\134\146 NatCancelL (S m) n Sm' n'') |3.
Time Proof.
Time (unfold NatCancelR, NatCancelL, MakeNatS).
Time lia.
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
Time End nat_cancel.
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
Time End find.
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
Time
Lemma replicate_plus n m x :
  replicate (n + m) x = replicate n x ++ replicate m x.
Time Proof.
Time (induction n; f_equal /=; auto).
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

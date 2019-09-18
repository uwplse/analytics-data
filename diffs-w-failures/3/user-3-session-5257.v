Require Import POCS.
Require Import POCS.
Require Import POCS.
Require Import POCS.
Require Import TwoDiskAPI.
Require Import Common.OneDiskAPI.
Module ReplicatedDisk (td: TwoDiskAPI)<: OneDiskAPI.
Definition read (a : addr) : proc block :=
  mv0 <- td.read d0 a;
  match mv0 with
  | Working v => Ret v
  | Failed =>
      mv2 <- td.read d1 a;
      match mv2 with
      | Working v => Ret v
      | Failed => Ret block0
      end
  end.
Definition read_stub (a : addr) : proc block := Ret block0.
Require Import AtomicPairAPI.
Require Import Common.OneDiskAPI.
Import ListNotations.
Module AtomicPair (d: OneDiskAPI)<: AtomicPairAPI.
Definition ptr_a : addr := 0.
Definition data0a : addr := 1.
Definition data1a : addr := 2.
Definition data0b : addr := 3.
Definition data1b : addr := 4.
Require Import VariablesAPI.
Require Import StatDbAPI.
Module StatDB (v: VarsAPI)<: StatDbAPI.
Import ListNotations.
Definition add (v : nat) : proc unit :=
  sum <- v.read VarSum;
  count <- v.read VarCount;
  _ <- v.write VarSum (sum + v); _ <- v.write VarCount (count + 1); Ret tt.
Definition mean : proc (option nat) :=
  count <- v.read VarCount;
  (if count == 0
   then Ret None
   else sum <- v.read VarSum; Ret (Some (sum / count))).
Require Import OneDiskAPI.
Require Import NbdAPI.
Require Import NbdImpl.
Module nbd:=  NbdImpl.
Module NBDServer (d: OneDiskAPI).
Fixpoint read (off : nat) n : proc (bytes (n * blockbytes)) :=
  match n with
  | 0 => Ret bnull
  | S n => b <- d.read off; rest <- read (off + 1) n; Ret (bappend b rest)
  end.
Definition write (a : addr) (b : block) : proc unit :=
  _ <- td.write d0 a b; _ <- td.write d1 a b; Ret tt.
Definition size : proc nat :=
  msz <- td.size d0;
  match msz with
  | Working sz => Ret sz
  | Failed =>
      msz <- td.size d1;
      match msz with
      | Working sz => Ret sz
      | Failed => Ret 0
      end
  end.
Definition sizeInit : proc (option nat) :=
  sz1 <- td.size d0;
  sz2 <- td.size d1;
  match sz1 with
  | Working sz1 =>
      match sz2 with
      | Working sz2 => if sz1 == sz2 then Ret (Some sz1) else Ret None
      | Failed => Ret (Some sz1)
      end
  | Failed =>
      match sz2 with
      | Working sz2 => Ret (Some sz2)
      | Failed => Ret None
      end
  end.
Fixpoint init_at (a : nat) : proc unit :=
  match a with
  | 0 => Ret tt
  | S a => _ <- td.write d0 a block0; _ <- td.write d1 a block0; init_at a
  end.
Definition init' : proc InitResult :=
  size <- sizeInit;
  match size with
  | Some sz => _ <- init_at sz; Ret Initialized
  | None => Ret InitFailed
  end.
Ltac addr_lia := progress unfold ptr_a, data0a, data1a, data0b, data1b; lia.
Hint Extern 2 (_ <> _ :> addr) => addr_lia: core.
Hint Extern 2 (_ < _) => addr_lia: core.
Definition get : proc (block * block) :=
  ptr <- d.read ptr_a;
  (if ptr == block0
   then b0 <- d.read data0a; b1 <- d.read data1a; Ret (b0, b1)
   else b0 <- d.read data0b; b1 <- d.read data1b; Ret (b0, b1)).
Definition put (p : block * block) : proc unit :=
  ptr <- d.read ptr_a;
  (if ptr == block0
   then
    _ <- d.write data0b (fst p);
    _ <- d.write data1b (snd p); _ <- d.write ptr_a block1; Ret tt
   else
    _ <- d.write data0a (fst p);
    _ <- d.write data1a (snd p); _ <- d.write ptr_a block0; Ret tt).
Definition init' : proc InitResult :=
  len <- d.size;
  (if len == 5
   then
    _ <- d.write ptr_a block0;
    _ <- d.write data0a block0; _ <- d.write data1a block0; Ret Initialized
   else Ret InitFailed).
Definition init := then_init d.init init'.
Definition recover : proc unit := d.recover.
Definition atomic_pair_abstraction (ds : OneDiskAPI.State)
  (ps : AtomicPairAPI.State) : Prop :=
  diskSize ds = 5 /\
  (diskGet ds ptr_a ?|= eq block0 ->
   diskGet ds data0a = Some (fst ps) /\ diskGet ds data1a = Some (snd ps)) /\
  (forall b,
   diskGet ds ptr_a ?|= eq b ->
   b <> block0 ->
   diskGet ds data0b = Some (fst ps) /\ diskGet ds data1b = Some (snd ps)).
Definition init' : proc InitResult :=
  _ <- v.write VarCount 0; _ <- v.write VarSum 0; Ret Initialized.
Definition init := then_init v.init init'.
Definition recover : proc unit := v.recover.
Definition statdb_abstraction (vars_state : VariablesAPI.State)
  (statdb_state : StatDbAPI.State) : Prop :=
  StateCount vars_state = length statdb_state /\
  StateSum vars_state = fold_right plus 0 statdb_state.
Definition abstr : Abstraction StatDbAPI.State :=
  abstraction_compose v.abstr {| abstraction := statdb_abstraction |}.
Example abstr_1_ok : statdb_abstraction (VariablesAPI.mkState 0 0) nil.
Proof.
(unfold statdb_abstraction; auto).
Qed.
Example abstr_2_nok : ~ statdb_abstraction (VariablesAPI.mkState 1 0) nil.
Proof.
(unfold statdb_abstraction; simpl).
lia.
Fixpoint write (off : nat) (bl : list (bytes blockbytes)) : 
proc unit :=
  match bl with
  | nil => Ret tt
  | b :: bl' => _ <- d.write off b; write (off + 1) bl'
  end.
Theorem read_ok :
  forall n off,
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' => state' = state /\ read_match state off n r;
     recovered := fun _ state' => state' = state |}) 
    (read off n) d.recover d.abstr.
Proof.
(induction n; intros).
-
(simpl).
step_proc.
-
(simpl read).
Definition init := then_init td.init init'.
Theorem exists_tuple2 :
  forall A B (P : A * B -> Prop), (exists a b, P (a, b)) -> exists p, P p.
Proof.
(intros).
(repeat deex; eauto).
Qed.
Tactic Notation "eexist_tuple" ident(a) ident(b) :=
 (match goal with
  | |- exists _ : ?aT * ?bT, _ =>
        let a := fresh a in
        let b := fresh b in
        evar ( a : aT ); evar ( b : bT ); exists (a, b); subst a; subst b
  end).
Ltac
 simplify :=
  repeat
   match goal with
   | |- forall _, _ => intros
   | _ => deex
   | _ =>
       destruct_tuple
   | u:unit |- _ => destruct u
   | |- _ /\ _ => split; [ solve [ auto ] |  ]
   | |- _ /\ _ => split; [  | solve [ auto ] ]
   | |- exists _ : disk * (disk -> Prop), _ => eexist_tuple d F
   | |- exists _ : disk * disk, _ => eexist_tuple d_0 d_1
   | |- exists _ : disk * _, _ => apply exists_tuple2
   | _ => progress simpl in *
   | _ => progress safe_intuition
   | _ => progress subst
   | _ => progress autorewrite with upd in *
   end.
Ltac
 finish :=
  repeat
   match goal with
   | _ => solve_false
   | _ => congruence
   | _ => solve [ intuition eauto; try congruence ]
   | _ =>
       descend; intuition eauto;
        lazymatch goal with
        | |- proc_spec _ _ _ _ => idtac
        | _ => fail
        end
   end.
Ltac step := step_proc; simplify; finish.
Theorem both_disks_not_missing :
  forall state : TwoDiskBaseAPI.State,
  disk0 state ?|= missing -> disk1 state ?|= missing -> False.
Proof.
(destruct state; unfold missing; simpl; intuition auto).
Example abstraction_ok_ptr0 :
  forall b1 b2 b3 b4,
  atomic_pair_abstraction [block0; b1; b2; b3; b4] (b1, b2).
Proof.
(unfold atomic_pair_abstraction; intuition auto).
Qed.
Qed.
Hint Resolve both_disks_not_missing: false.
Theorem missing0_implies_any :
  forall (state : TwoDiskBaseAPI.State) P,
  disk0 state ?|= missing -> disk0 state ?|= P.
Proof.
(destruct state; unfold missing; simpl; intuition auto).
Qed.
Theorem missing1_implies_any :
  forall (state : TwoDiskBaseAPI.State) P,
  disk1 state ?|= missing -> disk1 state ?|= P.
Proof.
(destruct state; unfold missing; simpl; intuition auto).
Example abstraction_ok_ptr1 :
  forall b1 b2 b3 b4,
  atomic_pair_abstraction [block1; b1; b2; b3; b4] (b3, b4).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
Qed.
Qed.
Example abstr_3_ok : statdb_abstraction (VariablesAPI.mkState 2 3) [1; 2].
Proof.
(unfold statdb_abstraction; simpl).
lia.
Qed.
Hint Resolve missing0_implies_any: core.
Hint Resolve missing1_implies_any: core.
Theorem read_int_ok :
  forall a,
  proc_spec
    (fun d state =>
     {|
     pre := disk0 state ?|= eq d /\ disk1 state ?|= eq d;
     post := fun r state' =>
             diskGet d a =?= r /\
             disk0 state' ?|= eq d /\ disk1 state' ?|= eq d;
     recovered := fun _ state' =>
                  disk0 state' ?|= eq d /\ disk1 state' ?|= eq d |}) 
    (read a) td.recover td.abstr.
Proof.
(unfold read).
step.
Example abstraction_ok_ptr_same :
  forall b b1 b2, atomic_pair_abstraction [b; b1; b2; b1; b2] (b1, b2).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
Qed.
Example abstraction_nok_size :
  forall b1 b2, ~ atomic_pair_abstraction [] (b1, b2).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
Qed.
lia.
Theorem init_ok : init_abstraction init recover abstr inited.
Proof.
(eapply then_init_compose; eauto).
(unfold init').
(step_proc_basic; intros).
exists tt.
(simpl; intuition idtac).
(step_proc_basic; intros).
exists tt.
(simpl; intuition idtac).
(step_proc_basic; intros).
{
eauto.
}
(simpl in *; intuition subst).
exists nil.
(unfold statdb_abstraction, inited).
intuition auto.
Qed.
Qed.
Example abstraction_nok_size2 :
  forall b1 b2, ~ atomic_pair_abstraction [block0; block1] (b1, b2).
Theorem add_ok : forall v, proc_spec (add_spec v) (add v) recover abstr.
Proof.
(unfold add).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc_basic; intros).
(destruct a'; simpl in *; intuition idtac).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
lia.
(exists tt; simpl; intuition idtac).
(step_proc_basic; intros).
(exists tt; simpl; intuition idtac).
Qed.
(step_proc_basic; intros).
(exists tt; simpl; intuition idtac).
(step_proc_basic; intros).
(exists tt; simpl; intuition idtac).
(step_proc_basic; intros).
{
eauto.
}
(simpl in *; intuition subst).
Example abstraction_nok_size3 :
  forall b1 b2,
  ~ atomic_pair_abstraction [block0; block1; block0; block1] (b1, b2).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
{
(eexists; intuition auto).
lia.
(unfold statdb_abstraction in *; simpl in *).
intuition lia.
step_proc.
Qed.
Example abstraction_ptr0_invert :
  forall b1 b2 b3 b4 v1 v2,
  atomic_pair_abstraction [block0; b1; b2; b3; b4] (v1, v2) ->
  (v1, v2) = (b1, b2).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition).
congruence.
Qed.
Definition abstr : Abstraction AtomicPairAPI.State :=
  abstraction_compose d.abstr {| abstraction := atomic_pair_abstraction |}.
Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 8, left associativity).
Opaque diskGet.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
}
(autounfold in *; intuition).
Qed.
(eapply then_init_compose; eauto).
step_proc.
(destruct (r == 5)).
-
step_proc.
step_proc.
step_proc.
Theorem mean_ok : proc_spec mean_spec mean recover abstr.
Proof.
(unfold mean).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc_basic; intros).
(destruct a'; simpl in *; intuition idtac).
step_proc.
exists (block0, block0).
(unfold atomic_pair_abstraction).
(autorewrite with upd; intuition auto).
(exists tt; simpl; intuition idtac).
(destruct (r == 0)).
-
(step_proc_basic; intros).
{
eauto.
}
(simpl in *; intuition subst).
(destruct r; step).
2: (autounfold in *; intuition).
(unfold statdb_abstraction in *).
(destruct s; intuition; simpl in *; try congruence).
(exists nil; intuition auto).
-
(step_proc_basic; intros).
(exists tt; simpl; intuition idtac).
(step_proc_basic; intros).
{
eauto.
}
(simpl in *; intuition subst).
2: (autounfold in *; intuition).
(unfold statdb_abstraction in *).
(destruct s; intuition).
(eexists; intuition auto).
step_proc.
(right; intuition congruence).
Qed.
Theorem recover_wipe : rec_wipe recover abstr no_crash.
Proof.
(unfold rec_wipe).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc_basic; intros).
{
eauto.
}
(destruct a; simpl in *).
intuition eauto.
Qed.
End StatDB.
Require Import VariablesImpl.
Module StatDBImpl:=  StatDB Vars.
Print Assumptions StatDBImpl.abstr_2_nok.
(destruct r; step).
Qed.
step_proc.
Hint Resolve read_int_ok: core.
Theorem write_int_ok :
  forall a b,
  proc_spec
    (fun d state =>
     {|
     pre := disk0 state ?|= eq d /\ disk1 state ?|= eq d;
     post := fun r state' =>
             r = tt /\
             disk0 state' ?|= eq (diskUpd d a b) /\
             disk1 state' ?|= eq (diskUpd d a b);
     recovered := fun _ state' =>
                  disk0 state' ?|= eq d /\ disk1 state' ?|= eq d \/
                  a < diskSize d /\
                  disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq d \/
                  disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq (diskUpd d a b) |}) 
    (write a b) td.recover td.abstr.
Proof.
(unfold write).
step.
(rewrite bsplit_bappend).
intuition subst; eauto.
(destruct (diskGet state off); simpl in *; intuition subst; eauto).
-
step_proc.
Qed.
(destruct r; step).
Theorem get_ok : proc_spec get_spec get recover abstr.
Proof.
(unfold get).
(apply spec_abstraction_compose; simpl).
step_proc.
(destruct a'; simpl in *; intuition; subst; eauto).
(destruct (r == block0)).
-
(step_proc; intuition eauto).
(step_proc; intuition eauto).
(step_proc; intuition eauto).
(unfold atomic_pair_abstraction in *; intuition).
exists s.
(destruct s; intuition).
replace (diskGet state data0a) in *.
replace (diskGet state data1a) in *.
(simpl in *; subst; auto).
-
(step_proc; intuition eauto).
(step_proc; intuition eauto).
(step_proc; intuition eauto).
(unfold atomic_pair_abstraction in *; intuition).
exists s.
(destruct s; intuition).
(specialize (H4 r); intuition).
replace (diskGet state data0b) in *.
replace (diskGet state data1b) in *.
(simpl in *; subst; auto).
Qed.
Lemma abstraction_update_b :
  forall state p0 p,
  atomic_pair_abstraction state p0 ->
  diskGet state ptr_a ?|= eq block0 ->
  atomic_pair_abstraction
    state [data0b |-> fst p] [data1b |-> snd p] [ptr_a |-> block1] p.
Proof.
(unfold atomic_pair_abstraction).
(intros).
(autorewrite with upd; intuition).
(descend; intuition eauto).
Print Assumptions StatDBImpl.abstr_3_ok.
Qed.
Lemma abstraction_update_a :
  forall state p0 b p,
  atomic_pair_abstraction state p0 ->
  diskGet state ptr_a ?|= eq b ->
  b <> block0 ->
  atomic_pair_abstraction
    state [data0a |-> fst p] [data1a |-> snd p] [ptr_a |-> block0] p.
Proof.
(unfold atomic_pair_abstraction).
(intros).
(autorewrite with upd; intuition).
Print Assumptions StatDBImpl.add_ok.
Qed.
Lemma diskGet_eq_values :
  forall d a b b',
  diskGet d a ?|= eq b -> diskGet d a ?|= eq b' -> a < diskSize d -> b = b'.
Proof.
(intros).
(destruct (diskGet d a) eqn:?; simpl in *).
congruence.
Print Assumptions StatDBImpl.mean_ok.

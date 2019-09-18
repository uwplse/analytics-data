Require Import POCS.
Require Import POCS.
Require Import POCS.
Require Import TwoDiskAPI.
Require Import TwoDiskAPI.
Require Import TwoDiskBaseAPI.
Module TwoDisk (b: TwoDiskBaseAPI)<: TwoDiskAPI.
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
Definition init := b.init.
Definition read := b.read.
Definition write := b.write.
Definition size := b.size.
Definition recover := b.recover.
Definition abstr := b.abstr.
Ltac
 inv_step :=
  match goal with
  | H:op_step _ _ _ _
    |- _ => inversion H; subst; clear H; repeat sigT_eq; safe_intuition
  end.
Ltac
 inv_bg :=
  match goal with
  | H:bg_failure _ _ |- _ => inversion H; subst; clear H
  end.
Theorem maybe_holds_stable :
  forall state state' F0 F1 i,
  get_disk (other i) state ?|= F0 ->
  get_disk i state ?|= F1 ->
  bg_failure state state' ->
  get_disk (other i) state' ?|= F0 /\ get_disk i state' ?|= F1.
Proof.
(intros).
(destruct i; inv_bg; simpl in *; eauto).
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
Definition init := then_init td.init init'.
Theorem exists_tuple2 :
  forall A B (P : A * B -> Prop), (exists a b, P (a, b)) -> exists p, P p.
Proof.
(intros).
(repeat deex; eauto).
Qed.
Require Import LogAPI.
Require Import Common.OneDiskAPI.
Import ListNotations.
Axiom (addr_to_block : addr -> proc block).
Axiom (block_to_addr : block -> addr).
Definition addr_to_block_spec State a :
  Specification unit block unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => state' = state /\ block_to_addr r = a;
  recovered := fun _ state' => state' = state |}.
Axiom
  (addr_to_block_ok :
     forall State a recover abstr,
     proc_spec (@addr_to_block_spec State a) (addr_to_block a) recover abstr).
Hint Resolve addr_to_block_ok: core.
Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 12, left associativity).
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
Qed.
Hint Resolve both_disks_not_missing: false.
Theorem missing0_implies_any :
  forall (state : TwoDiskBaseAPI.State) P,
  disk0 state ?|= missing -> disk0 state ?|= P.
Notation "d [ a |=> bs ]" := (diskUpds d a bs)
  (at level 12, left associativity).
Opaque diskGet.
Module Log (d: OneDiskAPI)<: LogAPI.
Definition len_addr : addr := 0.
Definition log_addr a : addr := S a.
Definition init' : proc InitResult :=
  size <- d.size;
  (if lt_dec size 1
   then Ret InitFailed
   else len0 <- addr_to_block 0; _ <- d.write len_addr len0; Ret Initialized).
Definition init := then_init d.init init'.
Definition get_len : proc addr := b <- d.read len_addr; Ret (block_to_addr b).
Definition get_at (a : addr) : proc block := d.read (log_addr a).
Fixpoint get_upto (a : addr) : proc (list block) :=
  match a with
  | 0 => Ret nil
  | S a => b <- get_at a; bs <- get_upto a; Ret (bs ++ [b])
  end.
Definition get : proc (list block) := len <- get_len; get_upto len.
Fixpoint append_at (a : addr) (bs : list block) : 
proc unit :=
  match bs with
  | [] => Ret tt
  | b :: bs => _ <- d.write (log_addr a) b; append_at (S a) bs
  end.
Definition append (bs : list block) : proc bool :=
  size <- d.size;
  len <- get_len;
  (if le_dec (1 + len + length bs) size
   then
    _ <- append_at len bs;
    len_b <- addr_to_block (len + length bs);
    _ <- d.write len_addr len_b; Ret true
   else Ret false).
Qed.
Proof.
(destruct state; unfold missing; simpl; intuition auto).
Qed.
Theorem missing1_implies_any :
  forall (state : TwoDiskBaseAPI.State) P,
  disk1 state ?|= missing -> disk1 state ?|= P.
Proof.
(destruct state; unfold missing; simpl; intuition auto).
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
Definition reset : proc unit :=
  len0 <- addr_to_block 0; d.write len_addr len0.
Definition recover : proc unit := d.recover.
Definition log_length_ok (d : disk) (log : list block) :=
  forall b, diskGet d len_addr =?= b -> block_to_addr b = length log.
Definition log_size_ok (d : disk) (log : list block) :=
  diskSize d >= 1 + length log.
Definition log_contents_ok (d : disk) (log : list block) :=
  forall a, a < length log -> diskGet d (log_addr a) =?= nth a log block0.
Definition log_abstraction (d : disk) (log : list block) : Prop :=
  log_length_ok d log /\ log_size_ok d log /\ log_contents_ok d log.
Theorem abstr_length_proj d log :
  log_abstraction d log -> log_length_ok d log.
Proof.
(unfold log_abstraction; intuition).
Qed.
Theorem abstr_size_proj d log : log_abstraction d log -> log_size_ok d log.
Proof.
(unfold log_abstraction; intuition).
Ltac
 cleanup :=
  repeat
   match goal with
   | |- forall _, _ => intros
   | |- _ /\ _ => split; [ solve [ eauto || congruence ] |  ]
   | |- _ /\ _ => split; [  | solve [ eauto || congruence ] ]
   | H:Working _ = Working _ |- _ => inversion H; subst; clear H
   | H:bg_failure _ _
     |- _ =>
         eapply maybe_holds_stable in H;
          [  | solve [ eauto ] | solve [ eauto ] ]; destruct_ands
   | H:_ ?|= eq _, H':_ = Some _
     |- _ => pose proof (holds_some_inv_eq _ H' H); clear H
   | H:?A * ?B |- _ => destruct H
   | H:DiskResult _ |- _ => destruct H
   | _ => deex
   | _ => destruct_tuple
   | _ => progress unfold pre_step in *
   | _ => progress autounfold in *
   | _ => progress simpl in *
   | _ => progress subst
   | _ => progress safe_intuition
   | _ => solve [ eauto ]
   | _ => congruence
   | _ =>
       inv_step
   | H:context [ match ?expr with
                 | _ => _
                 end ]
     |- _ => destruct expr eqn:?; [  | solve [ repeat cleanup ] ]
   | H:context [ match ?expr with
                 | _ => _
                 end ]
     |- _ => destruct expr eqn:?; [ solve [ repeat cleanup ] |  ]
   end.
Ltac
 prim :=
  intros; eapply proc_spec_weaken; [ eauto | unfold spec_impl ]; eexists;
   intuition eauto; cleanup; intuition eauto; cleanup.
Hint Resolve holds_in_some_eq: core.
Hint Resolve holds_in_none_eq: core.
Hint Resolve pred_missing: core.
Hint Unfold combined_step: core.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
eauto.
Proof.
(unfold read).
step.
Qed.
Theorem abstr_contents_proj d log :
  log_abstraction d log -> log_contents_ok d log.
Proof.
(unfold log_abstraction; intuition).
Qed.
Hint Resolve abstr_length_proj abstr_size_proj abstr_contents_proj: core.
Definition abstr : Abstraction State :=
  abstraction_compose d.abstr {| abstraction := log_abstraction |}.
Lemma diskGet_eq_values :
  forall d a b b',
  diskGet d a =?= b -> diskGet d a =?= b' -> a < diskSize d -> b = b'.
Proof.
(intros).
(destruct (diskGet d a) eqn:?; simpl in *).
-
congruence.
-
exfalso.
Qed.
Theorem read_ok :
  forall i a, proc_spec (read_spec i a) (read i a) recover abstr.
Proof.
(unshelve prim; eauto).
(apply disk_inbounds_not_none in Heqo; eauto).
Qed.
Ltac
 eq_values :=
  match goal with
  | H:diskGet ?d ?a =?= ?b, H':diskGet ?d ?a =?= ?b'
    |- _ =>
        assert (b = b') by
         (apply (@diskGet_eq_values d a b b'); try lia; auto); subst
  end.
Ltac step := step_proc.
Theorem log_length_ok_nil d b :
  diskGet d len_addr = Some b -> block_to_addr b = 0 -> log_length_ok d nil.
Proof.
(unfold log_length_ok; intros).
(rewrite H in *; simpl in *; subst).
auto.
Qed.
Theorem log_abstraction_nil d b :
  diskGet d len_addr = Some b -> block_to_addr b = 0 -> log_abstraction d nil.
Proof.
(unfold log_abstraction; intros).
intuition.
-
eauto using log_length_ok_nil.
-
(unfold log_size_ok).
(destruct d; simpl in *; [  | lia ]).
(assert (diskGet nil len_addr = None)).
{
(apply disk_oob_eq).
(simpl; lia).
}
congruence.
-
(unfold log_contents_ok; simpl in *; intuition).
(exfalso; lia).
Qed.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
(eapply then_init_compose; eauto).
step.
(destruct (lt_dec r 1)).
-
step.
-
step.
step.
step.
(exists nil; simpl).
(split; auto).
(apply log_abstraction_nil with (b := r0); eauto).
(unfold len_addr).
(autorewrite with upd; auto).
(destruct r; step).
Qed.
Theorem log_abstraction_length d bs :
  log_abstraction d bs -> log_length_ok d bs.
Proof.
(unfold log_abstraction; intuition).
Qed.
Hint Resolve log_abstraction_length: core.
Lemma abstr_get_len :
  forall (bs : list block) (state : State),
  log_length_ok state bs ->
  forall r : block,
  diskGet state len_addr =?= r -> block_to_addr r = length bs.
Proof.
(intros).
(unfold log_length_ok in H).
auto.
Qed.
Hint Resolve abstr_get_len: core.
Theorem get_len_ok :
  proc_spec
    (fun bs state =>
     {|
     pre := log_length_ok state bs /\ log_size_ok state bs;
     post := fun r state' => state' = state /\ r = length bs;
     recovered := fun _ state' => state' = state |}) get_len recover d.abstr.
Proof.
(unfold get_len; intros).
step.
step.
eauto.
Qed.
Hint Resolve get_len_ok: core.
Theorem get_len_abstr_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' => state' = state /\ r = length state;
     recovered := fun _ state' => state' = state |}) get_len recover abstr.
Proof.
(apply spec_abstraction_compose).
step.
(destruct a' as [[] bs]; simpl in *; intuition eauto).
step.
intuition eauto.
(exists bs; intuition eauto).
Qed.
Hint Resolve get_len_abstr_ok: core.
Theorem log_size_bound d bs a :
  log_size_ok d bs -> a < length bs -> log_addr a < diskSize d.
Proof.
(unfold log_size_ok, log_addr; intros; lia).
Qed.
Theorem get_at_ok a :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := a < length state;
     post := fun r state' => state' = state /\ nth a state block0 = r;
     recovered := fun _ state' => state' = state |}) 
    (get_at a) recover abstr.
Proof.
(unfold get_at; intros).
(apply spec_abstraction_compose).
(simpl).
step.
(destruct r; step).
(destruct a0 as [_ bs]; simpl in *; intuition eauto).
(exists bs; intuition eauto).
(unfold log_abstraction in H0; intuition).
(pose proof (H3 a); intuition).
(assert (log_addr a < diskSize state)).
{
eauto using log_size_bound.
}
eq_values.
Qed.
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
auto.
Qed.
Hint Resolve get_at_ok: core.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
(unfold rec_wipe; simpl; intros).
(apply spec_abstraction_compose).
step.
(destruct a as [_ bs]; simpl in *; intuition eauto).
Qed.
Hint Resolve recover_wipe: core.
Lemma firstn_one_more :
  forall (a : nat) (d : list block),
  S a <= length d -> firstn a d ++ [nth a d block0] = firstn (S a) d.
Proof.
(intros).
generalize dependent a.
(induction d; simpl; intros).
-
(exfalso; lia).
-
(destruct a0; simpl in *; auto).
(rewrite IHd by lia; auto).
Qed.
Opaque firstn.
Theorem get_upto_ok a :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := a <= length state;
     post := fun r state' => state' = state /\ r = firstn a state;
     recovered := fun _ state' => state' = state |}) 
    (get_upto a) recover abstr.
Proof.
(induction a; simpl).
-
step.
-
step.
step.
intuition eauto.
{
lia.
}
step.
auto using firstn_one_more.
Qed.
Hint Resolve get_upto_ok: core.
Theorem get_ok : proc_spec get_spec get recover abstr.
Proof.
(unfold get, get_spec; intros).
step.
step.
(rewrite firstn_all; auto).
Qed.
Theorem log_contents_ok_unchanged d bs a0 b :
  log_size_ok d bs ->
  log_contents_ok d bs ->
  a0 >= length bs -> log_contents_ok (diskUpd d (log_addr a0) b) bs.
Proof.
(unfold log_size_ok, log_contents_ok; intros).
(destruct (a == a0); subst; autorewrite with upd; auto).
Qed.
(destruct r; step).
Ltac
 destruct_all :=
  repeat
   match goal with
   | _ => solve
   [ auto ]
   | i:diskId |- _ => destruct i
   | |-
     context [ match ?s with
               | BothDisks _ _ => _
               | OnlyDisk0 _ => _
               | OnlyDisk1 _ => _
               end ] => destruct s
   | _ => simpl in *
   end.
Theorem write_ok :
  forall i a v, proc_spec (write_spec i a v) (write i a v) recover abstr.
Proof.
(unshelve prim; eauto; try (solve [ destruct_all ])).
Qed.
Theorem log_size_ok_shrink d bs bs' :
  log_size_ok d (bs ++ bs') -> log_size_ok d bs.
Proof.
(unfold log_size_ok; simpl).
(rewrite app_length; intros).
lia.
Qed.
Hint Resolve log_size_ok_shrink: core.
Hint Rewrite app_length : list.
Theorem log_contents_ok_prefix d bs bs' :
  log_contents_ok d (bs ++ bs') -> log_contents_ok d bs.
Proof.
(unfold log_contents_ok; intros).
specialize (H a).
(rewrite app_nth1 in H by lia).
(apply H).
(rewrite app_length; lia).
Qed.
Hint Resolve log_contents_ok_prefix: core.
Theorem log_contents_ok_append d bs b bs' :
  log_size_ok d (bs ++ b :: bs') ->
  log_contents_ok d bs ->
  log_contents_ok (diskUpd d (log_addr (length bs)) b) (bs ++ [b]).
Proof.
(unfold log_contents_ok; intros).
(assert (log_addr (length bs) < diskSize d)).
{
(unfold log_size_ok, log_addr, diskSize in *).
(rewrite app_length in *; simpl in *).
lia.
}
(destruct (a == length bs); subst; autorewrite with upd).
-
(simpl).
(rewrite app_nth2 by lia).
replace (length bs - length bs) with 0 by lia.
reflexivity.
-
(assert (a < length bs)).
{
(rewrite app_length in *; simpl in *; lia).
}
(rewrite app_nth1 by lia).
-
(descend; intuition eauto).
auto.
Qed.
Hint Resolve log_contents_ok_append: core.
Theorem append_at_ok a bs' :
  proc_spec
    (fun (bs : list block) state =>
     {|
     pre := a = length bs /\
            log_size_ok state (bs ++ bs') /\ log_contents_ok state bs;
     post := fun r state' =>
             diskGet state' len_addr = diskGet state len_addr /\
             diskSize state' = diskSize state /\
             log_size_ok state' (bs ++ bs') /\
             log_contents_ok state' (bs ++ bs');
     recovered := fun _ state' =>
                  diskGet state' len_addr = diskGet state len_addr /\
                  diskSize state' = diskSize state /\
                  log_contents_ok state' bs |}) (append_at a bs') recover
    d.abstr.
Proof.
generalize dependent a.
(induction bs'; simpl; intros).
-
step.
intuition eauto.
{
(destruct (lt_dec a (diskSize a'))).
-
eauto.
-
simplify.
(rewrite app_nil_r; auto).
-
step.
}
step.
(intuition eauto; autorewrite with upd; auto).
step.
(exists (a' ++ [a]); intuition eauto; autorewrite with upd list in *; eauto).
(destruct r; intuition eauto; simplify).
-
(destruct r; step).
Qed.
Hint Resolve write_int_ok: core.
Theorem size_int_ok :
  proc_spec
    (fun '(d_0, d_1) state =>
     {|
     pre := disk0 state ?|= eq d_0 /\
            disk1 state ?|= eq d_1 /\ diskSize d_0 = diskSize d_1;
     post := fun r state' =>
             r = diskSize d_0 /\
             r = diskSize d_1 /\
             disk0 state' ?|= eq d_0 /\ disk1 state' ?|= eq d_1;
     recovered := fun _ state' =>
                  disk0 state' ?|= eq d_0 /\ disk1 state' ?|= eq d_1 |}) size
    td.recover td.abstr.
Proof.
(unfold size).
step.
(destruct r; step).
(destruct r; step).
Qed.
Hint Resolve size_int_ok: core.
Definition equal_after a (d_0 d_1 : disk) :=
  diskSize d_0 = diskSize d_1 /\
  (forall a', a <= a' -> diskGet d_0 a' = diskGet d_1 a').
Theorem le_eq_or_S_le : forall n m, n <= m -> n = m \/ S n <= m /\ n <> m.
Proof.
(intros).
lia.
Qed.
Theorem equal_after_diskUpd :
  forall a d_0 d_1 b,
  equal_after (S a) d_0 d_1 ->
  equal_after a (diskUpd d_0 a b) (diskUpd d_1 a b).
Proof.
(unfold equal_after; intuition).
-
(autorewrite with upd; eauto).
-
(apply le_eq_or_S_le in H1; intuition subst).
{
(destruct (lt_dec a' (diskSize d_0)); autorewrite with upd).
+
(assert (a' < diskSize d_1) by congruence; autorewrite with upd; auto).
+
(assert (~ a' < diskSize d_1) by congruence; autorewrite with upd; auto).
}
(autorewrite with upd; eauto).
Qed.
Hint Resolve equal_after_diskUpd: core.
Theorem init_at_ok :
  forall a,
  proc_spec
    (fun '(d_0, d_1) state =>
     {|
     pre := disk0 state ?|= eq d_0 /\
            disk1 state ?|= eq d_1 /\ equal_after a d_0 d_1;
     post := fun _ state' =>
             exists d_0' d_1' : disk,
               disk0 state' ?|= eq d_0' /\
               disk1 state' ?|= eq d_1' /\ equal_after 0 d_0' d_1';
     recovered := fun _ state' => True |}) (init_at a) td.recover td.abstr.
Proof.
(induction a; simpl; intros).
-
step.
-
step.
step.
(destruct r; finish).
+
+
step.
(simpl; lia).
+
(unfold log_size_ok in *; simpl in *).
autorewrite with upd list in *.
(destruct r; simplify; finish).
(simpl in *; lia).
+
(unfold log_size_ok in *; simpl in *).
autorewrite with upd list in *.
+
step.
(simpl in *; lia).
+
(rewrite <- app_assoc in *; simpl in *; auto).
Qed.
Hint Resolve append_at_ok: core.
Theorem log_abstraction_preserved d bs d' :
  log_abstraction d bs ->
  diskGet d' len_addr = diskGet d len_addr ->
  diskSize d' = diskSize d -> log_contents_ok d' bs -> log_abstraction d' bs.
Proof.
(unfold log_abstraction, log_length_ok, log_size_ok; intuition).
-
replace (diskGet d' len_addr) in *.
auto.
-
congruence.
Qed.
Theorem abstr_length_sz_bound d bs :
  log_size_ok d bs -> len_addr < diskSize d.
Proof.
(unfold log_size_ok, len_addr, diskSize).
(intros; lia).
Qed.
Hint Resolve abstr_length_sz_bound: core.
Theorem log_contents_ok_len_change d bs b :
  log_size_ok d bs ->
  log_contents_ok d bs -> log_contents_ok (diskUpd d len_addr b) bs.
Proof.
(unfold log_size_ok, log_contents_ok, len_addr; intros).
(destruct (0 == log_addr a); autorewrite with upd).
(destruct r; finish).
Qed.
Hint Resolve init_at_ok: core.
Theorem sizeInit_ok :
  proc_spec
    (fun '(d_0, d_1) state =>
     {|
     pre := disk0 state ?|= eq d_0 /\ disk1 state ?|= eq d_1;
     post := fun r state' =>
             exists d_0' d_1',
               disk0 state' ?|= eq d_0' /\
               disk1 state' ?|= eq d_1' /\
               match r with
               | Some sz => diskSize d_0' = sz /\ diskSize d_1' = sz
               | None => True
               end;
     recovered := fun _ state' => True |}) sizeInit td.recover td.abstr.
Proof.
(unfold sizeInit).
step.
-
(exfalso; unfold log_addr in *; lia).
-
auto.
Qed.
Lemma log_abstraction_commit :
  forall bs bs' : list block,
  forall d' : State,
  log_size_ok d' (bs ++ bs') ->
  log_contents_ok d' (bs ++ bs') ->
  forall len_b : block,
  block_to_addr len_b = length bs + length bs' ->
  log_abstraction (diskUpd d' len_addr len_b) (bs ++ bs').
Proof.
(intros).
(assert (len_addr < diskSize d') by eauto).
(unfold log_abstraction; intuition).
-
(unfold log_length_ok in *; intros; autorewrite with upd list in *).
(destruct r).
-
step.
(simpl in *; intuition).
-
(unfold log_size_ok in *; autorewrite with upd list in *).
(destruct r).
+
(destruct (diskSize d_0 == v)).
*
step.
lia.
-
(apply log_contents_ok_len_change; auto).
Qed.
Hint Resolve log_abstraction_commit: core.
Theorem log_length_ok_unchanged d bs d' :
  log_length_ok d bs ->
  diskGet d' len_addr = diskGet d len_addr -> log_length_ok d' bs.
Proof.
(unfold log_length_ok; intros).
(rewrite H0 in *).
eauto.
Qed.
Hint Resolve log_length_ok_unchanged: core.
Theorem append_ok :
  forall v, proc_spec (append_spec v) (append v) recover abstr.
Proof.
(unfold append; intros).
(apply spec_abstraction_compose).
step.
(destruct a' as [[] bs]; simpl in *).
intuition eauto.
*
step.
step.
(exists bs; intuition eauto).
destruct matches.
-
step.
+
step.
(exists bs; intuition eauto).
-
step.
{
(unfold log_size_ok; autorewrite with list; auto).
}
{
(exists bs; intuition eauto using log_abstraction_preserved).
}
step.
intuition.
{
(exists bs; eauto using log_abstraction_preserved).
}
step.
intuition.
{
(exists bs; intuition eauto).
(unfold log_abstraction; intuition eauto).
(destruct r).
+
step.
}
{
(exists (bs ++ v); intuition).
}
step.
intuition.
{
(exists (bs ++ v); intuition eauto).
}
{
(exists (bs ++ v); intuition eauto).
}
-
step.
intuition eauto.
Qed.
+
step.
Theorem reset_ok : proc_spec reset_spec reset recover abstr.
Proof.
(unfold reset; intros).
(apply spec_abstraction_compose).
step.
Qed.
(destruct a' as [[] bs]; simpl in *).
intuition.
{
(exists bs; intuition eauto).
Hint Resolve sizeInit_ok: core.
}
step.
intuition eauto.
Theorem equal_after_0_to_eq :
  forall d_0 d_1, equal_after 0 d_0 d_1 -> d_0 = d_1.
Proof.
(unfold equal_after; intuition).
(eapply disk_ext_eq; intros).
(eapply H0; lia).
Qed.
Theorem equal_after_size :
  forall d_0 d_1,
  diskSize d_0 = diskSize d_1 -> equal_after (diskSize d_0) d_0 d_1.
Proof.
(unfold equal_after; intuition).
(assert (~ a' < diskSize d_0) by lia).
(assert (~ a' < diskSize d_1) by congruence).
(autorewrite with upd; eauto).
Qed.
Hint Resolve equal_after_size: core.
Hint Resolve equal_after_0_to_eq: core.
Theorem init'_ok :
  proc_spec
    (fun '(d_0, d_1) state =>
     {|
     pre := disk0 state ?|= eq d_0 /\ disk1 state ?|= eq d_1;
     post := fun r state' =>
             match r with
             | Initialized =>
                 exists d_0' d_1',
                   disk0 state' ?|= eq d_0' /\
                   disk1 state' ?|= eq d_1' /\ d_0' = d_1'
             | InitFailed => True
             end;
     recovered := fun _ state' => True |}) init' td.recover td.abstr.
{
(exists []; intuition eauto).
Proof.
(unfold init).
step.
(apply log_abstraction_nil with (b := r); auto).
(rewrite diskUpd_eq; eauto).
}
{
(exists []; intuition eauto).
(apply log_abstraction_nil with (b := r); auto).
(rewrite diskUpd_eq; eauto).
}
Qed.
End Log.
(descend; intuition eauto).
(destruct r; step).
step.
Qed.
Hint Resolve init'_ok: core.
Inductive RecStatus :=
  | Continue : _
  | RepairDoneOrFailed : _.
Definition fixup (a : addr) : proc RecStatus :=
  mv0 <- td.read d0 a;
  match mv0 with
  | Working v =>
      mv2 <- td.read d1 a;
      match mv2 with
      | Working v' =>
          if v == v'
          then Ret Continue
          else mu <- td.write d1 a v; Ret RepairDoneOrFailed
      | Failed => Ret RepairDoneOrFailed
      end
  | Failed => Ret RepairDoneOrFailed
  end.
Definition fixup_stub (a : addr) : proc RecStatus := Ret Continue.
Fixpoint recover_at (a : addr) : proc unit :=
  match a with
  | 0 => Ret tt
  | S n =>
      s <- fixup n;
      match s with
      | Continue => recover_at n
      | RepairDoneOrFailed => Ret tt
      end
  end.
Definition Recover : proc unit := sz <- size; _ <- recover_at sz; Ret tt.
Theorem if_lt_dec :
  forall A n m (a a' : A), n < m -> (if lt_dec n m then a else a') = a.
Proof.
(intros).
(destruct (lt_dec n m); auto).
Qed.
Theorem disks_eq_inbounds :
  forall (d : disk) a v v',
  a < diskSize d -> diskGet d a =?= v -> diskGet d a =?= v' -> v = v'.
Proof.
(intros).
(case_eq (diskGet d a); intros).
-
(rewrite H2 in *).
(simpl in *).
congruence.
-
exfalso.
(eapply disk_inbounds_not_none; eauto).
Qed.
Inductive DiskStatus :=
  | FullySynced : _
  | OutOfSync : forall (a : addr) (b : block), _.
Theorem diskUpd_maybe_same :
  forall (d : disk) a b, diskGet d a =?= b -> diskUpd d a b = d.
Proof.
(intros).
(destruct (diskGet d a) eqn:?; simpl in *; subst; autorewrite with upd; auto).
Qed.
Hint Rewrite diskUpd_maybe_same using (solve [ auto ]) : upd.
Hint Resolve PeanoNat.Nat.lt_neq: core.
Hint Resolve disks_eq_inbounds: core.
Theorem fixup_equal_ok :
  forall a,
  proc_spec
    (fun d state =>
     {|
     pre := a < diskSize d /\ disk0 state ?|= eq d /\ disk1 state ?|= eq d;
     post := fun r state' => disk0 state' ?|= eq d /\ disk1 state' ?|= eq d;
     recovered := fun _ state' =>
                  disk0 state' ?|= eq d /\ disk1 state' ?|= eq d |})
    (fixup a) td.recover td.abstr.
Proof.
(unfold fixup).
step.
(destruct r; step).
(destruct r; try step).
(destruct (v == v0); subst; try step).
Unshelve.
{
auto.
}
exact (fun _ => True).
Qed.
Theorem fixup_correct_addr_ok :
  forall a,
  proc_spec
    (fun '(d, b) state =>
     {|
     pre := a < diskSize d /\
            disk0 state ?|= eq (diskUpd d a b) /\ disk1 state ?|= eq d;
     post := fun r state' =>
             match r with
             | Continue =>
                 disk0 state' ?|= eq (diskUpd d a b) /\
                 disk1 state' ?|= eq (diskUpd d a b)
             | RepairDoneOrFailed =>
                 disk0 state' ?|= eq (diskUpd d a b) /\
                 disk1 state' ?|= eq (diskUpd d a b) \/
                 disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
             end;
     recovered := fun _ state' =>
                  disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq (diskUpd d a b) \/
                  disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq d \/
                  disk0 state' ?|= eq d /\ disk1 state' ?|= eq d |})
    (fixup a) td.recover td.abstr.
Proof.
(unfold fixup; intros).
step.
(destruct r; try step).
(destruct r; try step).
(destruct (b == v); subst; try step).
step.
(destruct r; simplify; finish).
Qed.
Theorem fixup_wrong_addr_ok :
  forall a,
  proc_spec
    (fun '(d, b, a') state =>
     {|
     pre := a < diskSize d /\
            a' < a /\
            disk0 state ?|= eq (diskUpd d a' b) /\ disk1 state ?|= eq d;
     post := fun r state' =>
             match r with
             | Continue =>
                 disk0 state' ?|= eq (diskUpd d a' b) /\
                 disk1 state' ?|= eq d
             | RepairDoneOrFailed =>
                 disk0 state' ?|= eq d /\ disk1 state' ?|= eq d \/
                 disk0 state' ?|= eq (diskUpd d a' b) /\
                 disk1 state' ?|= eq (diskUpd d a' b)
             end;
     recovered := fun _ state' =>
                  disk0 state' ?|= eq (diskUpd d a' b) /\
                  disk1 state' ?|= eq d \/
                  disk0 state' ?|= eq d /\ disk1 state' ?|= eq d |})
    (fixup a) td.recover td.abstr.
Proof.
(unfold fixup; intros).
step.
(destruct r; try step).
(destruct r; try step).
(destruct (v == v0); subst).
-
step.
-
step.
Unshelve.
{
auto.
}
exact (fun _ => True).
Qed.
Theorem fixup_ok :
  forall a,
  proc_spec
    (fun '(d, s) state =>
     {|
     pre := a < diskSize d /\
            match s with
            | FullySynced => disk0 state ?|= eq d /\ disk1 state ?|= eq d
            | OutOfSync a' b =>
                a' <= a /\
                disk0 state ?|= eq (diskUpd d a' b) /\ disk1 state ?|= eq d
            end;
     post := fun r state' =>
             match s with
             | FullySynced => disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
             | OutOfSync a' b =>
                 match r with
                 | Continue =>
                     a' < a /\
                     disk0 state' ?|= eq (diskUpd d a' b) /\
                     disk1 state' ?|= eq d \/
                     disk0 state' ?|= eq (diskUpd d a' b) /\
                     disk1 state' ?|= eq (diskUpd d a' b)
                 | RepairDoneOrFailed =>
                     disk0 state' ?|= eq d /\ disk1 state' ?|= eq d \/
                     disk0 state' ?|= eq (diskUpd d a' b) /\
                     disk1 state' ?|= eq (diskUpd d a' b)
                 end
             end;
     recovered := fun _ state' =>
                  match s with
                  | FullySynced =>
                      disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
                  | OutOfSync a' b =>
                      disk0 state' ?|= eq (diskUpd d a' b) /\
                      disk1 state' ?|= eq (diskUpd d a' b) \/
                      disk0 state' ?|= eq (diskUpd d a' b) /\
                      disk1 state' ?|= eq d \/
                      disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
                  end |}) (fixup a) td.recover td.abstr.
Proof.
(spec_intros; simplify).
(destruct s; intuition eauto).
-
(spec_case fixup_equal_ok; simplify; finish).
-
(apply PeanoNat.Nat.lt_eq_cases in H0; intuition).
+
(spec_case fixup_wrong_addr_ok; simplify; finish).
(repeat apply exists_tuple2; simpl).
exists d,b,a0.
(simplify; finish).
(destruct v; finish).
+
(spec_case fixup_correct_addr_ok; simplify; finish).
exists d,b.
(simplify; finish).
(destruct v; finish).
Restart.
(intros).
step_proc.
(destruct a'; simpl in *).
(destruct d0; intuition idtac).
-
(simplify; finish).
(destruct r; try step).
(destruct r; try step).
(destruct (v == v0); try step).
-
(simplify; finish).
(destruct r; try step).
(destruct r; try step).
(destruct (v == v0); try step).
+
(assert (a0 < a \/ a0 = a) by lia; intuition auto; simplify).
+
intuition eauto.
{
(destruct (a == a0); simplify; finish).
}
step.
(destruct r; try step).
*
(destruct (a == a0); simplify; finish).
*
(destruct (a == a0); simplify; finish).
Unshelve.
{
auto.
}
exact (fun _ => True).
Qed.
Theorem fixup_stub_ok :
  forall a,
  proc_spec
    (fun '(d, s) state =>
     {|
     pre := a < diskSize d /\
            match s with
            | FullySynced => True
            | OutOfSync a' b => True
            end;
     post := fun r state' =>
             match s with
             | FullySynced => True
             | OutOfSync a' b => True
             end;
     recovered := fun _ state' =>
                  match s with
                  | FullySynced => True
                  | OutOfSync a' b => True
                  end |}) (fixup a) td.recover td.abstr.
Proof.
Admitted.
Hint Resolve fixup_ok: core.
Theorem recover_at_ok :
  forall a,
  proc_spec
    (fun '(d, s) state =>
     {|
     pre := a <= diskSize d /\
            match s with
            | FullySynced => disk0 state ?|= eq d /\ disk1 state ?|= eq d
            | OutOfSync a' b =>
                a' < a /\
                disk0 state ?|= eq (diskUpd d a' b) /\ disk1 state ?|= eq d
            end;
     post := fun r state' =>
             match s with
             | FullySynced => disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
             | OutOfSync a' b =>
                 disk0 state' ?|= eq d /\ disk1 state' ?|= eq d \/
                 disk0 state' ?|= eq (diskUpd d a' b) /\
                 disk1 state' ?|= eq (diskUpd d a' b)
             end;
     recovered := fun _ state' =>
                  match s with
                  | FullySynced =>
                      disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
                  | OutOfSync a' b =>
                      disk0 state' ?|= eq d /\ disk1 state' ?|= eq d \/
                      disk0 state' ?|= eq (diskUpd d a' b) /\
                      disk1 state' ?|= eq d \/
                      disk0 state' ?|= eq (diskUpd d a' b) /\
                      disk1 state' ?|= eq (diskUpd d a' b)
                  end |}) (recover_at a) td.recover td.abstr.
Proof.
(induction a; simpl; intros).
-
step.
(destruct s; simplify).
-
step.
(destruct s; simplify).
+
(exists d,FullySynced; simplify; finish).
(destruct r; step).
(exists d,FullySynced; simplify; finish).
lia.
+
(exists d,(OutOfSync a0 b); simplify; finish).
intuition eauto.
{
lia.
}
{
(destruct r; step).
intuition.
*
(exists d,(OutOfSync a0 b); simplify; finish).
lia.
*
(exists (diskUpd d a0 b),FullySynced; simplify; finish).
lia.
}
Qed.
Theorem recover_stub_at_ok :
  forall a,
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' => True;
     recovered := fun _ state' => True |}) (recover_at a) td.recover td.abstr.
Proof.
Admitted.
Hint Resolve recover_at_ok: core.
Definition Recover_spec : Specification _ unit unit TwoDiskBaseAPI.State :=
  fun '(d, s) state =>
  {|
  pre := match s with
         | FullySynced => disk0 state ?|= eq d /\ disk1 state ?|= eq d
         | OutOfSync a b =>
             a < diskSize d /\
             disk0 state ?|= eq (diskUpd d a b) /\ disk1 state ?|= eq d
         end;
  post := fun (_ : unit) state' =>
          match s with
          | FullySynced => disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
          | OutOfSync a b =>
              disk0 state' ?|= eq d /\ disk1 state' ?|= eq d \/
              disk0 state' ?|= eq (diskUpd d a b) /\
              disk1 state' ?|= eq (diskUpd d a b)
          end;
  recovered := fun (_ : unit) state' =>
               match s with
               | FullySynced =>
                   disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
               | OutOfSync a b =>
                   disk0 state' ?|= eq d /\ disk1 state' ?|= eq d \/
                   disk0 state' ?|= eq (diskUpd d a b) /\
                   disk1 state' ?|= eq d \/
                   disk0 state' ?|= eq (diskUpd d a b) /\
                   disk1 state' ?|= eq (diskUpd d a b)
               end |}.
Definition Recover_spec_stub :
  Specification _ unit unit TwoDiskBaseAPI.State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun _ state' => True;
  recovered := fun _ state' => True |}.
Theorem Recover_rok : proc_spec Recover_spec Recover td.recover td.abstr.
Proof.
(unfold Recover, Recover_spec; intros).
(spec_intros; simplify).
(destruct s; simplify).
+
step.
step.
(exists d,FullySynced; simplify; finish).
step.
+
step.
intuition eauto.
{
simplify.
}
step.
(exists d,(OutOfSync a b); simplify; finish).
(destruct (le_dec (S a) (diskSize d0))).
step.
-
destruct_all.
Qed.
-
(rewrite diskUpd_oob_noop by lia).
destruct_all.
Theorem Recover_spec_idempotent : idempotent Recover_spec.
Proof.
(unfold idempotent).
(destruct a as [d st]).
(intuition; simplify).
(destruct st; intuition eauto).
Qed.
-
(exists d,FullySynced; finish).
-
(exists d,FullySynced; finish).
Theorem size_ok : forall i, proc_spec (size_spec i) (size i) recover abstr.
Proof.
unshelve prim.
-
(exists d,(OutOfSync a b); finish).
-
(exists (diskUpd d a b),FullySynced; finish).
Qed.
Theorem Recover_ok : proc_loopspec Recover_spec Recover td.recover td.abstr.
Proof.
(eapply idempotent_loopspec; simpl).
-
(apply Recover_rok).
-
(apply Recover_spec_idempotent).
Qed.
Hint Resolve Recover_ok: core.
Definition recover : proc unit := _ <- td.recover; Recover.
Definition rd_abstraction (state : TwoDiskBaseAPI.State)
  (d : OneDiskAPI.State) : Prop :=
  disk0 state ?|= eq d /\ disk1 state ?|= eq d.
Definition abstr : Abstraction OneDiskAPI.State :=
  abstraction_compose td.abstr {| abstraction := rd_abstraction |}.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
(intros).
(eapply then_init_compose; eauto).
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; intros).
(destruct state; simpl in *).
-
(exists (d_0, d_1); simpl; intuition eauto).
(unfold rd_abstraction).
(destruct v; repeat deex; eauto).
-
(exists (d_0, d_0); simpl; intuition eauto).
(unfold rd_abstraction).
(destruct v; repeat deex; eauto).
-
(exists (d_1, d_1); simpl; intuition eauto).
(unfold rd_abstraction).
(destruct v; repeat deex; eauto).
Qed.
Theorem read_ok : forall a, proc_spec (read_spec a) (read a) recover abstr.
Proof.
(intros).
(apply spec_abstraction_compose; simpl).
(eapply compose_recovery; eauto; simplify).
(unfold rd_abstraction in *; descend; intuition eauto).
(exists (state2, FullySynced); simplify; finish).
Qed.
Theorem write_ok :
  forall a v, proc_spec (write_spec a v) (write a v) recover abstr.
Proof.
(intros).
(apply spec_abstraction_compose; simpl).
(eapply compose_recovery; eauto; simplify).
rename state2 into d.
(unfold rd_abstraction in *; descend; intuition eauto).
-
(exists (d, FullySynced); simplify; intuition eauto).
eauto.
Qed.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
eauto.
Qed.
End TwoDisk.
-
(exists (d, OutOfSync a v); simplify; intuition eauto).
-
(exists (diskUpd d a v, FullySynced); simplify; intuition eauto).
Qed.
Theorem size_ok : proc_spec size_spec size recover abstr.
Proof.
(intros).
(apply spec_abstraction_compose; simpl).
(eapply compose_recovery; eauto).
(intros; apply exists_tuple2).
(destruct a; simpl in *).
rename s into d.
(unfold rd_abstraction in *; simplify).
(exists d,d; intuition eauto).
simplify.
(exists d,FullySynced; simplify; finish).
Qed.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
(eapply rec_wipe_compose; eauto; simpl).
(autounfold; unfold rd_abstraction, Recover_spec; simplify).
(exists state0',FullySynced; intuition eauto).
Qed.
End ReplicatedDisk.

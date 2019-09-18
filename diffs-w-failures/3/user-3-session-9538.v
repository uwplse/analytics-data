Require Import POCS.
Require Import POCS.
Require Import POCS.
Require Import Lab0.HeapVariablesAPI.
Module HeapExamples (vars: VarsAPI).
Definition swapXY : proc unit :=
  x <- vars.read VarX;
  y <- vars.read VarY; _ <- vars.write VarX y; _ <- vars.write VarY x; Ret tt.
Theorem swapXY_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' = mkState (StateY state) (StateX state) (StateZ state);
     recovered := fun _ state' => True |}) swapXY vars.recover vars.abstr.
Proof.
(unfold swapXY).
step_proc.
Require Import LogAPI.
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
step_proc.
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
Module Log (d: OneDiskAPI)<: LogAPI.
Fixpoint get_helper (start : addr) (count : addr) : 
proc (list block) :=
  match count with
  | O => Ret nil
  | S count' =>
      b <- d.read start; l <- get_helper (start + 1) count'; Ret ([b] ++ l)
  end.
Axiom
  (addr_to_block_ok :
     forall State a recover abstr,
     proc_spec (@addr_to_block_spec State a) (addr_to_block a) recover abstr).
Hint Resolve addr_to_block_ok: core.
Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 12, left associativity).
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
step_proc.
step_proc.
Definition get : proc (list block) :=
  len <- d.read 0; r <- get_helper 1 (block_to_addr len); Ret r.
Fixpoint append_helper (start : addr) (l : list block) : 
proc unit :=
  match l with
  | nil => Ret tt
  | b :: l' =>
      _ <- d.write start b; _ <- append_helper (start + 1) l'; Ret tt
  end.
Definition append (l : list block) : proc bool :=
  maxlen <- d.size;
  curlenb <- d.read 0;
  (let curlen := block_to_addr curlenb in
   let newlen := curlen + length l in
   if gt_dec (newlen + 1) maxlen
   then Ret false
   else
    _ <- append_helper (curlen + 1) l;
    newlenb <- addr_to_block newlen; _ <- d.write 0 newlenb; Ret true).
Definition reset : proc unit :=
  newlenb <- addr_to_block 0; _ <- d.write 0 newlenb; Ret tt.
Definition init' : proc InitResult :=
  len <- d.size;
  (if len == 0
   then Ret InitFailed
   else newlenb <- addr_to_block 0; _ <- d.write 0 newlenb; Ret Initialized).
Definition init := then_init d.init init'.
Definition recover : proc unit := d.recover.
Definition disk_matches_list (ds : OneDiskAPI.State) 
  (start : addr) (l : list block) : Prop :=
  diskGets ds start (length l) =??= l.
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
step_proc.
Qed.
Definition log_abstraction (ds : OneDiskAPI.State) 
  (ls : LogAPI.State) : Prop :=
  diskSize ds > length ls /\
  (exists lblk, diskGet ds 0 =?= lblk /\ block_to_addr lblk = length ls) /\
  disk_matches_list ds 1 ls.
Definition abstr : Abstraction LogAPI.State :=
  abstraction_compose d.abstr {| abstraction := log_abstraction |}.
Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 8, left associativity).
Notation "d [ a |=> bs ]" := (diskUpds d a bs)
  (at level 8, left associativity).
Opaque diskGet.
Theorem log_abstraction_nonempty :
  forall disk l, log_abstraction disk l -> diskSize disk <> 0.
Proof.
firstorder.
Qed.
Theorem abstr_size_proj d log : log_abstraction d log -> log_size_ok d log.
Proof.
(unfold log_abstraction; intuition).
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
Theorem log_length_ok_nil d b :
  diskGet d len_addr = Some b -> block_to_addr b = 0 -> log_length_ok d nil.
Proof.
(unfold log_length_ok; intros).
(rewrite H in *; simpl in *; subst).
Theorem swapXY_ok2 :
  proc_spec
    (fun '(x, y, z) state =>
     {|
     pre := StateX state = x /\ StateY state = y /\ StateZ state = z;
     post := fun r state' => state' = mkState y x z;
     recovered := fun _ state' => True |}) swapXY vars.recover vars.abstr.
Proof.
(unfold swapXY).
step_proc.
auto.
Qed.
Theorem log_abstraction_nil d b :
  diskGet d len_addr = Some b -> block_to_addr b = 0 -> log_abstraction d nil.
Proof.
(unfold log_abstraction; intros).
intuition.
(destruct a' as ((x, y), z); simplify).
step_proc.
-
eauto using log_length_ok_nil.
step_proc.
-
(unfold log_size_ok).
(destruct d; simpl in *; [  | lia ]).
step_proc.
step_proc.
Qed.
(assert (diskGet nil len_addr = None)).
{
(apply disk_oob_eq).
(simpl; lia).
Definition swapYZ : proc unit :=
  y <- vars.read VarY;
  z <- vars.read VarZ; _ <- vars.write VarY z; _ <- vars.write VarZ y; Ret tt.
Theorem swapYZ_ok :
  proc_spec
    (fun '(x, y, z) state =>
     {|
     pre := StateX state = x /\ StateY state = y /\ StateZ state = z;
     post := fun r state' => state' = mkState x z y;
     recovered := fun _ state' => True |}) swapYZ vars.recover vars.abstr.
}
congruence.
-
(unfold log_contents_ok; simpl in *; intuition).
(exfalso; lia).
Proof.
(unfold swapYZ).
step_proc.
(destruct a' as ((x, y), z); simplify).
Qed.
step_proc.
step_proc.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
(eapply then_init_compose; eauto).
step_proc.
(destruct (lt_dec r 1)).
-
step_proc.
step_proc.
step_proc.
Qed.
-
step_proc.
step_proc.
step_proc.
(exists nil; simpl).
(split; auto).
(eapply log_abstraction_nil; eauto).
(unfold len_addr).
(autorewrite with upd; auto).
Definition swapXZ : proc unit :=
  _ <- swapXY; _ <- swapYZ; _ <- swapXY; Ret tt.
Hint Resolve swapXY_ok2 swapYZ_ok: core.
Theorem swapXZ_ok :
  proc_spec
    (fun '(x, y, z) state =>
     {|
     pre := StateX state = x /\ StateY state = y /\ StateZ state = z;
     post := fun r state' => state' = mkState z y x;
     recovered := fun _ state' => True |}) swapXZ vars.recover vars.abstr.
Proof.
(unfold swapXZ).
(spec_intros; simplify).
(destruct a as ((x, y), z); simplify).
step_proc.
(eexists (_, _, _); simplify; intuition eauto).
Qed.
Hint Resolve log_abstraction_nonempty: core.
Theorem log_abstraction_init :
  forall disk b,
  block_to_addr b = 0 ->
  diskSize disk <> 0 -> log_abstraction disk [0 |-> b] nil.
Proof.
(unfold log_abstraction; intros).
(autorewrite with upd; simpl; intuition).
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
step_proc.
step_proc.
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
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; intros).
(destruct a as [[] bs]; simpl in *; intuition eauto).
(descend; intuition eauto).
step_proc.
Qed.
(eexists (_, _, _); simplify; intuition eauto).
Hint Resolve get_len_abstr_ok: core.
Theorem log_size_bound d bs a :
  log_size_ok d bs -> a < length bs -> log_addr a < diskSize d.
Proof.
(unfold log_size_ok, log_addr; intros; lia).
Qed.
Hint Resolve log_size_bound: core.
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
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; intros).
(destruct a0 as [_ bs]; simpl in *; intuition eauto).
(descend; intuition eauto).
(descend; intuition eauto).
-
lia.
-
(exists b; intuition).
-
(unfold disk_matches_list; simpl; auto).
(unfold log_abstraction in H0; intuition).
Qed.
Hint Resolve log_abstraction_init: core.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
(eapply then_init_compose; eauto).
step_proc.
(destruct (r == 0)).
(pose proof (H3 a); intuition).
-
step_proc.
-
step_proc.
step_proc.
(assert (v = nth a bs block0)).
{
(eapply diskGet_eq_values; eauto).
}
auto.
Qed.
step_proc.
(exists nil; intuition).
Qed.
Hint Resolve get_at_ok: core.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
(unfold rec_wipe; simpl; intros).
(apply spec_abstraction_compose).
step_proc.
(destruct a as [_ bs]; simpl in *; intuition eauto).
Theorem reset_ok : proc_spec reset_spec reset recover abstr.
Proof.
(unfold reset).
(apply spec_abstraction_compose; simpl).
step_proc.
(destruct a'; simpl in *; intuition; subst; eauto).
Qed.
Hint Resolve recover_wipe: core.
Lemma firstn_one_more :
  forall (a : nat) (d : list block),
  S a <= length d -> firstn a d ++ [nth a d block0] = firstn (S a) d.
step_proc.
(eexists (_, _, _); simplify; intuition eauto).
Proof.
(intros).
generalize dependent a.
(induction d; simpl; intros).
-
(exfalso; lia).
-
(destruct a0; simpl in *; auto).
(rewrite IHd by lia; auto).
(step_proc; intuition; subst; eauto).
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
step_proc.
-
step_proc.
step_proc.
{
(exists nil; intuition).
intuition eauto.
eauto.
}
(step_proc; intuition; subst; eauto).
{
lia.
}
step_proc.
auto using firstn_one_more.
Qed.
Hint Resolve get_upto_ok: core.
Theorem get_ok : proc_spec get_spec get recover abstr.
Proof.
(unfold get, get_spec; intros).
step_proc.
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; simpl; intuition).
{
(exists nil; intuition).
(descend; intuition eauto).
eauto.
}
{
(exists nil; intuition).
eauto.
(rewrite firstn_all; auto).
Qed.
}
Qed.
Theorem log_contents_ok_unchanged d bs a0 b :
  log_size_ok d bs ->
  log_contents_ok d bs ->
  a0 >= length bs -> log_contents_ok (diskUpd d (log_addr a0) b) bs.
Proof.
(unfold log_size_ok, log_contents_ok; intros).
(destruct (a == a0); subst; autorewrite with upd; auto).
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
Lemma disk_matches_state_next :
  forall disk start b blocks,
  disk_matches_list disk start (b :: blocks) ->
  disk_matches_list disk (start + 1) blocks.
Proof.
(unfold disk_matches_list; simpl; intuition).
Qed.
Hint Resolve disk_matches_state_next: core.
Lemma disk_matches_list_first :
  forall disk start b blocks,
  disk_matches_list disk start (b :: blocks) -> diskGet disk start =?= b.
Proof.
(unfold disk_matches_list; simpl; intuition).
Qed.
Definition get_helper_spec start count :
  Specification (list block) (list block) unit State :=
  fun (blocks : list block) state =>
  {|
  pre := disk_matches_list state start blocks /\
         start + count <= diskSize state /\ length blocks = count;
  post := fun r state' => r = blocks /\ state' = state;
  recovered := fun _ state' => state' = state |}.
Theorem get_helper_ok :
  forall count start,
  proc_spec (get_helper_spec start count) (get_helper start count) d.recover
    d.abstr.
Proof.
(induction count; simpl; intros).
-
step_proc.
(simpl in *; intuition).
(destruct a; simpl in *; auto; lia).
-
step_proc.
step_proc.
Qed.
step_proc.
(simpl in *; intuition).
(destruct a'; simpl in *; try lia).
Definition swapVars (v1 v2 : var) : proc unit :=
  v1_val <- vars.read v1;
  v2_val <- vars.read v2;
  _ <- vars.write v1 v2_val; _ <- vars.write v2 v1_val; Ret tt.
Theorem swapVars_ok v1 v2 :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             forall v,
             StateVar v state' =
             (if v == v1
              then StateVar v2 state
              else if v == v2 then StateVar v1 state else StateVar v state);
     recovered := fun _ state' => True |}) (swapVars v1 v2) vars.recover
    vars.abstr.
Proof.
(unfold swapVars).
step_proc.
step_proc.
step_proc.
step_proc.
step_proc.
(destruct v, v1, v2; intuition).
exists a'.
intuition eauto.
Qed.
{
lia.
}
step_proc.
(apply disk_matches_list_first in H).
eq_values.
Definition inc1 (v1 : var) : proc unit :=
  v <- vars.read v1; _ <- vars.write v1 (1 + v); Ret tt.
(simpl; auto).
Qed.
Theorem log_size_ok_shrink d bs bs' :
  log_size_ok d (bs ++ bs') -> log_size_ok d bs.
Proof.
(unfold log_size_ok; simpl).
(rewrite app_length; intros).
lia.
Definition inc1X_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' =
             mkState (1 + StateX state) (StateY state) (StateZ state);
     recovered := fun _ state' => True |}) (inc1 VarX) vars.recover
    vars.abstr.
Proof.
(unfold inc1).
step_proc.
step_proc.
step_proc.
Qed.
Qed.
Hint Resolve inc1X_ok: core.
Fixpoint increment (v1 : var) (n : nat) : proc unit :=
  match n with
  | 0 => Ret tt
  | S n' => _ <- inc1 v1; increment v1 n'
  end.
Theorem incrementX_ok n :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' =
             mkState (n + StateX state) (StateY state) (StateZ state);
     recovered := fun _ state' => True |}) (increment VarX n) vars.recover
    vars.abstr.
Proof.
(induction n; simpl).
-
step_proc.
(destruct state; auto).
-
step_proc.
Hint Resolve log_size_ok_shrink: core.
Hint Rewrite app_length : list.
Theorem log_contents_ok_prefix d bs bs' :
  log_contents_ok d (bs ++ bs') -> log_contents_ok d bs.
Proof.
(unfold log_contents_ok; intros).
specialize (H a).
(rewrite app_nth1 in H by lia).
step_proc.
(simpl).
auto.
Qed.
(apply H).
(rewrite app_length; lia).
f_equal.
lia.
Qed.
Hint Resolve get_helper_ok: core.
Theorem get_ok : proc_spec get_spec get recover abstr.
Proof.
(unfold get).
(apply spec_abstraction_compose; simpl).
step_proc.
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
End HeapExamples.
(destruct a'; simpl in *; intuition eauto).
lia.
}
(destruct (a == length bs); subst; autorewrite with upd).
step_proc.
exists s.
intuition eauto.
-
(unfold log_abstraction in H0; intuition).
-
(unfold log_abstraction in H0; intuition).
eq_values.
lia.
-
(unfold log_abstraction in H0; intuition).
eq_values.
auto.
-
(step_proc; intuition eauto).
Qed.
Definition append_helper_spec start blocks :
  Specification unit unit unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => r = tt /\ state' = diskUpds state start blocks;
  recovered := fun _ state' =>
               exists n, state' = diskUpds state start (firstn n blocks) |}.
Theorem append_helper_ok :
  forall blocks start,
  proc_spec (append_helper_spec start blocks) (append_helper start blocks)
    d.recover d.abstr.
Proof.
(induction blocks; simpl; intros).
-
(step_proc; intuition; subst; eauto).
(exists 0; simpl).
reflexivity.
-
(step_proc; intuition; subst; eauto).
-
(simpl).
(rewrite app_nth2 by lia).
{
(exists 0; simpl; auto).
}
{
(exists 1; simpl; auto).
}
{
(step_proc; intuition; subst; eauto).
replace (length bs - length bs) with 0 by lia.
{
(destruct H).
(exists (S n); simpl).
(autorewrite with upd; auto).
reflexivity.
-
(assert (a < length bs)).
{
(rewrite app_length in *; simpl in *; lia).
}
(rewrite app_nth1 by lia).
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
step_proc.
intuition eauto.
}
{
(step_proc; intuition; subst; eauto).
+
(autorewrite with upd; auto).
+
(exists (S (length blocks)); simpl).
(rewrite firstn_all).
(rewrite app_nil_r; auto).
-
step_proc.
(autorewrite with upd; auto).
(intuition eauto; autorewrite with upd; auto).
}
}
Qed.
Hint Resolve append_helper_ok: core.
Lemma disk_matches_list_update_blocks :
  forall blocks disk s base start,
  disk_matches_list disk base s ->
  start >= base + length s ->
  disk_matches_list (diskUpds disk start blocks) base s.
Proof.
(unfold disk_matches_list; intros).
autorewrite with upd.
auto.
Qed.
Lemma log_abstraction_pre_commit :
  forall disk s lenblk blocks,
  diskGet disk 0 =?= lenblk ->
  log_abstraction disk s ->
  log_abstraction (diskUpds disk (block_to_addr lenblk + 1) blocks) s.
Proof.
(unfold log_abstraction; intros).
(autorewrite with upd; intuition eauto).
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; simpl; intuition).
(exists (a' ++ [a]); intuition eauto; autorewrite with upd list in *; eauto).
eq_values.
(apply disk_matches_list_update_blocks; auto).
lia.
Qed.
Lemma disk_matches_list_oob :
  forall disk b l,
  disk_matches_list disk 1 l -> disk_matches_list disk [0 |-> b] 1 l.
Proof.
(unfold disk_matches_list; intros).
autorewrite with upd.
auto.
Qed.
Lemma log_abstraction_nop :
  forall disk s oldlen newlen,
  diskGet disk 0 =?= oldlen ->
  block_to_addr oldlen = block_to_addr newlen ->
  log_abstraction disk s -> log_abstraction disk [0 |-> newlen] s.
Proof.
(unfold log_abstraction; intuition).
-
autorewrite with upd.
auto.
-
autorewrite with upd.
eq_values.
exists newlen.
(simpl; intuition).
congruence.
-
(apply disk_matches_list_oob; auto).
Qed.
Lemma log_abstraction_post_commit :
  forall blocks disk s lenblk newlenblk,
  diskSize disk > length (s ++ blocks) ->
  diskGet disk 0 =?= lenblk ->
  block_to_addr newlenblk = block_to_addr lenblk + length blocks ->
  log_abstraction disk s ->
  log_abstraction
    (diskUpds disk (block_to_addr lenblk + 1) blocks) [0 |-> newlenblk]
    (s ++ blocks).
Proof.
(induction blocks; simpl; intuition).
-
(rewrite app_nil_r in *).
(eapply log_abstraction_nop; eauto).
lia.
-
(unfold log_abstraction in *; intuition).
+
autorewrite with upd.
lia.
+
eq_values.
exists newlenblk.
autorewrite with upd.
(rewrite app_length; simpl).
intuition.
lia.
+
autorewrite with upd.
+
(simpl; lia).
+
(unfold log_size_ok in *; simpl in *).
autorewrite with upd list in *.
(simpl in *; lia).
+
(unfold log_size_ok in *; simpl in *).
autorewrite with upd list in *.
(rewrite <- diskUpds_diskUpd_comm by lia).
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
(rewrite <- diskUpds_diskUpd_comm by lia).
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
(rewrite diskUpds_diskUpd_before).
(unfold disk_matches_list).
autorewrite with upd.
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
(rewrite app_length in *).
(rewrite diskGets_app).
eq_values.
Proof.
(intros).
(assert (len_addr < diskSize d') by eauto).
(unfold log_abstraction; intuition).
-
(unfold log_length_ok in *; intros; autorewrite with upd list in *).
replace (1 + length s) with block_to_addr lblk + 1 by lia.
(simpl in *; intuition).
-
(unfold log_size_ok in *; autorewrite with upd list in *).
autorewrite with upd.
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
step_proc.
(destruct a' as [[] bs]; simpl in *).
intuition eauto.
step_proc.
(descend; intuition eauto).
(apply maybe_eq_list_app).
*
assumption.
*
(apply maybe_eq_list_map_some).
Qed.
destruct matches.
-
step_proc.
(descend; intuition eauto).
Lemma log_abstraction_len :
  forall state s r,
  log_abstraction state s ->
  diskGet state 0 =?= r -> block_to_addr r = length s.
Proof.
(unfold log_abstraction; intuition).
eq_values.
{
(unfold log_size_ok; autorewrite with list; auto).
}
{
(exists bs; intuition eauto using log_abstraction_preserved).
auto.
Qed.
Theorem append_ok :
  forall v, proc_spec (append_spec v) (append v) recover abstr.
Proof.
(unfold append; intros).
(apply spec_abstraction_compose; simpl).
}
step_proc.
step_proc.
intuition.
(destruct a'; simpl in *; intuition; subst; eauto).
{
(exists bs; eauto using log_abstraction_preserved).
}
step_proc.
intuition.
(step_proc; intuition; subst; eauto).
{
(exists bs; intuition eauto).
(destruct (gt_dec (block_to_addr r + length v + 1) (diskSize state))).
-
(step_proc; intuition; subst; eauto).
(unfold log_abstraction; intuition eauto).
-
(step_proc; intuition; subst; eauto).
}
{
(exists (bs ++ v); intuition).
}
step_proc.
intuition.
{
(descend; intuition eauto).
}
{
(descend; intuition eauto).
}
-
step_proc.
{
(exists s; simpl; intuition).
intuition eauto.
(apply log_abstraction_pre_commit; auto).
}
(step_proc; intuition; subst; eauto).
Qed.
{
(exists s; simpl; intuition).
Theorem reset_ok : proc_spec reset_spec reset recover abstr.
Proof.
(unfold reset; intros).
(apply spec_abstraction_compose).
step_proc.
(destruct a' as [[] bs]; simpl in *).
intuition.
(apply log_abstraction_pre_commit; auto).
}
(step_proc; intuition; subst; eauto).
{
(descend; intuition eauto).
}
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; simpl; intuition).
(descend; intuition eauto).
{
(exists s; simpl; intuition).
{
(descend; intuition eauto).
(eapply log_abstraction_nil; eauto).
(rewrite diskUpd_eq; eauto).
}
{
(descend; intuition eauto).
(apply log_abstraction_pre_commit; auto).
}
{
(exists (s ++ v); simpl; intuition).
(eapply log_abstraction_nil; eauto).
(rewrite diskUpd_eq; eauto).
}
Qed.
(apply log_abstraction_post_commit; auto).
End Log.
(erewrite log_abstraction_len in * by eauto).
(rewrite app_length).
lia.
}
{
(step_proc; intuition; subst; eauto).
{
(exists (s ++ v); simpl; intuition).
(apply log_abstraction_post_commit; auto).
(erewrite log_abstraction_len in * by eauto).
(rewrite app_length).
lia.
}
{
(exists (s ++ v); simpl; intuition).
(apply log_abstraction_post_commit; auto).
(erewrite log_abstraction_len in * by eauto).
(rewrite app_length).
lia.
}
}
Qed.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
(unfold rec_wipe).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc; intros).
eauto.
(destruct a; simpl in *).
(autounfold in *; intuition; subst; eauto).
Qed.
End Log.

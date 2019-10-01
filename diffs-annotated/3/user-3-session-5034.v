Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqMcpdIP"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import POCS.
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
Module Log (d: OneDiskAPI)<: LogAPI.
Fixpoint get_helper (start : addr) (count : addr) : 
proc (list block) :=
  match count with
  | O => Ret nil
  | S count' =>
      b <- d.read start; l <- get_helper (start + 1) count'; Ret ([b] ++ l)
  end.
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
Hint Resolve log_abstraction_nonempty: core.
Theorem log_abstraction_init :
  forall disk b,
  block_to_addr b = 0 ->
  diskSize disk <> 0 -> log_abstraction disk [0 |-> b] nil.
Proof.
(unfold log_abstraction; intros).
(autorewrite with upd; simpl; intuition).
-
lia.
-
(exists b; intuition).
-
(unfold disk_matches_list; simpl; auto).
Qed.
Hint Resolve log_abstraction_init: core.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
(eapply then_init_compose; eauto).
step_proc.
(destruct (r == 0)).
-
step_proc.
-
step_proc.
step_proc.
step_proc.
(exists nil; intuition).
Qed.
Theorem reset_ok : proc_spec reset_spec reset recover abstr.
Proof.
(unfold reset).
(apply spec_abstraction_compose; simpl).
step_proc.
(destruct a'; simpl in *; intuition; subst; eauto).
(step_proc; intuition; subst; eauto).
{
(step_proc; intuition; subst; eauto).
{
(step_proc; intuition; subst; eauto).
+
(autorewrite with upd; auto).
+
(exists (S (length blocks)); simpl).
(rewrite firstn_all).
(autorewrite with upd; auto).
}
(destruct H).
(exists (S n); simpl).
(autorewrite with upd; auto).
}
{
(exists 0; simpl; auto).
}
{
(exists 1; simpl; auto).
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

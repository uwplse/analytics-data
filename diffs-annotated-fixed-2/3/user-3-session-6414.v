Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqC9Uqvm"
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
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqB5MAsu"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqXvoZpF"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
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
Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 8, left associativity).
Notation "d [ a |=> bs ]" := (diskUpds d a bs)
  (at level 8, left associativity).
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
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqYiLt1m"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqy2ao4W"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
   then _ <- append_at len bs; Ret true
   else Ret false).
Definition reset : proc unit :=
  len0 <- addr_to_block 0; d.write len_addr len0.
Definition recover : proc unit := Ret tt.
Definition log_length_ok (d : disk) (log : list block) :=
  exists b, diskGet d 0 =?= b /\ block_to_addr b = length log.
Definition log_abstraction (d : disk) (log : list block) : Prop :=
  log_length_ok d log /\
  (forall a, a < length log -> diskGet d (log_addr a) =?= nth a log block0).
Definition abstr : Abstraction State :=
  abstraction_compose d.abstr {| abstraction := log_abstraction |}.
Theorem log_length_ok_nil d b :
  diskGet d 0 = Some b -> block_to_addr b = 0 -> log_length_ok d nil.
Proof.
(unfold log_length_ok; intros).
(rewrite H; simpl; eauto).
Qed.
Theorem log_abstraction_nil d b :
  diskGet d 0 = Some b -> block_to_addr b = 0 -> log_abstraction d nil.
Proof.
(unfold log_abstraction; intros).
split.
-
eauto using log_length_ok_nil.
-
(simpl; intuition).
(exfalso; lia).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqeWX6KU"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
(eapply then_init_compose; eauto).
step_proc.
(destruct (lt_dec r 1)).
-
step_proc.
-
step_proc.
step_proc.
step_proc.
(exists nil; simpl).
(split; auto).
(eapply log_abstraction_nil; eauto).
(autorewrite with upd; auto).
Qed.
Theorem get_len_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' => state' = state /\ block_to_addr r = a;
     recovered := fun _ state' => state' = state |}) get_len d.recover.
(* Auto-generated comment: Failed. *)


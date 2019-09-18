Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqC9Uqvm"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Set Silent.
Require Import POCS.
Require Import LogAPI.
Require Import Common.OneDiskAPI.
Unset Silent.
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
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
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
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 8, left associativity).
Notation "d [ a |=> bs ]" := (diskUpds d a bs)
  (at level 8, left associativity).
Unset Silent.
Opaque diskGet.
Set Silent.
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
Unset Silent.
Timeout 1 Check @nil.
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
Unset Silent.
Set Diffs "off".
Timeout 1 Check @forallb.
Set Printing Width 78.
Definition log_length_ok (d : disk) (log : list block) :=
  forall b, diskGet d 0 =?= b -> block_to_addr b = length log.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqq8pd99"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqKfpcXP"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition log_abstraction (d : disk) (log : list block) : Prop :=
  log_length_ok d log /\
  (forall a, a < length log -> diskGet d (log_addr a) =?= nth a log block0).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq6pmLBV"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqT7hpH0"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition abstr : Abstraction State :=
  abstraction_compose d.abstr {| abstraction := log_abstraction |}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqMEyfIB"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqzysxCz"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Theorem log_length_ok_nil d b :
  diskGet d 0 = Some b -> block_to_addr b = 0 -> log_length_ok d nil.
Proof.
(unfold log_length_ok; intros).
Timeout 1 Check @Ascii.nat_ascii_embedding.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @sig.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(rewrite H in *; simpl in *; subst).
auto.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqyyuSGc"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Set Silent.
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
Unset Silent.
Qed.
Set Silent.
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
Theorem log_abstraction_length d bs :
  log_abstraction d bs -> log_length_ok d bs.
Proof.
(unfold log_abstraction; intuition).
Unset Silent.
Qed.
Set Silent.
Hint Resolve log_abstraction_length: core.
Lemma abstr_get_len :
  forall (bs : list block) (state : State),
  log_length_ok state bs ->
  forall r : block,
  diskGet state len_addr =?= r -> block_to_addr r = length bs.
Proof.
(intros).
Unset Silent.
(unfold log_length_ok in H).
Timeout 1 Check @app.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Tauto.A.
Set Printing Width 78.
Show.
auto.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqUxDb1R"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Timeout 1 Check @Ret.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Hint Resolve abstr_get_len: core.
Theorem get_len_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' => state' = state /\ r = length state;
     recovered := fun _ state' => state' = state |}) get_len d.recover abstr.
Proof.
(unfold get_len; intros).
(apply spec_abstraction_compose).
step_proc.
(destruct a' as [_ bs]; simpl in *; intuition eauto).
step_proc.
intuition eauto.
(eexists; intuition eauto).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqxfJz1W"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Set Silent.
Theorem get_ok : proc_spec get_spec get recover abstr.
Unset Silent.
Proof.
(unfold get; intros).
(apply spec_abstraction_compose; simpl).
step_proc.

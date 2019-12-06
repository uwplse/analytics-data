Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq8JO2NW"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import POCS.
Require Import LogAPI.
Require Import Common.OneDiskAPI.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq6jkELh"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqsAVenK"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Import ListNotations.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqodrjWK"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqGRB3oV"
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
     proc_spec (@addr_to_block_spec State a) 
       (addr_to_block a) recover abstr).
Hint Resolve addr_to_block_ok: core.
Notation "d [ a |-> b ]" := (diskUpd d a b)
  (at level 12, left associativity).
Notation "d [ a |=> bs ]" := (diskUpds d a bs)
  (at level 12, left associativity).
Opaque diskGet.
Module Log (d: OneDiskAPI)<: LogAPI.
Definition len_addr : addr := 0.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqnHbnEd"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqo5lVKK"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition log_addr a : addr := S a.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq1MimdH"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq2U2I6L"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition init' : proc InitResult :=
  size <- d.size;
  (if lt_dec size 1
   then Ret InitFailed
   else
    len0 <- addr_to_block 0;
    _ <- d.write len_addr len0; Ret Initialized).
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq8DQys4"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqsuaNCs"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition init := then_init d.init init'.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqeP41Bg"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqICah7l"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition get_len : proc addr :=
  b <- d.read len_addr; Ret (block_to_addr b).
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqdV247O"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqSG1NRr"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition get_at (a : addr) : proc block := d.read (log_addr a).
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqTDcFEr"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqBRYURt"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Fixpoint get_upto (a : addr) : proc (list block) :=
  match a with
  | 0 => Ret nil
  | S a => b <- get_at a; bs <- get_upto a; Ret (bs ++ [b])
  end.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq8BL9jg"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqRQgLVh"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition get : proc (list block) := len <- get_len; get_upto len.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqznrtKC"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqtKF1Q6"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Fixpoint append_at (a : addr) (bs : list block) : 
proc unit :=
  match bs with
  | [] => Ret tt
  | b :: bs => _ <- d.write (log_addr a) b; append_at (S a) bs
  end.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqg2oaAh"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq9iGxFC"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition append (bs : list block) : proc bool :=
  size <- d.size;
  len <- get_len;
  (if le_dec (1 + len + length bs) size
   then
    _ <- append_at len bs;
    len_b <- addr_to_block (len + length bs);
    _ <- d.write len_addr len_b; Ret true
   else Ret false).
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq7YWio4"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqRttP6D"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition reset : proc unit :=
  len0 <- addr_to_block 0; d.write len_addr len0.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqm1B31a"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqf37moS"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition recover : proc unit := d.recover.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq69sjE0"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq2nuY85"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition log_length_ok (d : disk) (log : list block) :=
  forall b,
  diskGet d len_addr =?= b -> block_to_addr b = length log.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqo1drHL"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq86RcfA"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition log_size_ok (d : disk) (log : list block) :=
  diskSize d >= 1 + length log.
Definition log_contents_ok (d : disk) (log : list block) :=
  forall a,
  a < length log -> diskGet d (log_addr a) =?= nth a log block0.
Definition log_abstraction (d : disk) (log : list block) : Prop :=
  log_length_ok d log /\ log_size_ok d log /\ log_contents_ok d log.
Theorem abstr_length_proj d log :
  log_abstraction d log -> log_length_ok d log.
Proof.
(unfold log_abstraction; intuition).
Qed.
Theorem abstr_size_proj d log :
  log_abstraction d log -> log_size_ok d log.
Proof.
(unfold log_abstraction; intuition).
Qed.
Theorem abstr_contents_proj d log :
  log_abstraction d log -> log_contents_ok d log.
Proof.
(unfold log_abstraction; intuition).
Qed.
Hint Resolve abstr_length_proj abstr_size_proj abstr_contents_proj:
  core.
Definition abstr : Abstraction State :=
  abstraction_compose d.abstr {| abstraction := log_abstraction |}.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqDETMzQ"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqafQlpc"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Lemma diskGet_eq_values :
  forall d a b b',
  diskGet d a =?= b ->
  diskGet d a =?= b' -> a < diskSize d -> b = b'.
Proof.
(intros).
(destruct (diskGet d a) eqn:?; simpl in *).
-
congruence.
-
exfalso.
(apply disk_inbounds_not_none in Heqo; eauto).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0E4PvN"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Ltac
 eq_values :=
  match goal with
  | H:diskGet ?d ?a =?= ?b, H':diskGet ?d ?a =?= ?b'
    |- _ =>
        assert (b = b') by
         (apply (@diskGet_eq_values d a b b'); try lia; auto);
         subst
  end.
Theorem log_length_ok_nil d b :
  diskGet d len_addr = Some b ->
  block_to_addr b = 0 -> log_length_ok d nil.
Proof.
(unfold log_length_ok; intros).
(rewrite H in *; simpl in *; subst).
auto.
Qed.
Theorem log_abstraction_nil d b :
  diskGet d len_addr = Some b ->
  block_to_addr b = 0 -> log_abstraction d nil.
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
(unfold len_addr).
(autorewrite with upd; auto).
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
     recovered := fun _ state' => state' = state |}) get_len
    recover d.abstr.
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
     recovered := fun _ state' => state' = state |}) get_len
    recover abstr.
Proof.
(apply spec_abstraction_compose).
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; intros).
(destruct a as [[] bs]; simpl in *; intuition eauto).
(exists bs; intuition eauto).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqfCnpvQ"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Hint Resolve get_len_abstr_ok: core.
Theorem log_size_bound d bs a :
  log_size_ok d bs -> a < length bs -> log_addr a < diskSize d.
Proof.
(unfold log_size_ok, log_addr; intros; lia).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqLORREb"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Hint Resolve log_size_bound: core.
Theorem get_at_ok a :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := a < length state;
     post := fun r state' =>
             state' = state /\ nth a state block0 = r;
     recovered := fun _ state' => state' = state |}) 
    (get_at a) recover abstr.
Proof.
(unfold get_at; intros).
(apply spec_abstraction_compose).
(simpl).
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; intros).
(destruct a0 as [_ bs]; simpl in *; intuition eauto).
(simplify; intuition eauto).
(exists bs; intuition eauto).
(unfold log_abstraction in H0; intuition).
(pose proof (H3 a); intuition).
(eapply diskGet_eq_values; eauto).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqJxzttA"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
auto.
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-09-05 17:21:55.820000.*)


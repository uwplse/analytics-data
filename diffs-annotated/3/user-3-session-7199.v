Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqIz2qfk"
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
(unfold len_addr).
(autorewrite with upd; auto).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqGXgs2S"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Qed.
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
(unfold log_abstraction in H0; intuition).
(pose proof (H3 a); intuition).
(assert (v = nth a bs block0)).
(eapply diskGet_eq_values; eauto).
auto.
Qed.
Hint Resolve get_at_ok: core.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
(unfold rec_wipe; simpl; intros).
(apply spec_abstraction_compose).
step_proc.
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
step_proc.
-
step_proc.
step_proc.
intuition eauto.
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
(descend; intuition eauto).
(rewrite firstn_all; auto).
Qed.
Theorem log_contents_ok_unchanged d bs a0 b :
  log_size_ok d bs ->
  log_contents_ok d bs ->
  a0 >= length bs -> log_contents_ok (diskUpd d (log_addr a0) b) bs.
Proof.
(unfold log_size_ok, log_contents_ok; intros).
(destruct (a == a0); subst; autorewrite with upd; auto).
(simpl; auto).
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
(rewrite app_nil_r; auto).
-
step_proc.
(intuition eauto; autorewrite with upd; auto).
{
(apply log_contents_ok_unchanged; eauto).
}
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; simpl; intuition).
(exists (a' ++ [a]); intuition eauto; autorewrite with upd list in *; eauto).
+
(simpl; lia).
+
(unfold log_size_ok in *; simpl in *).
autorewrite with upd list in *.
(simpl in *; lia).
+
admit.
+
(unfold log_size_ok in *; simpl in *).
autorewrite with upd list in *.
(simpl in *; lia).
+
(rewrite <- app_assoc in *; simpl in *; auto).
+
admit.
Admitted.
Hint Resolve append_at_ok: core.
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
destruct matches.
-
step_proc.
(descend; intuition eauto).
(unfold log_size_ok; autorewrite with list; auto).
(exists bs; intuition eauto).
(unfold log_abstraction; intuition eauto).
(unfold log_length_ok).
(rewrite H).
Admitted.
Theorem reset_ok : proc_spec reset_spec reset recover abstr.
Proof.
Admitted.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.

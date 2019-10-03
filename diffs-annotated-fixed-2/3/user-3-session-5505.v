Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqaJduVZ"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import POCS.
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
step_proc.
step_proc.
step_proc.
(rewrite bsplit_bappend).
intuition subst; eauto.
+
(destruct (diskGet state off); simpl in *; intuition subst; eauto).
+
(replace (S off) with off + 1 by lia; auto).
Qed.
Theorem write_ok :
  forall blocks off,
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' => r = tt /\ state' = write_upd state off blocks;
     recovered := fun _ state' =>
                  exists nwritten,
                    state' = write_upd state off (firstn nwritten blocks) |})
    (write off blocks) d.recover d.abstr.
Proof.
(induction blocks; intros).
-
(simpl).
step_proc.
intuition eauto.
(exists 0; simpl; eauto).
-
(simpl write).
step_proc.
intuition eauto.
+
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqEM7AbS"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqyjemv2"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
specialize (IHblocks (off + 1)).
step_proc.
(* Auto-generated comment: Succeeded. *)


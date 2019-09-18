Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqwgYkf9"
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
(destruct (diskGet state off); simpl in *; intuition subst; eauto).

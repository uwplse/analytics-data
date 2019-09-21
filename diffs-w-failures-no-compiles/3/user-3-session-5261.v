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
+
(destruct (diskGet state off); simpl in *; intuition subst; eauto).
+
(replace (S off) with off + 1 by lia; auto).
Unset Silent.
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqYvBan9"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqbUkiQL"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Silent.
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
Unset Silent.
+
specialize (IHblocks (off + 1)).
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
step_proc.
Set Silent.
Set Silent.
intuition subst; eauto.
Unset Silent.
*
(f_equal; lia).
*
(repeat deex).
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(exists (S nwritten); simpl).
(f_equal; lia).
+
(exists 0; simpl; auto).
+
(exists 1; simpl; auto).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqjRYYMf"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Set Silent.
CoFixpoint handle  : proc unit :=
  req <- nbd.getRequest;
  match req with
  | Read h off blocks =>
      data <- read off blocks;
      _ <-
      nbd.sendResponse {| rhandle := h; error := ESuccess; data := data |};
      handle
  | Write h off _ dat =>
      _ <- write off (bsplit_list dat);
      _ <-
      nbd.sendResponse {| rhandle := h; error := ESuccess; data := bnull |};
      handle
  | Flush h =>
      _ <-
      nbd.sendResponse {| rhandle := h; error := ESuccess; data := bnull |};
      handle
  | UnknownOp h =>
      _ <-
      nbd.sendResponse {| rhandle := h; error := EInvalid; data := bnull |};
      handle
  | Disconnect => Ret tt
  end.
Definition serverLoop : proc unit := _ <- nbd.recover; _ <- d.recover; handle.
Definition size : proc nat := d.size.
Definition init := then_init nbd.init d.init.
Unset Silent.
End NBDServer.

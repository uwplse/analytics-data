Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqv4syCy"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import POCS.
Require Import TwoDiskAPI.
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
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqr9dxAy"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqWm74kG"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Definition read_stub (a : addr) : proc block := Ret block0.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqui1abQ"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqZKr2j7"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqFyWRsO"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq9LNEcM"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqnoO54M"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqOtxYD5"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqi2zeRh"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqyDRpRL"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition init := then_init td.init init'.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqgXWsKG"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq3jRkhL"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Theorem exists_tuple2 :
  forall A B (P : A * B -> Prop), (exists a b, P (a, b)) -> exists p, P p.
Proof.
(intros).
(repeat deex; eauto).
Qed.
Tactic Notation "eexist_tuple" ident(a) ident(b) :=
 (match goal with
  | |- exists _ : ?aT * ?bT, _ =>
        let a := fresh a in
        let b := fresh b in
        evar ( a : aT ); evar ( b : bT ); exists (a, b); subst a; subst b
  end).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqKm6vC6"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.

Time Require Import AtomicPair.AtomicPairAPI.
Time Require Import ExMach.ExMachAPI.
Time Definition log_commit := 0.
Time Definition main_fst := 1.
Time Definition main_snd := 2.
Time Definition log_fst := 3.
Time Definition log_snd := 4.
Time Definition main_lock := 0.
Time Definition log_lock := 1.
Time
Definition write (p : nat * nat) :=
  (_ <- lock log_lock;
   _ <- write_disk log_fst (fst p);
   _ <- write_disk log_snd (snd p);
   _ <- write_disk log_commit 1;
   _ <- lock main_lock;
   _ <- write_disk main_fst (fst p);
   _ <- write_disk main_snd (snd p);
   _ <- write_disk log_commit 0; _ <- unlock log_lock; unlock main_lock)%proc.
Time
Definition read :=
  (_ <- lock main_lock;
   fst_val <- read_disk main_fst;
   snd_val <- read_disk main_snd;
   _ <- unlock main_lock; Ret (fst_val, snd_val))%proc.
Time
Definition recv :=
  (is_commit <- read_disk log_commit;
   match is_commit with
   | O => Ret tt
   | _ =>
       fst_val <- read_disk log_fst;
       snd_val <- read_disk log_snd;
       _ <- write_disk main_fst fst_val;
       _ <- write_disk main_snd snd_val; write_disk log_commit 0
   end)%proc.
Time
Definition impl : LayerImpl ExMach.Op AtomicPair.Op :=
  {|
  compile_op := fun T (op : AtomicPair.Op T) =>
                match op with
                | AtomicPair.Write n => write n
                | AtomicPair.Read => read
                end;
  recover := Seq_Cons recv Seq_Nil |}.

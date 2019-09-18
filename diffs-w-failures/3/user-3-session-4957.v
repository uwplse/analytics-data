Time From Coq Require Import List.
Time From stdpp Require Import gmap.
Time From Perennial Require Export Lib.
Time From Perennial Require Import TwoDiskAPI OneDiskAPI.
Time Import TwoDisk.
Time
Definition write (addr : nat) (v : nat) :=
  (if lt_dec addr size
   then _ <- lock addr;
        _ <- write_disk d0 addr v; _ <- write_disk d1 addr v; unlock addr
   else _ <- Ret tt; Ret tt)%proc.
Time
Definition read (addr : nat) :=
  (if lt_dec addr size
   then _ <- lock addr;
        v <-
        rd0 <- read_disk d0 addr;
        match rd0 with
        | Some v => Ret v
        | None =>
            rd1 <- read_disk d1 addr;
            match rd1 with
            | Some v => Ret v
            | None => Ret 0
            end
        end; _ <- unlock addr; Ret v else _ <- Ret tt; Ret 0)%proc.
Time
Definition fixup (a : addr) : proc Op unit :=
  (rd0 <- read_disk d0 a;
   match rd0 with
   | None => Ret tt
   | Some v => write_disk d1 a v
   end)%proc.
Time
Fixpoint recover_at (a : addr) : proc Op unit :=
  match a with
  | 0 => Ret tt
  | S n => _ <- fixup n; recover_at n
  end%proc.
Time Definition recv := recover_at size.
Time
Definition impl : LayerImpl TwoDisk.Op OneDisk.Op :=
  {|
  compile_op := fun T (op : OneDisk.Op T) =>
                match op with
                | OneDisk.Write_Disk a v => write a v
                | OneDisk.Read_Disk a => read a
                end;
  recover := Seq_Cons recv Seq_Nil |}.

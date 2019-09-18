Time From RecordUpdate Require Import RecordUpdate.
Time From Perennial Require Import Spec.Proc.
Time From Perennial Require Import Spec.InjectOp.
Time From Perennial Require Import Spec.SemanticsHelpers.
Time From Perennial Require Import Spec.LockDefs.
Time From Perennial.Goose Require Import Machine.
Time From Perennial.Goose Require Import GoZeroValues.
Time From Tactical Require Import ProofAutomation.
Time From stdpp Require Import base.
Time Import ProcNotations.
Time From Transitions Require Import Relations.
Time Set Implicit Arguments.
Time Implicit Type na : NonAtomicArgs unit.
Time Module Data.
Time Section GoModel.
Time Context `{model_wf : GoModelWf}.
Time
Inductive Op : Type -> Type :=
  | NewAlloc : forall T (v : T) (len : uint64), Op (ptr T)
  | PtrDeref : forall {T} (p : ptr T) (off : uint64), Op T
  | PtrStore : forall T (p : ptr T) (off : uint64) (x : T) na, Op unit
  | SliceAppend : forall T (s : slice.t T) (x : T), Op (slice.t T)
  | NewMap : forall V, Op (Map V)
  | MapAlter :
      forall `(m : Map V) (off : uint64) (f : option V -> option V) na,
      Op unit
  | MapLookup : forall `(m : Map V) (k : uint64), Op (option V)
  | MapStartIter : forall `(m : Map V), Op (list (uint64 * V))
  | MapEndIter : forall `(m : Map V), Op unit
  | NewLock : Op LockRef
  | LockAcquire : LockRef -> LockMode -> Op unit
  | LockRelease : LockRef -> LockMode -> Op unit
  | Uint64Get : slice.t byte -> forall na, Op (retT na uint64)
  | Uint64Put : slice.t byte -> uint64 -> forall na, Op unit
  | BytesToString : slice.t byte -> Op string
  | StringToBytes : string -> Op (slice.t byte)
  | RandomUint64 : Op uint64.
Time
Definition nonAtomicOp {Op} {Op'} {i : Injectable Op Op'} 
  {T} (op : forall args : NonAtomicArgs unit, Op (retT args T)) :
  proc Op' T :=
  Bind (Call (inject (op Begin)))
    (fun _ => Call (inject (op (FinishArgs tt)))).
Time
Definition nonAtomicWriteOp {Op} {Op'} {i : Injectable Op Op'}
  (op : forall args : NonAtomicArgs unit, Op unit) : 
  proc Op' unit :=
  Bind (Call (inject (op Begin)))
    (fun _ => Call (inject (op (FinishArgs tt)))).
Time Section OpWrappers.
Time Context {Op'} {i : Injectable Op Op'}.
Time Notation proc := (proc Op').
Time Notation "'Call' op" := (Call (inject op) : proc _) (at level 0).
Time
Notation "'Call!' op" := (Call (op) : proc _) (at level 0, op  at level 200).
Time Definition newAlloc T v len := Call! @NewAlloc T v len.
Time
Definition newPtr T {GoZero : HasGoZero T} : proc (ptr T) :=
  newAlloc (zeroValue T) 1.
Time
Definition newSlice T {GoZero : HasGoZero T} len : 
  proc (slice.t T) :=
  (p <- newAlloc (zeroValue T) len;
   Ret {| slice.ptr := p; slice.length := len; slice.offset := 0 |})%proc.
Time Definition ptrDeref {T} p off := Call! @PtrDeref T p off.
Time Definition readPtr {T} (p : ptr T) : proc T := ptrDeref p 0.
Time
Definition sliceRead T (s : slice.t T) off : proc T :=
  ptrDeref s.(slice.ptr) (s.(slice.offset) + off).
Time
Definition ptrStore T p off x : proc _ :=
  nonAtomicWriteOp (@PtrStore T p off x).
Time Definition writePtr T (p : ptr T) x := ptrStore p 0 x.
Time
Definition sliceWrite T (s : slice.t T) off (x : T) : 
  proc unit := ptrStore s.(slice.ptr) (s.(slice.offset) + off) x.
Time Definition sliceAppend T s x : proc _ := Call! @SliceAppend T s x.
Time
Fixpoint sliceAppendSlice_aux T (s s' : slice.t T) 
rem off :=
  match rem with
  | O => _ <- Ret tt; Ret s
  | S rem' =>
      x <- sliceRead s' off;
      supd <- sliceAppend s x; sliceAppendSlice_aux supd s' rem' (S off)
  end%proc.
Time
Definition sliceAppendSlice T (s s' : slice.t T) : 
  proc _ := sliceAppendSlice_aux s s' s'.(slice.length) O.
Time Definition newMap V := Call! NewMap V.
Time
Definition mapAlter V m (k : uint64) (f : option V -> option V) : 
  proc _ := nonAtomicWriteOp (@MapAlter V m k f).
Time Definition mapLookup {V} m k := Call! @MapLookup V m k.
Time
Definition mapIterLoop V kvs (body : uint64 -> V -> proc unit) : 
  proc unit :=
  List.fold_right (fun '(k, v) p => Bind p (fun _ => body k v)) (Ret tt) kvs.
Time
Definition mapIter V (m : Map V) (body : uint64 -> V -> proc unit) :
  proc unit :=
  (kvs <- Call (MapStartIter m);
   _ <- mapIterLoop kvs body; Call (MapEndIter m))%proc.
Time
Definition mapGet V {_ : HasGoZero V} (m : Map V) 
  k : proc (V * bool) :=
  (mv <- mapLookup m k;
   match mv with
   | Some v => Ret (v, true)
   | None => Ret (zeroValue V, false)
   end)%proc.
Time Definition newLock := Call! NewLock.
Time Definition lockAcquire l m := Call! LockAcquire l m.
Time Definition lockRelease l m := Call! LockRelease l m.
Time Definition uint64Get p := nonAtomicOp (Uint64Get p).
Time Definition uint64Put p n := nonAtomicWriteOp (Uint64Put p n).
Time Definition bytesToString bs := Call! BytesToString bs.
Time Definition stringToBytes s := Call! StringToBytes s.
Time Definition randomUint64 := Call! RandomUint64.
Time End OpWrappers.
Time Definition hashtableM V := (LockStatus * gmap.gmap uint64 V)%type.
Time
Definition ptrRawModel (code : Ptr.ty) : Type :=
  match code with
  | Ptr.Heap T => list T
  | Ptr.Map V => gmap.gmap uint64 V
  | Ptr.Lock => unit
  end.
Time
Definition ptrModel (code : Ptr.ty) : Type := LockStatus * ptrRawModel code.
Time
Lemma ptrModel_raw1 code :
  ptrModel code = (LockStatus * ptrRawModel code)%type.
Time Proof.
Time (destruct code; auto).
Time Qed.
Time Record State : Type := mkState {allocs : DynMap Ptr ptrModel}.
Time #[global]Instance _eta : (Settable _) := settable! mkState < allocs >.
Time
Definition getAlloc {ty} (p : Ptr ty) (s : State) : 
  option (ptrModel ty) := getDyn s.(allocs) p.
Time
Definition updAllocs {ty} (p : Ptr ty) (x : ptrModel ty) :
  relation State State unit := puts (set allocs (updDyn p x)).
Time
Definition delAllocs {ty} (p : Ptr ty) : relation State State unit :=
  puts (set allocs (deleteDyn p)).
Time Import RelationNotations.
Time
Lemma lock_acquire_release m s :
  forall s', lock_acquire m s = Some s' -> lock_release m s' = Some s.
Time Proof.
Time (destruct m, s; simpl; inversion 1; auto).
Time Qed.
Time
Theorem lock_available_acquire_release m s :
  lock_available m s = Some tt <->
  (exists s', lock_acquire m s = Some s' /\ lock_release m s' = Some s).
Time Proof.
Time (destruct m, s; simpl; intuition eauto; propositional; try congruence).
Time Qed.
Time
Fixpoint list_nth_upd A (l : list A) (n : nat) (x : A) : 
option (list A) :=
  match n with
  | 0 => match l with
         | nil => None
         | x0 :: xs => Some (x :: xs)
         end
  | S n' =>
      match l with
      | nil => None
      | x0 :: xs =>
          match list_nth_upd xs n' x with
          | Some xs' => Some (x0 :: xs')
          | None => None
          end
      end
  end.
Time
Theorem list_nth_upd_length A (l : list A) n x l' :
  list_nth_upd l n x = Some l' -> length l = length l'.
Time Proof.
Time generalize dependent l.
Time generalize dependent l'.
Time (induction n; simpl).
Time -
Time (destruct l; simpl; inversion 1; subst).
Time (simpl; auto).
Time -
Time (destruct l; simpl; inversion 1; subst).
Time (destruct_with_eqn list_nth_upd l n x; try congruence).
Time (inv_clear H).
Time (simpl; eauto).
Time Qed.
Time
Theorem list_nth_upd_get_nth A (l : list A) n x l' :
  list_nth_upd l n x = Some l' -> List.nth_error l' n = Some x.
Time Proof.
Time generalize dependent l.
Time generalize dependent l'.
Time (induction n; simpl).
Time -
Time (destruct l; simpl; inversion 1; subst; auto).
Time -
Time (destruct l; simpl; inversion 1; subst).
Time (destruct_with_eqn list_nth_upd l n x; try congruence).
Time (inv_clear H).
Time eauto.
Time Qed.
Time
Definition getSliceModel T (s : slice.t T) (alloc : list T) :
  option (list T) :=
  stdpp.list.sublist_lookup s.(slice.offset) s.(slice.length) alloc.
Time
Definition allocPtr (ty : Ptr.ty) (init : ptrRawModel ty) :
  relation State State (model.(@Ptr) ty) :=
  r <- such_that (fun s r => getAlloc r s = None /\ r <> nullptr _);
  _ <- updAllocs r (Unlocked, init); pure r.
Time
Definition step T (op : Op T) : relation State State T :=
  match op in (Op T) return (relation State State T) with
  | NewAlloc v len => allocPtr (Ptr.Heap _) (List.repeat v len)
  | PtrDeref p off =>
      let! (s, alloc) <- readSome (getAlloc p);
      _ <- readSome (fun _ => lock_available Reader s);
      x <- readSome (fun _ => List.nth_error alloc off); pure x
  | PtrStore p off x ph =>
      let! (s, alloc) <- readSome (getAlloc p);
      match ph with
      | Begin =>
          s' <- readSome (fun _ => lock_acquire Writer s);
          updAllocs p (s', alloc)
      | FinishArgs _ =>
          s' <- readSome (fun _ => lock_release Writer s);
          alloc' <- readSome (fun _ => list_nth_upd alloc off x);
          updAllocs p (s', alloc')
      end
  | SliceAppend p x =>
      let! (s, alloc) <- readSome (getAlloc p.(slice.ptr));
      val <- readSome (fun _ => getSliceModel p alloc);
      _ <- readSome (fun _ => lock_available Writer s);
      _ <- delAllocs p.(slice.ptr);
      r <- allocPtr (Ptr.Heap _) (val ++ [x]);
      pure
        {|
        slice.ptr := r;
        slice.offset := 0;
        slice.length := (p.(slice.length) + 1)%nat |}
  | NewMap V => allocPtr (Ptr.Map _) \226\136\133
  | MapLookup r k =>
      let! (s, m) <- readSome (fun s => getDyn s.(allocs) r);
      _ <- readSome (fun _ => lock_available Reader s); pure (m !! k)
  | MapAlter r k f ph =>
      let! (s, m) <- readSome (fun s => getDyn s.(allocs) r);
      match ph with
      | Begin =>
          s' <- readSome (fun _ => lock_acquire Writer s);
          updAllocs r (s', m)
      | FinishArgs _ =>
          s' <- readSome (fun _ => lock_release Writer s);
          updAllocs r (s', partial_alter f k m)
      end
  | MapStartIter r =>
      let! (s, m) <- readSome (fun s => getDyn s.(allocs) r);
      s' <- readSome (fun _ => lock_acquire Reader s);
      _ <- updAllocs r (s', m);
      such_that
        (fun _ l => Permutation.Permutation l (fin_maps.map_to_list m))
  | MapEndIter r =>
      let! (s, m) <- readSome (fun s => getDyn s.(allocs) r);
      s' <- readSome (fun _ => lock_release Reader s);
      _ <- updAllocs r (s', m); pure tt
  | NewLock => allocPtr Ptr.Lock tt
  | LockAcquire r m =>
      let! (v, _) <- readSome (fun s => getDyn s.(allocs) r);
      match lock_acquire m v with
      | Some s' => updAllocs r (s', tt)
      | None => none
      end
  | LockRelease r m =>
      let! (v, _) <- readSome (fun s => getDyn s.(allocs) r);
      match lock_release m v with
      | Some s' => updAllocs r (s', tt)
      | None => error
      end
  | Uint64Get p ph =>
      let! (s, alloc) <- readSome (getAlloc p.(slice.ptr));
      val <- readSome (fun _ => getSliceModel p alloc);
      match ph return (relation _ _ (retT ph uint64)) with
      | Begin =>
          s' <- readSome (fun _ => lock_acquire Reader s);
          updAllocs p.(slice.ptr) (s', alloc)
      | FinishArgs _ =>
          s' <- readSome (fun _ => lock_release Reader s);
          _ <- updAllocs p.(slice.ptr) (s', alloc);
          pure (uint64_from_le (list.take 8 val))
      end
  | Uint64Put p x ph =>
      let! (s, alloc) <- readSome (getAlloc p.(slice.ptr));
      val <- readSome (fun _ => getSliceModel p alloc);
      if numbers.nat_lt_dec (length val) 8
      then error
      else
       match ph with
       | Begin =>
           s' <- readSome (fun _ => lock_acquire Writer s);
           updAllocs p.(slice.ptr) (s', alloc)
       | FinishArgs _ =>
           s' <- readSome (fun _ => lock_release Writer s);
           enc <- readSome (fun _ => uint64_to_le x);
           updAllocs p.(slice.ptr) (s', enc ++ list.drop 8 alloc)
       end
  | BytesToString p =>
      let! (s, alloc) <- readSome (getAlloc p.(slice.ptr));
      val <- readSome (fun _ => getSliceModel p alloc);
      _ <- readSome (fun _ => lock_available Reader s);
      pure (bytes_to_string val)
  | StringToBytes s =>
      r <- allocPtr (Ptr.Heap _) (string_to_bytes s);
      pure
        {|
        slice.ptr := r;
        slice.offset := 0;
        slice.length := String.length s |}
  | RandomUint64 => such_that (fun _ (r : uint64) => True)
  end.
Time #[global]Instance empty_heap : (Empty State) := {| allocs := \226\136\133 |}.
Time End GoModel.
Time End Data.
Time Arguments Data.newPtr {model} {Op'} {i} T {GoZero}.
Time Arguments Data.newSlice {model} {Op'} {i} T {GoZero} len.

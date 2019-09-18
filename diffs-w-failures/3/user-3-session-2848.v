Time
Inductive LockStatus :=
  | Locked : _
  | ReadLocked : forall num : nat, _
  | Unlocked : _.
Time Inductive LockMode :=
       | Reader : _
       | Writer : _.
Time
Definition lock_acquire (m : LockMode) (s : LockStatus) :
  option LockStatus :=
  match m, s with
  | Reader, ReadLocked n => Some (ReadLocked (S n))
  | Reader, Unlocked => Some (ReadLocked 0)
  | Writer, Unlocked => Some Locked
  | _, _ => None
  end.
Time
Definition lock_release (m : LockMode) (s : LockStatus) :
  option LockStatus :=
  match m, s with
  | Reader, ReadLocked 0 => Some Unlocked
  | Reader, ReadLocked (S n) => Some (ReadLocked n)
  | Writer, Locked => Some Unlocked
  | _, _ => None
  end.
Time
Definition lock_available (m : LockMode) (s : LockStatus) : 
  option unit :=
  match m, s with
  | Reader, ReadLocked _ => Some tt
  | _, Unlocked => Some tt
  | _, _ => None
  end.
Time
Definition force_read_lock (s : LockStatus) : LockStatus :=
  match s with
  | ReadLocked n => ReadLocked (S n)
  | _ => ReadLocked 0
  end.
Time
Definition force_read_unlock (s : LockStatus) : LockStatus :=
  match s with
  | ReadLocked (S n) => ReadLocked n
  | _ => Unlocked
  end.
Time From Coq Require Export RelationClasses.
Time From Classes Require Export EqualDec.
Time From Classes Require Export Default.
Time
Ltac
 RelInstance_t :=
  intros;
   (let refl := try (solve [ hnf; intros; reflexivity ]) in
    let symm := try (solve [ hnf; intros; try symmetry; eauto ]) in
    let trans := try (solve [ hnf; intros; etransitivity; eauto ]) in
    try
     match goal with
     | |- Reflexive _ => hnf; intros; refl
     | |- Symmetric _ => hnf; intros; symm
     | |- Transitive _ => hnf; intros; trans
     | |- PreOrder _ => constructor; hnf; intros; [ refl | trans ]
     | |- Equivalence _ => constructor; hnf; intros; [ refl | symm | trans ]
     end).
Time Notation RelInstance := _ (only parsing).

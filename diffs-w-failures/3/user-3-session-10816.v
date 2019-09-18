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
Time Reserved Notation "P \226\138\162 Q"
(at level 99, Q  at level 200, right associativity).
Time Reserved Notation "P '\226\138\162@{' PROP } Q"
(at level 99, Q  at level 200, right associativity).
Time Reserved Notation "('\226\138\162@{' PROP } )" (at level 99).
Time Reserved Notation "P \226\138\163\226\138\162 Q" (at level 95, no associativity).
Time Reserved Notation "P '\226\138\163\226\138\162@{' PROP } Q" (at level 95, no associativity).
Time Reserved Notation "('\226\138\163\226\138\162@{' PROP } )" (at level 95).
Time Reserved Notation "'emp'".
Time Reserved Notation "'\226\140\156' \207\134 '\226\140\157'"
(at level 1, \207\134  at level 200, format "\226\140\156 \207\134 \226\140\157").
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
Time Reserved Notation "P \226\136\151 Q" (at level 80, right associativity).
Time Reserved Notation "P -\226\136\151 Q"
(at level 99, Q  at level 200, right associativity,
 format "'[' P  '/' -\226\136\151  Q ']'").
Time Reserved Notation "\226\142\161 P \226\142\164".
Time Reserved Notation "'<pers>' P" (at level 20, right associativity).
Time Reserved Notation "'<pers>?' p P"
(at level 20, p  at level 9, P  at level 20, right associativity,
 format "'<pers>?' p  P").
Time Reserved Notation "\226\150\183 P" (at level 20, right associativity).
Time Reserved Notation "\226\150\183? p P"
(at level 20, p  at level 9, P  at level 20, format "\226\150\183? p  P").
Time Reserved Notation "\226\150\183^ n P"
(at level 20, n  at level 9, P  at level 20, format "\226\150\183^ n  P").
Time Reserved Notation "x '\226\136\151-\226\136\151' y" (at level 95, no associativity).
Time Reserved Notation "'<affine>' P" (at level 20, right associativity).
Time Reserved Notation "'<affine>?' p P"
(at level 20, p  at level 9, P  at level 20, right associativity,
 format "'<affine>?' p  P").
Time Reserved Notation "'<absorb>' P" (at level 20, right associativity).
Time Reserved Notation "'<absorb>?' p P"
(at level 20, p  at level 9, P  at level 20, right associativity,
 format "'<absorb>?' p  P").
Time Reserved Notation "\226\150\161 P" (at level 20, right associativity).
Time Reserved Notation "'\226\150\161?' p P"
(at level 20, p  at level 9, P  at level 20, right associativity,
 format "'\226\150\161?' p  P").
Time Reserved Notation "\226\151\135 P" (at level 20, right associativity).
Time Reserved Notation "\226\150\160 P" (at level 20, right associativity).
Time Reserved Notation "\226\150\160? p P"
(at level 20, p  at level 9, P  at level 20, right associativity,
 format "\226\150\160? p  P").
Time Reserved Notation "'<obj>' P" (at level 20, right associativity).
Time Reserved Notation "'<subj>' P" (at level 20, right associativity).
Time Reserved Notation "|==> Q"
(at level 99, Q  at level 200, format "|==>  Q").
Time Reserved Notation "P ==\226\136\151 Q"
(at level 99, Q  at level 200, format "'[' P  '/' ==\226\136\151  Q ']'").
Time Reserved Notation "|={ E1 , E2 }=> Q"
(at level 99, E1, E2  at level 50, Q  at level 200,
 format "|={ E1 , E2 }=>  Q").
Time Reserved Notation "P ={ E1 , E2 }=\226\136\151 Q"
(at level 99, E1, E2  at level 50, Q  at level 200,
 format "'[' P  '/' ={ E1 , E2 }=\226\136\151  Q ']'").
Time Reserved Notation "|={ E }=> Q"
(at level 99, E  at level 50, Q  at level 200, format "|={ E }=>  Q").
Time Reserved Notation "P ={ E }=\226\136\151 Q"
(at level 99, E  at level 50, Q  at level 200,
 format "'[' P  '/' ={ E }=\226\136\151  Q ']'").
Time Reserved Notation "|={ E1 , E2 , E3 }\226\150\183=> Q"
(at level 99, E1, E2  at level 50, Q  at level 200,
 format "|={ E1 , E2 , E3 }\226\150\183=>  Q").
Time Reserved Notation "P ={ E1 , E2 , E3 }\226\150\183=\226\136\151 Q"
(at level 99, E1, E2  at level 50, Q  at level 200,
 format "'[' P  '/' ={ E1 , E2 , E3 }\226\150\183=\226\136\151  Q ']'").
Time Reserved Notation "|={ E1 , E2 }\226\150\183=> Q"
(at level 99, E1, E2  at level 50, Q  at level 200,
 format "|={ E1 , E2 }\226\150\183=>  Q").
Time Reserved Notation "P ={ E1 , E2 }\226\150\183=\226\136\151 Q"
(at level 99, E1, E2  at level 50, Q  at level 200,
 format "'[' P  '/' ={ E1 , E2 }\226\150\183=\226\136\151  Q ']'").
Time Reserved Notation "|={ E }\226\150\183=> Q"
(at level 99, E  at level 50, Q  at level 200, format "|={ E }\226\150\183=>  Q").
Time Reserved Notation "P ={ E }\226\150\183=\226\136\151 Q"
(at level 99, E  at level 50, Q  at level 200,
 format "'[' P  '/' ={ E }\226\150\183=\226\136\151  Q ']'").
Time Reserved Notation "|={ E1 , E2 }\226\150\183=>^ n Q"
(at level 99, E1, E2  at level 50, n  at level 9, Q  at level 200,
 format "|={ E1 , E2 }\226\150\183=>^ n  Q").
Time Reserved Notation "P ={ E1 , E2 }\226\150\183=\226\136\151^ n Q"
(at level 99, E1, E2  at level 50, n  at level 9, Q  at level 200,
 format "P  ={ E1 , E2 }\226\150\183=\226\136\151^ n  Q").
Time Reserved Notation "'[\226\136\151' 'list]' k \226\134\166 x \226\136\136 l , P"
(at level 200, l  at level 10, k, x  at level 1, right associativity,
 format "[\226\136\151  list]  k \226\134\166 x  \226\136\136  l ,  P").
Time Reserved Notation "'[\226\136\151' 'list]' x \226\136\136 l , P"
(at level 200, l  at level 10, x  at level 1, right associativity,
 format "[\226\136\151  list]  x  \226\136\136  l ,  P").
Time Reserved Notation "'[\226\136\151' 'list]' k \226\134\166 x1 ; x2 \226\136\136 l1 ; l2 , P"
(at level 200, l1, l2  at level 10, k, x1, x2  at level 1,
 right associativity, format "[\226\136\151  list]  k \226\134\166 x1 ; x2  \226\136\136  l1 ; l2 ,  P").
Time Reserved Notation "'[\226\136\151' 'list]' x1 ; x2 \226\136\136 l1 ; l2 , P"
(at level 200, l1, l2  at level 10, x1, x2  at level 1, right associativity,
 format "[\226\136\151  list]  x1 ; x2  \226\136\136  l1 ; l2 ,  P").
Time Reserved Notation "'[\226\136\151]' Ps" (at level 20).
Time Reserved Notation "'[\226\136\167' 'list]' k \226\134\166 x \226\136\136 l , P"
(at level 200, l  at level 10, k, x  at level 1, right associativity,
 format "[\226\136\167  list]  k \226\134\166 x  \226\136\136  l ,  P").
Time Reserved Notation "'[\226\136\167' 'list]' x \226\136\136 l , P"
(at level 200, l  at level 10, x  at level 1, right associativity,
 format "[\226\136\167  list]  x  \226\136\136  l ,  P").
Time Reserved Notation "'[\226\136\167]' Ps" (at level 20).
Time Reserved Notation "'[\226\136\168' 'list]' k \226\134\166 x \226\136\136 l , P"
(at level 200, l  at level 10, k, x  at level 1, right associativity,
 format "[\226\136\168  list]  k \226\134\166 x  \226\136\136  l ,  P").
Time Reserved Notation "'[\226\136\168' 'list]' x \226\136\136 l , P"
(at level 200, l  at level 10, x  at level 1, right associativity,
 format "[\226\136\168  list]  x  \226\136\136  l ,  P").
Time Reserved Notation "'[\226\136\168]' Ps" (at level 20).
Time Reserved Notation "'[\226\136\151' 'map]' k \226\134\166 x \226\136\136 m , P"
(at level 200, m  at level 10, k, x  at level 1, right associativity,
 format "[\226\136\151  map]  k \226\134\166 x  \226\136\136  m ,  P").
Time Reserved Notation "'[\226\136\151' 'map]' x \226\136\136 m , P"
(at level 200, m  at level 10, x  at level 1, right associativity,
 format "[\226\136\151  map]  x  \226\136\136  m ,  P").
Time Reserved Notation "'[\226\136\151' 'map]' k \226\134\166 x1 ; x2 \226\136\136 m1 ; m2 , P"
(at level 200, m1, m2  at level 10, k, x1, x2  at level 1,
 right associativity, format "[\226\136\151  map]  k \226\134\166 x1 ; x2  \226\136\136  m1 ; m2 ,  P").
Time Reserved Notation "'[\226\136\151' 'map]' x1 ; x2 \226\136\136 m1 ; m2 , P"
(at level 200, m1, m2  at level 10, x1, x2  at level 1, right associativity,
 format "[\226\136\151  map]  x1 ; x2  \226\136\136  m1 ; m2 ,  P").
Time Reserved Notation "'[\226\136\151' 'set]' x \226\136\136 X , P"
(at level 200, X  at level 10, x  at level 1, right associativity,
 format "[\226\136\151  set]  x  \226\136\136  X ,  P").
Time Reserved Notation "'[\226\136\151' 'mset]' x \226\136\136 X , P"
(at level 200, X  at level 10, x  at level 1, right associativity,
 format "[\226\136\151  mset]  x  \226\136\136  X ,  P").
Time Delimit Scope bi_scope with I.

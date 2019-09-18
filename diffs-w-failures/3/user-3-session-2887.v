Time From iris.algebra Require Export ofe.
Time Set Default Proof Using "Type".
Time
Class Monoid {M : ofeT} (o : M \226\134\146 M \226\134\146 M) :={monoid_unit : M;
                                           monoid_ne : NonExpansive2 o;
                                           monoid_assoc : Assoc (\226\137\161) o;
                                           monoid_comm : Comm (\226\137\161) o;
                                           monoid_left_id :
                                            LeftId (\226\137\161) monoid_unit o}.
Time Lemma monoid_proper `{Monoid M o} : Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) o.
Time Proof.
Time (apply ne_proper_2, monoid_ne).
Time Qed.
Time Lemma monoid_right_id `{Monoid M o} : RightId (\226\137\161) monoid_unit o.
Time Proof.
Time (intros x).
Time (etrans; [ apply monoid_comm | apply monoid_left_id ]).
Time Qed.
Time
Class WeakMonoidHomomorphism {M1 M2 : ofeT} (o1 : M1 \226\134\146 M1 \226\134\146 M1)
(o2 : M2 \226\134\146 M2 \226\134\146 M2) `{Monoid M1 o1} `{Monoid M2 o2} 
(R : relation M2) (f : M1 \226\134\146 M2) :={monoid_homomorphism_rel_po : PreOrder R;
                                   monoid_homomorphism_rel_proper :
                                    Proper ((\226\137\161) ==> (\226\137\161) ==> iff) R;
                                   monoid_homomorphism_op_proper :
                                    Proper (R ==> R ==> R) o2;
                                   monoid_homomorphism_ne : NonExpansive f;
                                   monoid_homomorphism :
                                    forall x y,
                                    R (f (o1 x y)) (o2 (f x) (f y))}.
Time
Class MonoidHomomorphism {M1 M2 : ofeT} (o1 : M1 \226\134\146 M1 \226\134\146 M1)
(o2 : M2 \226\134\146 M2 \226\134\146 M2) `{Monoid M1 o1} `{Monoid M2 o2} 
(R : relation M2) (f : M1 \226\134\146 M2) :={monoid_homomorphism_weak :>
                                    WeakMonoidHomomorphism o1 o2 R f;
                                   monoid_homomorphism_unit :
                                    R (f monoid_unit) monoid_unit}.
Time
Lemma weak_monoid_homomorphism_proper
  `{WeakMonoidHomomorphism M1 M2 o1 o2 R f} : Proper ((\226\137\161) ==> (\226\137\161)) f.
Time Proof.
Time (apply ne_proper, monoid_homomorphism_ne).
Time Qed.

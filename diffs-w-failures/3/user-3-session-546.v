From Coq Require Export RelationClasses.
From Classes Require Export EqualDec.
From Classes Require Export Default.
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
Notation RelInstance := _ (only parsing).

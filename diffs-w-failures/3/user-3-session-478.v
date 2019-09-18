Time Set Implicit Arguments.
Time Definition Reader E T := forall e : E, T e.
Time Arguments Reader : clear implicits.
Time
Definition constructor {E} {T} (x : T) : Reader E (fun _ => T) := fun _ => x.
Time
Definition applicative_ap {E} {A : E -> Type} {B : forall e : E, A e -> Type}
  (f : Reader E (fun e => forall a : A e, B e a)) :
  forall x : Reader E A, Reader E (fun e => B e (x e)) :=
  fun x => fun e => f e (x e).
Time
Class Settable T :={mkT : Reader T (fun _ => T);
                    mkT_ok : forall x, mkT x = x}.
Time Arguments mkT T mk : clear implicits,  rename.
Time #[local]
Ltac
 solve_mkT_ok :=
  match goal with
  | |- forall x, _ = _ => solve [ destruct x; compute; f_equal ]
  end.
Time
Notation "'settable!' mk < f1 ; .. ; fn >" :=
  (Build_Settable
     (applicative_ap .. (applicative_ap (constructor mk) f1) .. fn) _)
  (at level 0, mk  at level 10, f1, fn  at level 9, only parsing).
Time #[local]
Ltac
 setter etaT proj :=
  lazymatch etaT with
  | context [ proj ] => idtac
  | _ => fail 1 proj "is not a field"
  end;
   (let set :=
     match eval pattern proj in etaT with
     | ?setter ?proj => fun f => setter (fun r => f (proj r))
     end
    in
    let set := eval cbv[constructor applicative_ap] in set in
    exact
    set).
Time #[local]
Ltac
 get_setter T proj :=
  match mkT T _ with
  | mkT _ ?updateable =>
      let updateable := eval hnf in updateable in
      match updateable with
      | {| mkT := ?mk |} => setter mk proj
      end
  end.
Time Class Setter {R} {T} (proj : R -> T) :=
         set : (T -> T) -> R -> R.
Time Arguments set {R} {T} proj {Setter}.
Time
Class SetterWf {R} {T} (proj : R -> T) :={set_wf :> Setter proj;
                                          set_get :
                                           forall v r,
                                           proj (set proj v r) = v (proj r);
                                          set_eq :
                                           forall f r,
                                           f (proj r) = proj r ->
                                           set proj f r = r}.
Time Arguments set_wf {R} {T} proj {SetterWf}.
Time #[local]
Ltac
 SetterInstance_t := match goal with
                     | |- @Setter ?T _ ?A => get_setter T A
                     end.
Time #[local]
Ltac
 SetterWfInstance_t :=
  match goal with
  | |- @SetterWf ?T _ ?A =>
        unshelve notypeclasses refine (Build_SetterWf _ _ _);
         [ get_setter T A
         | let r := fresh in
           intros ? r; destruct r; reflexivity
         | let f := fresh in
           let r := fresh in
           intros f r; destruct r; compute; congruence ]
  end.
Time Hint Extern 1 (Setter _) => SetterInstance_t: typeclass_instances.
Time Hint Extern 1 (SetterWf _) => SetterWfInstance_t: typeclass_instances.
Time Module RecordSetNotations.
Time Delimit Scope record_set with rs.
Time Open Scope rs.
Time
Notation "x <| proj  :=  v |>" := (set proj (constructor v) x)
  (at level 12, left associativity) : record_set.
Time
Notation "x <| proj  ::=  f |>" := (set proj f x)
  (at level 12, f  at next level, left associativity) : record_set.
Time End RecordSetNotations.

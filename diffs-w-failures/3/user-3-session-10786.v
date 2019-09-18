Class Default T :=
    default : T.
#[local]Ltac mkDefault := unfold Default; constructor; exact default.
Hint Extern 1 (Default _) => mkDefault: typeclass_instances.
#[local]Notation cache_default := _ (only parsing).
Set Implicit Arguments.
Definition Reader E T := forall e : E, T e.
Arguments Reader : clear implicits.
Definition constructor {E} {T} (x : T) : Reader E (fun _ => T) := fun _ => x.
Instance unit_def : (Default unit) := cache_default.
Instance nat_def : (Default nat) := cache_default.
Instance list_def  A: (Default (list A)) := cache_default.
Instance option_def  A: (Default (option A)) := cache_default.
Instance pair_def  A B (defA : Default A) (defB : Default B):
 (Default (A * B)) := cache_default.
Definition applicative_ap {E} {A : E -> Type} {B : forall e : E, A e -> Type}
  (f : Reader E (fun e => forall a : A e, B e a)) :
  forall x : Reader E A, Reader E (fun e => B e (x e)) :=
  fun x => fun e => f e (x e).
Class Settable T :={mkT : Reader T (fun _ => T);
                    mkT_ok : forall x, mkT x = x}.
Arguments mkT T mk : clear implicits,  rename.
#[local]
Ltac
 solve_mkT_ok :=
  match goal with
  | |- forall x, _ = _ => solve [ destruct x; compute; f_equal ]
  end.
Notation "'settable!' mk < f1 ; .. ; fn >" :=
  (Build_Settable
     (applicative_ap .. (applicative_ap (constructor mk) f1) .. fn) _)
  (at level 0, mk  at level 10, f1, fn  at level 9, only parsing).
#[local]
Ltac
 setter etaT proj :=
  let set :=
   match eval pattern proj in etaT with
   | ?setter ?proj => fun f => setter (fun r => f (proj r))
   end
  in
  let set := eval cbv[constructor applicative_ap] in set in
  exact
  set.
#[local]
Ltac
 get_setter T proj :=
  match mkT T _ with
  | mkT _ ?updateable =>
      let updateable := eval hnf in updateable in
      match updateable with
      | {| mkT := ?mk |} => setter mk proj
      end
  end.
Class Setter {R} {T} (proj : R -> T) :=
    set : (T -> T) -> R -> R.
Arguments set {R} {T} proj {Setter}.
Class SetterWf {R} {T} (proj : R -> T) :={set_wf :> Setter proj;
                                          set_get :
                                           forall v r,
                                           proj (set proj v r) = v (proj r);
                                          set_eq :
                                           forall f r,
                                           f (proj r) = proj r ->
                                           set proj f r = r}.
Arguments set_wf {R} {T} proj {SetterWf}.
#[local]
Ltac
 SetterInstance_t := match goal with
                     | |- @Setter ?T _ ?A => get_setter T A
                     end.
#[local]
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
Hint Extern 1 (Setter _) => SetterInstance_t: typeclass_instances.
Hint Extern 1 (SetterWf _) => SetterWfInstance_t: typeclass_instances.
Module RecordSetNotations.
Delimit Scope record_set with rs.
Open Scope rs.
Notation "x <| proj  :=  v |>" := (set proj (constructor v) x)
  (at level 12, left associativity) : record_set.
Notation "x <| proj  ::=  f |>" := (set proj f x)
  (at level 12, f  at next level, left associativity) : record_set.
End RecordSetNotations.

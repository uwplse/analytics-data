Time From stdpp Require Export coPset.
Time From iris.program_logic Require Import language.
Time From iris.bi Require Import interface derived_connectives.
Time Inductive stuckness :=
       | NotStuck : _
       | MaybeStuck : _.
Time
Definition stuckness_leb (s1 s2 : stuckness) : bool :=
  match s1, s2 with
  | MaybeStuck, NotStuck => false
  | _, _ => true
  end.
Time Instance stuckness_le : (SqSubsetEq stuckness) := stuckness_leb.
Time Instance stuckness_le_po : (PreOrder stuckness_le).
Time Proof.
Time (split; by repeat intros []).
Time Qed.
Time
Definition stuckness_to_atomicity (s : stuckness) : atomicity :=
  match s with
  | MaybeStuck => StronglyAtomic
  | _ => WeaklyAtomic
  end.
Time
Class Wp (\206\155 : language) (PROP A : Type) :=
    wp : A \226\134\146 coPset \226\134\146 expr \206\155 \226\134\146 (val \206\155 \226\134\146 PROP) \226\134\146 PROP.
Time Arguments wp {_} {_} {_} {_} _ _ _%E _%I.
Time Instance: (Params (@wp) 7) := { }.
Time
Class Twp (\206\155 : language) (PROP A : Type) :=
    twp : A \226\134\146 coPset \226\134\146 expr \206\155 \226\134\146 (val \206\155 \226\134\146 PROP) \226\134\146 PROP.
Time Arguments twp {_} {_} {_} {_} _ _ _%E _%I.
Time Instance: (Params (@twp) 7) := { }.
Time
Notation "'WP' e @ s ; E {{ \206\166 } }" := (wp s E e%E \206\166)
  (at level 20, e, \206\166  at level 200, only parsing) : bi_scope.
Time
Notation "'WP' e @ E {{ \206\166 } }" := (wp NotStuck E e%E \206\166)
  (at level 20, e, \206\166  at level 200, only parsing) : bi_scope.
Time
Notation "'WP' e @ E ? {{ \206\166 } }" := (wp MaybeStuck E e%E \206\166)
  (at level 20, e, \206\166  at level 200, only parsing) : bi_scope.
Time
Notation "'WP' e {{ \206\166 } }" := (wp NotStuck \226\138\164 e%E \206\166)
  (at level 20, e, \206\166  at level 200, only parsing) : bi_scope.
Time
Notation "'WP' e ? {{ \206\166 } }" := (wp MaybeStuck \226\138\164 e%E \206\166)
  (at level 20, e, \206\166  at level 200, only parsing) : bi_scope.
Time
Notation "'WP' e @ s ; E {{ v , Q } }" := (wp s E e%E (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' '[          ' @  s ;  E  {{  v ,  Q  } } ']' ']'") :
  bi_scope.
Time
Notation "'WP' e @ E {{ v , Q } }" := (wp NotStuck E e%E (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' '[       ' @  E  {{  v ,  Q  } } ']' ']'") :
  bi_scope.
Time
Notation "'WP' e @ E ? {{ v , Q } }" := (wp MaybeStuck E e%E (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' '[        ' @  E  ? {{  v ,  Q  } } ']' ']'") :
  bi_scope.
Time
Notation "'WP' e {{ v , Q } }" := (wp NotStuck \226\138\164 e%E (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' '[   ' {{  v ,  Q  } } ']' ']'") : bi_scope.
Time
Notation "'WP' e ? {{ v , Q } }" := (wp MaybeStuck \226\138\164 e%E (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' '[    ' ? {{  v ,  Q  } } ']' ']'") : bi_scope.
Time
Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e @ s; E {{\206\166} }))%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  P  } } }  '/  ' e  '/' @  s ;  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") :
  bi_scope.
Time
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e @ E {{\206\166} }))%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") :
  bi_scope.
Time
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e @ E ? {{\206\166} }))%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  ? {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") :
  bi_scope.
Time
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e {{\206\166} }))%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  P  } } }  '/  ' e  '/' {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") :
  bi_scope.
Time
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e ? {{\206\166} }))%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  P  } } }  '/  ' e  '/' ? {{{  x  ..  y ,   RET  pat ;  Q  } } } ']'") :
  bi_scope.
Time
Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e @ s; E {{\206\166} }))%I
  (at level 20,
   format "'[hv' {{{  P  } } }  '/  ' e  '/' @  s ;  E  {{{  RET  pat ;  Q  } } } ']'") :
  bi_scope.
Time
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e @ E {{\206\166} }))%I
  (at level 20,
   format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  {{{  RET  pat ;  Q  } } } ']'") :
  bi_scope.
Time
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e @ E ? {{\206\166} }))%I
  (at level 20,
   format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  ? {{{  RET  pat ;  Q  } } } ']'") :
  bi_scope.
Time
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e {{\206\166} }))%I
  (at level 20,
   format "'[hv' {{{  P  } } }  '/  ' e  '/' {{{  RET  pat ;  Q  } } } ']'") :
  bi_scope.
Time
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e ? {{\206\166} }))%I
  (at level 20,
   format "'[hv' {{{  P  } } }  '/  ' e  '/' ? {{{  RET  pat ;  Q  } } } ']'") :
  bi_scope.
Time
Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e @ s; E {{\206\166} }) :
  stdpp_scope.
Time
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e @ E {{\206\166} }) :
  stdpp_scope.
Time
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e @ E ? {{\206\166} }) :
  stdpp_scope.
Time
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e {{\206\166} }) : stdpp_scope.
Time
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e ? {{\206\166} }) :
  stdpp_scope.
Time
Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e @ s; E {{\206\166} }) : stdpp_scope.
Time
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e @ E {{\206\166} }) : stdpp_scope.
Time
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e @ E ? {{\206\166} }) : stdpp_scope.
Time
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e {{\206\166} }) : stdpp_scope.
Time
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e ? {{\206\166} }) : stdpp_scope.
Time
Notation "'WP' e @ s ; E [{ \206\166 } ]" := (twp s E e%E \206\166)
  (at level 20, e, \206\166  at level 200, only parsing) : bi_scope.
Time
Notation "'WP' e @ E [{ \206\166 } ]" := (twp NotStuck E e%E \206\166)
  (at level 20, e, \206\166  at level 200, only parsing) : bi_scope.
Time
Notation "'WP' e @ E ? [{ \206\166 } ]" := (twp MaybeStuck E e%E \206\166)
  (at level 20, e, \206\166  at level 200, only parsing) : bi_scope.
Time
Notation "'WP' e [{ \206\166 } ]" := (twp NotStuck \226\138\164 e%E \206\166)
  (at level 20, e, \206\166  at level 200, only parsing) : bi_scope.
Time
Notation "'WP' e ? [{ \206\166 } ]" := (twp MaybeStuck \226\138\164 e%E \206\166)
  (at level 20, e, \206\166  at level 200, only parsing) : bi_scope.
Time
Notation "'WP' e @ s ; E [{ v , Q } ]" := (twp s E e%E (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' '[          ' @  s ;  E  [{  v ,  Q  } ] ']' ']'") :
  bi_scope.
Time
Notation "'WP' e @ E [{ v , Q } ]" := (twp NotStuck E e%E (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' '[       ' @  E  [{  v ,  Q  } ] ']' ']'") :
  bi_scope.
Time
Notation "'WP' e @ E ? [{ v , Q } ]" := (twp MaybeStuck E e%E (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' '[        ' @  E  ? [{  v ,  Q  } ] ']' ']'") :
  bi_scope.
Time
Notation "'WP' e [{ v , Q } ]" := (twp NotStuck \226\138\164 e%E (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' '[   ' [{  v ,  Q  } ] ']' ']'") : bi_scope.
Time
Notation "'WP' e ? [{ v , Q } ]" := (twp MaybeStuck \226\138\164 e%E (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' '[    ' ? [{  v ,  Q  } ] ']' ']'") : bi_scope.
Time
Notation "'[[{' P } ] ] e @ s ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e @ s; E [{\206\166} ]))%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  P  } ] ]  '/  ' e  '/' @  s ;  E  [[{  x  ..  y ,  RET  pat ;  Q  } ] ] ']'") :
  bi_scope.
Time
Notation "'[[{' P } ] ] e @ E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e @ E [{\206\166} ]))%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  P  } ] ]  '/  ' e  '/' @  E  [[{  x  ..  y ,  RET  pat ;  Q  } ] ] ']'") :
  bi_scope.
Time
Notation "'[[{' P } ] ] e @ E ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e @ E ? [{\206\166} ]))%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  P  } ] ]  '/  ' e  '/' @  E  ? [[{  x  ..  y ,  RET  pat ;  Q  } ] ] ']'") :
  bi_scope.
Time
Notation "'[[{' P } ] ] e [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e [{\206\166} ]))%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  P  } ] ]  '/  ' e  '/' [[{  x  ..  y ,  RET  pat ;  Q  } ] ] ']'") :
  bi_scope.
Time
Notation "'[[{' P } ] ] e ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e ? [{\206\166} ]))%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  P  } ] ]  '/  ' e  '/' ? [[{  x  ..  y ,   RET  pat ;  Q  } ] ] ']'") :
  bi_scope.
Time
Notation "'[[{' P } ] ] e @ s ; E [[{ 'RET' pat ; Q } ] ]" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e @ s; E [{\206\166} ]))%I
  (at level 20,
   format "'[hv' [[{  P  } ] ]  '/  ' e  '/' @  s ;  E  [[{  RET  pat ;  Q  } ] ] ']'") :
  bi_scope.
Time
Notation "'[[{' P } ] ] e @ E [[{ 'RET' pat ; Q } ] ]" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e @ E [{\206\166} ]))%I
  (at level 20,
   format "'[hv' [[{  P  } ] ]  '/  ' e  '/' @  E  [[{  RET  pat ;  Q  } ] ] ']'") :
  bi_scope.
Time
Notation "'[[{' P } ] ] e @ E ? [[{ 'RET' pat ; Q } ] ]" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e @ E ? [{\206\166} ]))%I
  (at level 20,
   format "'[hv' [[{  P  } ] ]  '/  ' e  '/' @  E  ? [[{  RET  pat ;  Q  } ] ] ']'") :
  bi_scope.
Time
Notation "'[[{' P } ] ] e [[{ 'RET' pat ; Q } ] ]" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e [{\206\166} ]))%I
  (at level 20,
   format "'[hv' [[{  P  } ] ]  '/  ' e  '/' [[{  RET  pat ;  Q  } ] ] ']'") :
  bi_scope.
Time
Notation "'[[{' P } ] ] e ? [[{ 'RET' pat ; Q } ] ]" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e ? [{\206\166} ]))%I
  (at level 20,
   format "'[hv' [[{  P  } ] ]  '/  ' e  '/' ? [[{  RET  pat ;  Q  } ] ] ']'") :
  bi_scope.
Time
Notation "'[[{' P } ] ] e @ s ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (\226\136\128 \206\166, P -\226\136\151 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e @ s; E [{\206\166} ]) :
  stdpp_scope.
Time
Notation "'[[{' P } ] ] e @ E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (\226\136\128 \206\166, P -\226\136\151 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e @ E [{\206\166} ]) :
  stdpp_scope.
Time
Notation "'[[{' P } ] ] e @ E ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (\226\136\128 \206\166, P -\226\136\151 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e @ E ? [{\206\166} ]) :
  stdpp_scope.
Time
Notation "'[[{' P } ] ] e [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (\226\136\128 \206\166, P -\226\136\151 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e [{\206\166} ]) : stdpp_scope.
Time
Notation "'[[{' P } ] ] e ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (\226\136\128 \206\166, P -\226\136\151 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat%V) ..) -\226\136\151 WP e ? [{\206\166} ]) : stdpp_scope.
Time
Notation "'[[{' P } ] ] e @ s ; E [[{ 'RET' pat ; Q } ] ]" :=
  (\226\136\128 \206\166, P -\226\136\151 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e @ s; E [{\206\166} ]) : stdpp_scope.
Time
Notation "'[[{' P } ] ] e @ E [[{ 'RET' pat ; Q } ] ]" :=
  (\226\136\128 \206\166, P -\226\136\151 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e @ E [{\206\166} ]) : stdpp_scope.
Time
Notation "'[[{' P } ] ] e @ E ? [[{ 'RET' pat ; Q } ] ]" :=
  (\226\136\128 \206\166, P -\226\136\151 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e @ E ? [{\206\166} ]) : stdpp_scope.
Time
Notation "'[[{' P } ] ] e [[{ 'RET' pat ; Q } ] ]" :=
  (\226\136\128 \206\166, P -\226\136\151 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e [{\206\166} ]) : stdpp_scope.
Time
Notation "'[[{' P } ] ] e ? [[{ 'RET' pat ; Q } ] ]" :=
  (\226\136\128 \206\166, P -\226\136\151 (Q -\226\136\151 \206\166 pat%V) -\226\136\151 WP e ? [{\206\166} ]) : stdpp_scope.

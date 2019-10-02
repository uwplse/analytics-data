Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqhRlcUN"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Export HOASCircuits.
Open Scope circ_scope.
Definition wproj {W1} {W2} (p : Pat (W1 \226\138\151 W2)) : Pat W1 * Pat W2 :=
  match p with
  | pair p1 p2 => (p1, p2)
  end.
Open Scope circ_scope.
Opaque wproj.
Global Opaque merge.
Global Opaque Ctx.
Global Opaque is_valid.
Fixpoint pair_circ' {W1 W2} (p : Pat W1) (c2 : Circuit W2) : 
Circuit (W1 \226\138\151 W2) :=
  match c2 with
  | output p2 => output (pair p p2)
  | gate g p1 f => gate g p1 (fun p2 => pair_circ' p (f p2))
  | lift p1 f => lift p1 (fun x => pair_circ' p (f x))
  end.
Fixpoint pair_circ {W1 W2} (c1 : Circuit W1) (c2 : Circuit W2) : 
Circuit (W1 \226\138\151 W2) :=
  match c1 with
  | output p1 => pair_circ' p1 c2
  | gate g p1 f => gate g p1 (fun p2 => pair_circ (f p2) c2)
  | lift p f => lift p (fun b => pair_circ (f b) c2)
  end.
Notation "( x , y , .. , z )" := (pair_circ .. (pair_circ x y) .. z) 
  (at level 0) : circ_scope.
Set Printing Coercions.
Notation letpair p1 p2 p c:= (let (p1, p2) := wproj p in c).
Notation "'box_' p \226\135\146 C" := (box (fun p => C)) (at level 13) : circ_scope.
Notation "'box_' () \226\135\146 C" := (box (fun _ => C)) (at level 13) : circ_scope.
Notation "'box_' ( p1 , p2 ) \226\135\146 C" := (box (fun p => letpair p1 p2 p C))
  (at level 13) : circ_scope.
Notation "'box_' ( p1 , p2 , p3 ) \226\135\146 C" :=
  (box (fun p => let (y, p3) := wproj p in let (p1, p2) := wproj y in C))
  (at level 13) : circ_scope.
Notation "'box_' ( p1 , ( p2 , p3 ) ) \226\135\146 C" :=
  (box (fun x => let (p1, y) := wproj x in let (p2, p3) := wproj y in C))
  (at level 13) : circ_scope.
Notation "'box_' ( ( p1 , p2 ) , ( p3 , p4 ) ) \226\135\146 C" :=
  (box
     (fun x =>
      let (y, z) := wproj x in
      let (p1, p2) := wproj y in let (p3, p4) := wproj z in C)) 
  (at level 13) : circ_scope.
Notation "()" := unit : circ_scope.
Notation "( x ,, y ,, .. ,, z )" := (pair .. (pair x y) .. z) 
  (at level 0) : circ_scope.
Notation comp p c1 c2:= (compose c1 (fun p => c2)).
Notation "'let_' p \226\134\144 c1 ; c2" := (comp p c1 c2) (at level 14, right associativity) :
  circ_scope.
Notation "'let_' () \226\134\144 c1 ; c2" := (compose c1 (fun _ => c2))
  (at level 14, right associativity) : circ_scope.
Notation "'let_' ( p1 , p2 ) \226\134\144 c1 ; c2" :=
  (compose c1 (fun x => letpair p1 p2 x c2)) (at level 14, right associativity) :
  circ_scope.
Notation "'let_' ( ( p1 , p2 ) , p3 ) \226\134\144 c1 ; c2" :=
  (compose c1 (fun x => let (y, p3) := wproj x in let (p1, p2) := wproj y in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'let_' ( p1 , p2 , p3 ) \226\134\144 c1 ; c2" :=
  (compose c1 (fun x => let (y, p3) := wproj x in let (p1, p2) := wproj y in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'let_' ( ( ( p1 , p2 ) , p3 ) , p4 ) \226\134\144 c1 ; c2" :=
  (compose c1
     (fun x =>
      let (y, p4) := wproj x in
      let (z, p3) := wproj y in let (p1, p2) := wproj z in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'let_' ( p1 , p2 , p3 , p4 ) \226\134\144 c1 ; c2" :=
  (compose c1
     (fun x =>
      let (y, p4) := wproj x in
      let (z, p3) := wproj y in let (p1, p2) := wproj z in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'let_' ( ( ( ( p1 , p2 ) , p3 ) , p4 ) , p5 ) \226\134\144 c1 ; c2" :=
  (compose c1
     (fun x =>
      let (y, p5) := wproj x in
      let (z, p4) := wproj y in
      let (a, p3) := wproj z in let (p1, p2) := wproj a in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'let_' ( p1 , p2 , p3 , p4 , p5 ) \226\134\144 c1 ; c2" :=
  (compose c1
     (fun x =>
      let (y, p5) := wproj x in
      let (z, p4) := wproj y in
      let (a, p3) := wproj z in let (p1, p2) := wproj a in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'let_' ( p1 , ( p2 , p3 ) ) \226\134\144 c1 ; c2" :=
  (compose c1 (fun x => let (p1, y) := wproj x in let (p2, p3) := wproj y in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'let_' ( p1 , ( p2 , ( p3 , p4 ) ) ) \226\134\144 c1 ; c2" :=
  (compose c1
     (fun x =>
      let (p1, y) := wproj x in
      let (p2, z) := wproj y in let (p3, p4) := wproj z in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'let_' ( p1 , ( p2 , ( p3 , ( p4 , p5 ) ) ) ) \226\134\144 c1 ; c2" :=
  (compose c1
     (fun x =>
      let (p1, y) := wproj x in
      let (p2, z) := wproj y in
      let (p3, a) := wproj z in let (p4, p5) := wproj a in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'let_' ( ( p1 , p2 ) , ( p3 , p4 ) ) \226\134\144 c1 ; c2" :=
  (compose c1
     (fun x =>
      let (y, z) := wproj x in
      let (p1, p2) := wproj y in let (p3, p4) := wproj z in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'let_' ( p1 , ( p2 , ( p3 , ( p4 , ( p5 , p6 ) ) ) ) ) \226\134\144 c1 ; c2" :=
  (compose c1
     (fun x =>
      let (p1, y) := wproj x in
      let (p2, z) := wproj y in
      let (p3, a) := wproj z in
      let (p4, b) := wproj a in let (p5, p6) := wproj b in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'gate_' p2 \226\134\144 g @ p ; c2" := (gate g p (fun p2 => c2))
  (at level 14, right associativity).
Notation "'gate_' () \226\134\144 g @ p ; c2" := (gate g p (fun _ => c2))
  (at level 14, right associativity).
Notation "'gate_' ( p1 , p2 ) \226\134\144 g @ p ; c2" :=
  (gate g p (fun x => letpair p1 p2 x c2)) (at level 14, right associativity) :
  circ_scope.
Notation "'gate_' ( p1 , p2 , p3 ) \226\134\144 g @ p ; c2" :=
  (gate g p (fun x => let (y, p3) := wproj x in let (p1, p2) := wproj y in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'gate_' ( ( p1 , p2 ) , p3 ) \226\134\144 g @ p ; c2" :=
  (gate g p (fun x => let (y, p3) := wproj x in let (p1, p2) := wproj y in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'gate_' ( p1 , ( p2 , p3 ) ) \226\134\144 g @ p ; c2" :=
  (gate g p (fun x => let (p1, y) := wproj x in let (p2, p3) := wproj y in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'gate_' ( ( p1 , p2 ) , ( p3 , p4 ) ) \226\134\144 g @ p ; c2" :=
  (gate g p
     (fun x =>
      let (y, z) := wproj x in
      let (p1, p2) := wproj y in let (p3, p4) := wproj z in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'gate_' ( p1 , ( p2 , ( p3 , ( p4 , ( p5 , p6 ) ) ) ) ) \226\134\144 g @ p ; c2" :=
  (gate g p
     (fun x =>
      let (p1, y) := wproj x in
      let (p2, z) := wproj y in
      let (p3, a) := wproj z in
      let (p4, b) := wproj a in let (p5, p6) := wproj b in c2))
  (at level 14, right associativity) : circ_scope.
Notation "'discard_' p ; c" := (gate discard p (fun _ => c))
  (at level 14, right associativity) : circ_scope.
Notation "'discard_' ( p1 , p2 ) ; c" :=
  (gate discard p1 (fun _ => gate discard p2 (fun _ => c)))
  (at level 14, right associativity) : circ_scope.
Notation "'discard_' ( p1 , p2 , p3 ) ; c" :=
  (gate discard p1
     (fun _ => gate discard p2 (fun _ => gate discard p3 (fun _ => c))))
  (at level 14, right associativity) : circ_scope.
Notation "'discard_' ( ( p1 , p2 ) , p3 ) ; c" :=
  (gate discard p1
     (fun _ => gate discard p2 (fun _ => gate discard p3 (fun _ => c))))
  (at level 14, right associativity) : circ_scope.
Notation "'discard_' ( p1 , ( p2 , p3 ) ) ; c" :=
  (gate discard p1
     (fun _ => gate discard p2 (fun _ => gate discard p3 (fun _ => c))))
  (at level 14, right associativity) : circ_scope.
Notation "'discard_' ( ( p1 , p2 ) , ( p3 , p4 ) ) ; c" :=
  (gate discard p1
     (fun _ =>
      gate discard p2
        (fun _ => gate discard p3 (fun _ => gate discard p4 (fun _ => c)))))
  (at level 14, right associativity) : circ_scope.
Delimit Scope circ_scope with qc.
Ltac goal_has_evars := match goal with
                       | |- ?G => has_evars G
                       end.
Ltac
 invert_patterns :=
  repeat
   match goal with
   | p:Pat One |- _ => dependent destruction p
   | p:Pat Qubit |- _ => dependent destruction p
   | p:Pat Bit |- _ => dependent destruction p
   | p:Pat (_ \226\138\151 _) |- _ => dependent destruction p
   | H:Types_Pat ?\206\147 () |- _ => is_var \206\147; inversion H; subst
   | H:Types_Pat ?\206\147 (qubit _) |- _ => is_var \206\147; inversion H; subst
   | H:Types_Pat ?\206\147 (bit _) |- _ => is_var \206\147; inversion H; subst
   | H:Types_Pat ?\206\147 (pair _ _) |- _ => is_var \206\147; dependent destruction H
   end.
Create HintDb typed_db.
Ltac
 type_check_once :=
  intros;
   try
    match goal with
    | |- Typed_Box _ => solve [ eauto with typed_db ]
    | |- @Typed_Box ?W1 ?W2 ?c => unfold Typed_Box in *; try unfold c
    end; intros; simpl in *; subst; invert_patterns;
   repeat
    match goal with
    | b:bool |- _ => destruct b
    | H:_ \226\169\181 _ \226\136\153 _ |- _ => destruct H
    | H:@Types_Circuit _ _ ?c |- @Types_Circuit _ _ ?c => exact H
    | |- @Types_Circuit _ _ _ => econstructor; type_check_once
    | |- @Types_Circuit _ _ (if ?b then _ else _) => destruct b; type_check_once
    | |- @Types_Circuit _ _ _ => eapply compose_typing; type_check_once
    | H:forall a b, Types_Pat _ _ -> Types_Circuit _ _
      |- Types_Circuit _ _ => apply H; type_check_once
    | H:@Types_Pat _ _ ?p |- @Types_Pat _ _ ?p => exact H
    | H:@Types_Pat ?\206\1471 _ ?p
      |- @Types_Pat ?\206\1472 _ ?p => replace \206\1472 with \206\1471; [ exact H | monoid ]
    | |- Types_Pat _ _ => econstructor; type_check_once
    | |- ?\206\147 \226\169\181 ?\206\1471 \226\136\153 ?\206\1472 => has_evars (\206\1471 \226\139\147 \206\1472 \226\139\147 \206\147)
    | |- _ \226\169\181 _ \226\136\153 _ => solve_merge
    end;
   match goal with
   | |- is_valid ?\206\147 => tryif has_evar \206\147 then idtac else (idtac; validate) 
   | |- ?G => tryif has_evars G then idtac else (idtac; monoid) 
   end.
Ltac
 type_check_num :=
  let pre := numgoals in
  idtac "Goals before: " pre ""; ([>type_check_once.. ]);
   (let post := numgoals in
    idtac "Goals after: " post "";
     tryif guard post<pre then type_check_num else idtac "done" ).
Ltac type_check := let n := numgoals in
                   do n ([>type_check_once.. ]).
Ltac destruct_merges := repeat match goal with
                               | H:_ \226\169\181 _ \226\136\153 _ |- _ => destruct H
                               end.
Definition cnot12 : Square_Box (Qubit \226\138\151 Qubit \226\138\151 Qubit) :=
  box_ (p0, p1, p2)\226\135\146 (gate_ (p3, p4)\226\134\144 CNOT @ (p1,, p2); output (p0,, p3,, p4)).
Lemma cnot12_WT_manual : Typed_Box cnot12.
Proof.
(unfold Typed_Box, cnot12).
(intros \206\147 p TP).
(simpl).
dependent destruction TP.
dependent destruction TP1.
rename \206\1470 into \206\147,\206\1471 into \206\1470.
rename \206\147 into \206\1471.
rename p3 into p1.
rename TP1_1 into TP0,TP1_2 into TP1.
(apply @types_gate with (\206\147 := \206\1470) (\206\1471 := \206\1471 \226\139\147 \206\1472); try solve_merge).
-
(apply types_pair with (\206\1471 := \206\1471) (\206\1472 := \206\1472); try solve_merge).
+
(apply TP1).
+
(apply TP2).
-
(intros \206\147 \206\147' p M TP).
dependent destruction TP.
(apply (@types_output _ _ _ _ eq_refl)).
(apply types_pair with (\206\1471 := \206\1470 \226\139\147 \206\1473) (\206\1472 := \206\1474); try solve_merge).
+
(apply types_pair with (\206\1471 := \206\1470) (\206\1472 := \206\1473); try solve_merge).
*
(apply TP0).
*
(apply TP3).
+
(apply TP4).
Qed.
Lemma cnot12_WT_evars : Typed_Box cnot12.
Proof.
(unfold Typed_Box, cnot12).
(intros; simpl).
invert_patterns.
(eapply types_gate).
1: {
(eapply @types_pair).
4: eauto.
3: eauto.
2: monoid.
1: validate.
}
2: {
split.
2: monoid.
1: validate.
}
1: {
(intros; simpl).
invert_patterns.
(eapply @types_output).
1: monoid.
1: {
(destruct_merges; subst).
(eapply @types_pair).
4: eauto.
3: {
(eapply @types_pair).
4: eauto.
3: eauto.
2: monoid.
1: validate.
}
2: monoid.
1: validate.
}
}
Qed.
Lemma cnot23_WT_evars' : Typed_Box cnot12.
Proof.
(unfold Typed_Box, cnot12).
(intros; simpl).
invert_patterns.
(eapply types_gate).
-
(eapply @types_pair).
3: eauto.
3: eauto.
2: monoid.
validate.
-
(intros; simpl).
invert_patterns.
(eapply @types_output).
+
monoid.
+
(destruct_merges; subst).
(eapply @types_pair).
4: eauto.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqSp51FQ"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
3: {
econstructor.
3: eauto.
3: eauto.
2: monoid.
validate.

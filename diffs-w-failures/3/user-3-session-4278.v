Time From iris.algebra Require Export ofe.
Time From iris.bi Require Export notation.
Time Set Primitive Projections.
Time Section bi_mixin.
Time Context {PROP : Type} `{Dist PROP} `{Equiv PROP}.
Time Context (bi_entails : PROP \226\134\146 PROP \226\134\146 Prop).
Time Context (bi_emp : PROP).
Time Context (bi_pure : Prop \226\134\146 PROP).
Time Context (bi_and : PROP \226\134\146 PROP \226\134\146 PROP).
Time Context (bi_or : PROP \226\134\146 PROP \226\134\146 PROP).
Time Context (bi_impl : PROP \226\134\146 PROP \226\134\146 PROP).
Time Context (bi_forall : \226\136\128 A, (A \226\134\146 PROP) \226\134\146 PROP).
Time Context (bi_exist : \226\136\128 A, (A \226\134\146 PROP) \226\134\146 PROP).
Time Context (bi_sep : PROP \226\134\146 PROP \226\134\146 PROP).
Time Context (bi_wand : PROP \226\134\146 PROP \226\134\146 PROP).
Time Context (bi_persistently : PROP \226\134\146 PROP).
Time Context (sbi_internal_eq : \226\136\128 A : ofeT, A \226\134\146 A \226\134\146 PROP).
Time Context (sbi_later : PROP \226\134\146 PROP).
Time #[local]Infix "\226\138\162" := bi_entails.
Time #[local]Notation "'emp'" := bi_emp.
Time #[local]Notation "'True'" := (bi_pure True).
Time #[local]Notation "'False'" := (bi_pure False).
Time #[local]Notation "'\226\140\156' \207\134 '\226\140\157'" := (bi_pure \207\134%type%stdpp).
Time #[local]Infix "\226\136\167" := bi_and.
Time #[local]Infix "\226\136\168" := bi_or.
Time #[local]Infix "\226\134\146" := bi_impl.
Time #[local]
Notation "\226\136\128 x .. y , P" := (bi_forall _ (\206\187 x, .. (bi_forall _ (\206\187 y, P)) ..)).
Time #[local]
Notation "\226\136\131 x .. y , P" := (bi_exist _ (\206\187 x, .. (bi_exist _ (\206\187 y, P)) ..)).
Time #[local]Infix "\226\136\151" := bi_sep.
Time #[local]Infix "-\226\136\151" := bi_wand.
Time #[local]Notation "'<pers>' P" := (bi_persistently P).
Time #[local]Notation "x \226\137\161 y" := (sbi_internal_eq _ x y).
Time #[local]Notation "\226\150\183 P" := (sbi_later P).
Time
Record BiMixin :={bi_mixin_entails_po : PreOrder bi_entails;
                  bi_mixin_equiv_spec :
                   forall P Q, equiv P Q \226\134\148 (P \226\138\162 Q) \226\136\167 (Q \226\138\162 P);
                  bi_mixin_pure_ne :
                   forall n, Proper (iff ==> dist n) bi_pure;
                  bi_mixin_and_ne : NonExpansive2 bi_and;
                  bi_mixin_or_ne : NonExpansive2 bi_or;
                  bi_mixin_impl_ne : NonExpansive2 bi_impl;
                  bi_mixin_forall_ne :
                   forall A n,
                   Proper (pointwise_relation _ (dist n) ==> dist n)
                     (bi_forall A);
                  bi_mixin_exist_ne :
                   forall A n,
                   Proper (pointwise_relation _ (dist n) ==> dist n)
                     (bi_exist A);
                  bi_mixin_sep_ne : NonExpansive2 bi_sep;
                  bi_mixin_wand_ne : NonExpansive2 bi_wand;
                  bi_mixin_persistently_ne : NonExpansive bi_persistently;
                  bi_mixin_pure_intro : forall (\207\134 : Prop) P, \207\134 \226\134\146 P \226\138\162 \226\140\156\207\134\226\140\157;
                  bi_mixin_pure_elim' :
                   forall (\207\134 : Prop) P, (\207\134 \226\134\146 True \226\138\162 P) \226\134\146 \226\140\156\207\134\226\140\157 \226\138\162 P;
                  bi_mixin_pure_forall_2 :
                   forall {A} (\207\134 : A \226\134\146 Prop), (\226\136\128 a, \226\140\156\207\134 a\226\140\157) \226\138\162 \226\140\156\226\136\128 a, \207\134 a\226\140\157;
                  bi_mixin_and_elim_l : forall P Q, P \226\136\167 Q \226\138\162 P;
                  bi_mixin_and_elim_r : forall P Q, P \226\136\167 Q \226\138\162 Q;
                  bi_mixin_and_intro :
                   forall P Q R, (P \226\138\162 Q) \226\134\146 (P \226\138\162 R) \226\134\146 P \226\138\162 Q \226\136\167 R;
                  bi_mixin_or_intro_l : forall P Q, P \226\138\162 P \226\136\168 Q;
                  bi_mixin_or_intro_r : forall P Q, Q \226\138\162 P \226\136\168 Q;
                  bi_mixin_or_elim :
                   forall P Q R, (P \226\138\162 R) \226\134\146 (Q \226\138\162 R) \226\134\146 P \226\136\168 Q \226\138\162 R;
                  bi_mixin_impl_intro_r :
                   forall P Q R, (P \226\136\167 Q \226\138\162 R) \226\134\146 P \226\138\162 Q \226\134\146 R;
                  bi_mixin_impl_elim_l' :
                   forall P Q R, (P \226\138\162 Q \226\134\146 R) \226\134\146 P \226\136\167 Q \226\138\162 R;
                  bi_mixin_forall_intro :
                   forall {A} P (\206\168 : A \226\134\146 PROP), (\226\136\128 a, P \226\138\162 \206\168 a) \226\134\146 P \226\138\162 \226\136\128 a, \206\168 a;
                  bi_mixin_forall_elim :
                   forall {A} {\206\168 : A \226\134\146 PROP} a, (\226\136\128 a, \206\168 a) \226\138\162 \206\168 a;
                  bi_mixin_exist_intro :
                   forall {A} {\206\168 : A \226\134\146 PROP} a, \206\168 a \226\138\162 \226\136\131 a, \206\168 a;
                  bi_mixin_exist_elim :
                   forall {A} (\206\166 : A \226\134\146 PROP) Q,
                   (\226\136\128 a, \206\166 a \226\138\162 Q) \226\134\146 (\226\136\131 a, \206\166 a) \226\138\162 Q;
                  bi_mixin_sep_mono :
                   forall P P' Q Q', (P \226\138\162 Q) \226\134\146 (P' \226\138\162 Q') \226\134\146 P \226\136\151 P' \226\138\162 Q \226\136\151 Q';
                  bi_mixin_emp_sep_1 : forall P, P \226\138\162 emp \226\136\151 P;
                  bi_mixin_emp_sep_2 : forall P, emp \226\136\151 P \226\138\162 P;
                  bi_mixin_sep_comm' : forall P Q, P \226\136\151 Q \226\138\162 Q \226\136\151 P;
                  bi_mixin_sep_assoc' : forall P Q R, (P \226\136\151 Q) \226\136\151 R \226\138\162 P \226\136\151 Q \226\136\151 R;
                  bi_mixin_wand_intro_r :
                   forall P Q R, (P \226\136\151 Q \226\138\162 R) \226\134\146 P \226\138\162 Q -\226\136\151 R;
                  bi_mixin_wand_elim_l' :
                   forall P Q R, (P \226\138\162 Q -\226\136\151 R) \226\134\146 P \226\136\151 Q \226\138\162 R;
                  bi_mixin_persistently_mono :
                   forall P Q, (P \226\138\162 Q) \226\134\146 <pers> P \226\138\162 <pers> Q;
                  bi_mixin_persistently_idemp_2 :
                   forall P, <pers> P \226\138\162 <pers> <pers> P;
                  bi_mixin_persistently_emp_2 : emp \226\138\162 <pers> emp;
                  bi_mixin_persistently_forall_2 :
                   forall {A} (\206\168 : A \226\134\146 PROP),
                   (\226\136\128 a, <pers> \206\168 a) \226\138\162 <pers> (\226\136\128 a, \206\168 a);
                  bi_mixin_persistently_exist_1 :
                   forall {A} (\206\168 : A \226\134\146 PROP),
                   <pers> (\226\136\131 a, \206\168 a) \226\138\162 \226\136\131 a, <pers> \206\168 a;
                  bi_mixin_persistently_absorbing :
                   forall P Q, <pers> P \226\136\151 Q \226\138\162 <pers> P;
                  bi_mixin_persistently_and_sep_elim :
                   forall P Q, <pers> P \226\136\167 Q \226\138\162 P \226\136\151 Q}.
Time
Record SbiMixin :={sbi_mixin_later_contractive : Contractive sbi_later;
                   sbi_mixin_internal_eq_ne :
                    forall A : ofeT, NonExpansive2 (sbi_internal_eq A);
                   sbi_mixin_internal_eq_refl :
                    forall {A : ofeT} P (a : A), P \226\138\162 a \226\137\161 a;
                   sbi_mixin_internal_eq_rewrite :
                    forall {A : ofeT} a b (\206\168 : A \226\134\146 PROP),
                    NonExpansive \206\168 \226\134\146 a \226\137\161 b \226\138\162 \206\168 a \226\134\146 \206\168 b;
                   sbi_mixin_fun_ext :
                    forall {A} {B : A \226\134\146 ofeT} (f g : ofe_fun B),
                    (\226\136\128 x, f x \226\137\161 g x) \226\138\162 f \226\137\161 g;
                   sbi_mixin_sig_eq :
                    forall {A : ofeT} (P : A \226\134\146 Prop) (x y : sig P),
                    `x \226\137\161 `y \226\138\162 x \226\137\161 y;
                   sbi_mixin_discrete_eq_1 :
                    forall {A : ofeT} (a b : A), Discrete a \226\134\146 a \226\137\161 b \226\138\162 \226\140\156a \226\137\161 b\226\140\157;
                   sbi_mixin_later_eq_1 :
                    forall {A : ofeT} (x y : A), Next x \226\137\161 Next y \226\138\162 \226\150\183 (x \226\137\161 y);
                   sbi_mixin_later_eq_2 :
                    forall {A : ofeT} (x y : A), \226\150\183 (x \226\137\161 y) \226\138\162 Next x \226\137\161 Next y;
                   sbi_mixin_later_mono : forall P Q, (P \226\138\162 Q) \226\134\146 \226\150\183 P \226\138\162 \226\150\183 Q;
                   sbi_mixin_later_intro : forall P, P \226\138\162 \226\150\183 P;
                   sbi_mixin_later_forall_2 :
                    forall {A} (\206\166 : A \226\134\146 PROP), (\226\136\128 a, \226\150\183 \206\166 a) \226\138\162 \226\150\183 (\226\136\128 a, \206\166 a);
                   sbi_mixin_later_exist_false :
                    forall {A} (\206\166 : A \226\134\146 PROP),
                    \226\150\183 (\226\136\131 a, \206\166 a) \226\138\162 \226\150\183 False \226\136\168 (\226\136\131 a, \226\150\183 \206\166 a);
                   sbi_mixin_later_sep_1 : forall P Q, \226\150\183 (P \226\136\151 Q) \226\138\162 \226\150\183 P \226\136\151 \226\150\183 Q;
                   sbi_mixin_later_sep_2 : forall P Q, \226\150\183 P \226\136\151 \226\150\183 Q \226\138\162 \226\150\183 (P \226\136\151 Q);
                   sbi_mixin_later_persistently_1 :
                    forall P, \226\150\183 <pers> P \226\138\162 <pers> \226\150\183 P;
                   sbi_mixin_later_persistently_2 :
                    forall P, <pers> \226\150\183 P \226\138\162 \226\150\183 <pers> P;
                   sbi_mixin_later_false_em :
                    forall P, \226\150\183 P \226\138\162 \226\150\183 False \226\136\168 (\226\150\183 False \226\134\146 P)}.
Time End bi_mixin.
Time
Structure bi :=
 Bi {bi_car :> Type;
     bi_dist : Dist bi_car;
     bi_equiv : Equiv bi_car;
     bi_entails : bi_car \226\134\146 bi_car \226\134\146 Prop;
     bi_emp : bi_car;
     bi_pure : Prop \226\134\146 bi_car;
     bi_and : bi_car \226\134\146 bi_car \226\134\146 bi_car;
     bi_or : bi_car \226\134\146 bi_car \226\134\146 bi_car;
     bi_impl : bi_car \226\134\146 bi_car \226\134\146 bi_car;
     bi_forall : \226\136\128 A, (A \226\134\146 bi_car) \226\134\146 bi_car;
     bi_exist : \226\136\128 A, (A \226\134\146 bi_car) \226\134\146 bi_car;
     bi_sep : bi_car \226\134\146 bi_car \226\134\146 bi_car;
     bi_wand : bi_car \226\134\146 bi_car \226\134\146 bi_car;
     bi_persistently : bi_car \226\134\146 bi_car;
     bi_ofe_mixin : OfeMixin bi_car;
     bi_bi_mixin :
      BiMixin bi_entails bi_emp bi_pure bi_and bi_or bi_impl bi_forall
        bi_exist bi_sep bi_wand bi_persistently}.
Time Coercion bi_ofeC (PROP : bi) : ofeT := OfeT PROP (bi_ofe_mixin PROP).
Time Canonical Structure bi_ofeC.
Time Instance: (Params (@bi_entails) 1) := { }.
Time Instance: (Params (@bi_emp) 1) := { }.
Time Instance: (Params (@bi_pure) 1) := { }.
Time Instance: (Params (@bi_and) 1) := { }.
Time Instance: (Params (@bi_or) 1) := { }.
Time Instance: (Params (@bi_impl) 1) := { }.
Time Instance: (Params (@bi_forall) 2) := { }.
Time Instance: (Params (@bi_exist) 2) := { }.
Time Instance: (Params (@bi_sep) 1) := { }.
Time Instance: (Params (@bi_wand) 1) := { }.
Time Instance: (Params (@bi_persistently) 1) := { }.
Time Arguments bi_car : simpl never.
Time Arguments bi_dist : simpl never.
Time Arguments bi_equiv : simpl never.
Time Arguments bi_entails {PROP} _%I _%I : simpl never,  rename.
Time Arguments bi_emp {PROP} : simpl never,  rename.
Time Arguments bi_pure {PROP} _%stdpp : simpl never,  rename.
Time Arguments bi_and {PROP} _%I _%I : simpl never,  rename.
Time Arguments bi_or {PROP} _%I _%I : simpl never,  rename.
Time Arguments bi_impl {PROP} _%I _%I : simpl never,  rename.
Time Arguments bi_forall {PROP} {_} _%I : simpl never,  rename.
Time Arguments bi_exist {PROP} {_} _%I : simpl never,  rename.
Time Arguments bi_sep {PROP} _%I _%I : simpl never,  rename.
Time Arguments bi_wand {PROP} _%I _%I : simpl never,  rename.
Time Arguments bi_persistently {PROP} _%I : simpl never,  rename.
Time
Structure sbi :=
 Sbi {sbi_car :> Type;
      sbi_dist : Dist sbi_car;
      sbi_equiv : Equiv sbi_car;
      sbi_entails : sbi_car \226\134\146 sbi_car \226\134\146 Prop;
      sbi_emp : sbi_car;
      sbi_pure : Prop \226\134\146 sbi_car;
      sbi_and : sbi_car \226\134\146 sbi_car \226\134\146 sbi_car;
      sbi_or : sbi_car \226\134\146 sbi_car \226\134\146 sbi_car;
      sbi_impl : sbi_car \226\134\146 sbi_car \226\134\146 sbi_car;
      sbi_forall : \226\136\128 A, (A \226\134\146 sbi_car) \226\134\146 sbi_car;
      sbi_exist : \226\136\128 A, (A \226\134\146 sbi_car) \226\134\146 sbi_car;
      sbi_sep : sbi_car \226\134\146 sbi_car \226\134\146 sbi_car;
      sbi_wand : sbi_car \226\134\146 sbi_car \226\134\146 sbi_car;
      sbi_persistently : sbi_car \226\134\146 sbi_car;
      sbi_internal_eq : \226\136\128 A : ofeT, A \226\134\146 A \226\134\146 sbi_car;
      sbi_later : sbi_car \226\134\146 sbi_car;
      sbi_ofe_mixin : OfeMixin sbi_car;
      sbi_cofe : Cofe (OfeT sbi_car sbi_ofe_mixin);
      sbi_bi_mixin :
       BiMixin sbi_entails sbi_emp sbi_pure sbi_and sbi_or sbi_impl
         sbi_forall sbi_exist sbi_sep sbi_wand sbi_persistently;
      sbi_sbi_mixin :
       SbiMixin sbi_entails sbi_pure sbi_or sbi_impl sbi_forall sbi_exist
         sbi_sep sbi_persistently sbi_internal_eq sbi_later}.
Time Instance: (Params (@sbi_later) 1) := { }.
Time Instance: (Params (@sbi_internal_eq) 1) := { }.
Time Arguments sbi_later {PROP} _%I : simpl never,  rename.
Time Arguments sbi_internal_eq {PROP} {_} _ _ : simpl never,  rename.
Time Coercion sbi_ofeC (PROP : sbi) : ofeT := OfeT PROP (sbi_ofe_mixin PROP).
Time Canonical Structure sbi_ofeC.
Time
Coercion sbi_bi (PROP : sbi) : bi :=
  {| bi_ofe_mixin := sbi_ofe_mixin PROP; bi_bi_mixin := sbi_bi_mixin PROP |}.
Time Canonical Structure sbi_bi.
Time #[global]Instance sbi_cofe'  (PROP : sbi): (Cofe PROP).
Time Proof.
Time (apply sbi_cofe).
Time Qed.
Time Arguments sbi_car : simpl never.
Time Arguments sbi_dist : simpl never.
Time Arguments sbi_equiv : simpl never.
Time Arguments sbi_entails {PROP} _%I _%I : simpl never,  rename.
Time Arguments sbi_emp {PROP} : simpl never,  rename.
Time Arguments sbi_pure {PROP} _%stdpp : simpl never,  rename.
Time Arguments sbi_and {PROP} _%I _%I : simpl never,  rename.
Time Arguments sbi_or {PROP} _%I _%I : simpl never,  rename.
Time Arguments sbi_impl {PROP} _%I _%I : simpl never,  rename.
Time Arguments sbi_forall {PROP} {_} _%I : simpl never,  rename.
Time Arguments sbi_exist {PROP} {_} _%I : simpl never,  rename.
Time Arguments sbi_sep {PROP} _%I _%I : simpl never,  rename.
Time Arguments sbi_wand {PROP} _%I _%I : simpl never,  rename.
Time Arguments sbi_persistently {PROP} _%I : simpl never,  rename.
Time Arguments sbi_internal_eq {PROP} {_} _ _ : simpl never,  rename.
Time Arguments sbi_later {PROP} _%I : simpl never,  rename.
Time Hint Extern 0 (bi_entails _ _) => reflexivity: core.
Time
Instance bi_rewrite_relation  (PROP : bi):
 (RewriteRelation (@bi_entails PROP)) := { }.
Time
Instance bi_inhabited  {PROP : bi}: (Inhabited PROP) :=
 (populate (bi_pure True)).
Time Notation "P \226\138\162 Q" := (bi_entails P%I Q%I) : stdpp_scope.
Time
Notation "P \226\138\162@{ PROP } Q" := (bi_entails (PROP:=PROP) P%I Q%I)
  (only parsing) : stdpp_scope.
Time Notation "(\226\138\162)" := bi_entails (only parsing) : stdpp_scope.
Time
Notation "(\226\138\162@{ PROP } )" := (bi_entails (PROP:=PROP)) 
  (only parsing) : stdpp_scope.
Time Notation "P \226\138\163\226\138\162 Q" := (equiv (A:=bi_car _) P%I Q%I) : stdpp_scope.
Time
Notation "P \226\138\163\226\138\162@{ PROP } Q" := (equiv (A:=bi_car PROP) P%I Q%I)
  (only parsing) : stdpp_scope.
Time Notation "(\226\138\163\226\138\162)" := (equiv (A:=bi_car _)) (only parsing) : stdpp_scope.
Time
Notation "(\226\138\163\226\138\162@{ PROP } )" := (equiv (A:=bi_car PROP)) 
  (only parsing) : stdpp_scope.
Time Notation "P -\226\136\151 Q" := (P \226\138\162 Q) : stdpp_scope.
Time Notation "'emp'" := bi_emp : bi_scope.
Time Notation "'\226\140\156' \207\134 '\226\140\157'" := (bi_pure \207\134%type%stdpp) : bi_scope.
Time Notation "'True'" := (bi_pure True) : bi_scope.
Time Notation "'False'" := (bi_pure False) : bi_scope.
Time Infix "\226\136\167" := bi_and : bi_scope.
Time Notation "(\226\136\167)" := bi_and (only parsing) : bi_scope.
Time Infix "\226\136\168" := bi_or : bi_scope.
Time Notation "(\226\136\168)" := bi_or (only parsing) : bi_scope.
Time Infix "\226\134\146" := bi_impl : bi_scope.
Time Infix "\226\136\151" := bi_sep : bi_scope.
Time Notation "(\226\136\151)" := bi_sep (only parsing) : bi_scope.
Time Notation "P -\226\136\151 Q" := (bi_wand P Q) : bi_scope.
Time
Notation "\226\136\128 x .. y , P" := (bi_forall (\206\187 x, .. (bi_forall (\206\187 y, P)) ..)%I) :
  bi_scope.
Time
Notation "\226\136\131 x .. y , P" := (bi_exist (\206\187 x, .. (bi_exist (\206\187 y, P)) ..)%I) :
  bi_scope.
Time Notation "'<pers>' P" := (bi_persistently P) : bi_scope.
Time Infix "\226\137\161" := sbi_internal_eq : bi_scope.
Time Notation "\226\150\183 P" := (sbi_later P) : bi_scope.
Time Coercion bi_emp_valid {PROP : bi} (P : PROP) : Prop := emp \226\138\162 P.
Time Coercion sbi_emp_valid {PROP : sbi} : PROP \226\134\146 Prop := bi_emp_valid.
Time Arguments bi_emp_valid {_} _%I : simpl never.
Time Typeclasses Opaque bi_emp_valid.
Time Module bi.
Time Section bi_laws.
Time Context {PROP : bi}.
Time Implicit Type \207\134 : Prop.
Time Implicit Types P Q R : PROP.
Time Implicit Type A : Type.
Time #[global]Instance entails_po : (PreOrder (@bi_entails PROP)).
Time Proof.
Time (eapply bi_mixin_entails_po, bi_bi_mixin).
Time Qed.
Time Lemma equiv_spec P Q : P \226\137\161 Q \226\134\148 (P \226\138\162 Q) \226\136\167 (Q \226\138\162 P).
Time Proof.
Time (eapply bi_mixin_equiv_spec, bi_bi_mixin).
Time Qed.
Time #[global]Instance pure_ne  n: (Proper (iff ==> dist n) (@bi_pure PROP)).
Time Proof.
Time (eapply bi_mixin_pure_ne, bi_bi_mixin).
Time Qed.
Time #[global]Instance and_ne : (NonExpansive2 (@bi_and PROP)).
Time Proof.
Time (eapply bi_mixin_and_ne, bi_bi_mixin).
Time Qed.
Time #[global]Instance or_ne : (NonExpansive2 (@bi_or PROP)).
Time Proof.
Time (eapply bi_mixin_or_ne, bi_bi_mixin).
Time Qed.
Time #[global]Instance impl_ne : (NonExpansive2 (@bi_impl PROP)).
Time Proof.
Time (eapply bi_mixin_impl_ne, bi_bi_mixin).
Time Qed.
Time #[global]
Instance forall_ne  A n:
 (Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_forall PROP A)).
Time Proof.
Time (eapply bi_mixin_forall_ne, bi_bi_mixin).
Time Qed.
Time #[global]
Instance exist_ne  A n:
 (Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_exist PROP A)).
Time Proof.
Time (eapply bi_mixin_exist_ne, bi_bi_mixin).
Time Qed.
Time #[global]Instance sep_ne : (NonExpansive2 (@bi_sep PROP)).
Time Proof.
Time (eapply bi_mixin_sep_ne, bi_bi_mixin).
Time Qed.
Time #[global]Instance wand_ne : (NonExpansive2 (@bi_wand PROP)).
Time Proof.
Time (eapply bi_mixin_wand_ne, bi_bi_mixin).
Time Qed.
Time #[global]
Instance persistently_ne : (NonExpansive (@bi_persistently PROP)).
Time Proof.
Time (eapply bi_mixin_persistently_ne, bi_bi_mixin).
Time Qed.
Time Lemma pure_intro (\207\134 : Prop) P : \207\134 \226\134\146 P \226\138\162 \226\140\156\207\134\226\140\157.
Time Proof.
Time (eapply bi_mixin_pure_intro, bi_bi_mixin).
Time Qed.
Time Lemma pure_elim' (\207\134 : Prop) P : (\207\134 \226\134\146 True \226\138\162 P) \226\134\146 \226\140\156\207\134\226\140\157 \226\138\162 P.
Time Proof.
Time (eapply bi_mixin_pure_elim', bi_bi_mixin).
Time Qed.
Time
Lemma pure_forall_2 {A} (\207\134 : A \226\134\146 Prop) : (\226\136\128 a, \226\140\156\207\134 a\226\140\157) \226\138\162@{ PROP} \226\140\156\226\136\128 a, \207\134 a\226\140\157.
Time Proof.
Time (eapply bi_mixin_pure_forall_2, bi_bi_mixin).
Time Qed.
Time Lemma and_elim_l P Q : P \226\136\167 Q \226\138\162 P.
Time Proof.
Time (eapply bi_mixin_and_elim_l, bi_bi_mixin).
Time Qed.
Time Lemma and_elim_r P Q : P \226\136\167 Q \226\138\162 Q.
Time Proof.
Time (eapply bi_mixin_and_elim_r, bi_bi_mixin).
Time Qed.
Time Lemma and_intro P Q R : (P \226\138\162 Q) \226\134\146 (P \226\138\162 R) \226\134\146 P \226\138\162 Q \226\136\167 R.
Time Proof.
Time (eapply bi_mixin_and_intro, bi_bi_mixin).
Time Qed.
Time Lemma or_intro_l P Q : P \226\138\162 P \226\136\168 Q.
Time Proof.
Time (eapply bi_mixin_or_intro_l, bi_bi_mixin).
Time Qed.
Time Lemma or_intro_r P Q : Q \226\138\162 P \226\136\168 Q.
Time Proof.
Time (eapply bi_mixin_or_intro_r, bi_bi_mixin).
Time Qed.
Time Lemma or_elim P Q R : (P \226\138\162 R) \226\134\146 (Q \226\138\162 R) \226\134\146 P \226\136\168 Q \226\138\162 R.
Time Proof.
Time (eapply bi_mixin_or_elim, bi_bi_mixin).
Time Qed.
Time Lemma impl_intro_r P Q R : (P \226\136\167 Q \226\138\162 R) \226\134\146 P \226\138\162 Q \226\134\146 R.
Time Proof.
Time (eapply bi_mixin_impl_intro_r, bi_bi_mixin).
Time Qed.
Time Lemma impl_elim_l' P Q R : (P \226\138\162 Q \226\134\146 R) \226\134\146 P \226\136\167 Q \226\138\162 R.
Time Proof.
Time (eapply bi_mixin_impl_elim_l', bi_bi_mixin).
Time Qed.
Time Lemma forall_intro {A} P (\206\168 : A \226\134\146 PROP) : (\226\136\128 a, P \226\138\162 \206\168 a) \226\134\146 P \226\138\162 \226\136\128 a, \206\168 a.
Time Proof.
Time (eapply bi_mixin_forall_intro, bi_bi_mixin).
Time Qed.
Time Lemma forall_elim {A} {\206\168 : A \226\134\146 PROP} a : (\226\136\128 a, \206\168 a) \226\138\162 \206\168 a.
Time Proof.
Time (eapply (bi_mixin_forall_elim bi_entails), bi_bi_mixin).
Time Qed.
Time Lemma exist_intro {A} {\206\168 : A \226\134\146 PROP} a : \206\168 a \226\138\162 \226\136\131 a, \206\168 a.
Time Proof.
Time (eapply bi_mixin_exist_intro, bi_bi_mixin).
Time Qed.
Time Lemma exist_elim {A} (\206\166 : A \226\134\146 PROP) Q : (\226\136\128 a, \206\166 a \226\138\162 Q) \226\134\146 (\226\136\131 a, \206\166 a) \226\138\162 Q.
Time Proof.
Time (eapply bi_mixin_exist_elim, bi_bi_mixin).
Time Qed.
Time Lemma sep_mono P P' Q Q' : (P \226\138\162 Q) \226\134\146 (P' \226\138\162 Q') \226\134\146 P \226\136\151 P' \226\138\162 Q \226\136\151 Q'.
Time Proof.
Time (eapply bi_mixin_sep_mono, bi_bi_mixin).
Time Qed.
Time Lemma emp_sep_1 P : P \226\138\162 emp \226\136\151 P.
Time Proof.
Time (eapply bi_mixin_emp_sep_1, bi_bi_mixin).
Time Qed.
Time Lemma emp_sep_2 P : emp \226\136\151 P \226\138\162 P.
Time Proof.
Time (eapply bi_mixin_emp_sep_2, bi_bi_mixin).
Time Qed.
Time Lemma sep_comm' P Q : P \226\136\151 Q \226\138\162 Q \226\136\151 P.
Time Proof.
Time (eapply (bi_mixin_sep_comm' bi_entails), bi_bi_mixin).
Time Qed.
Time Lemma sep_assoc' P Q R : (P \226\136\151 Q) \226\136\151 R \226\138\162 P \226\136\151 Q \226\136\151 R.
Time Proof.
Time (eapply bi_mixin_sep_assoc', bi_bi_mixin).
Time Qed.
Time Lemma wand_intro_r P Q R : (P \226\136\151 Q \226\138\162 R) \226\134\146 P \226\138\162 Q -\226\136\151 R.
Time Proof.
Time (eapply bi_mixin_wand_intro_r, bi_bi_mixin).
Time Qed.
Time Lemma wand_elim_l' P Q R : (P \226\138\162 Q -\226\136\151 R) \226\134\146 P \226\136\151 Q \226\138\162 R.
Time Proof.
Time (eapply bi_mixin_wand_elim_l', bi_bi_mixin).
Time Qed.
Time Lemma persistently_mono P Q : (P \226\138\162 Q) \226\134\146 <pers> P \226\138\162 <pers> Q.
Time Proof.
Time (eapply bi_mixin_persistently_mono, bi_bi_mixin).
Time Qed.
Time Lemma persistently_idemp_2 P : <pers> P \226\138\162 <pers> <pers> P.
Time Proof.
Time (eapply bi_mixin_persistently_idemp_2, bi_bi_mixin).
Time Qed.
Time Lemma persistently_emp_2 : emp \226\138\162@{ PROP} <pers> emp.
Time Proof.
Time (eapply bi_mixin_persistently_emp_2, bi_bi_mixin).
Time Qed.
Time
Lemma persistently_forall_2 {A} (\206\168 : A \226\134\146 PROP) :
  (\226\136\128 a, <pers> \206\168 a) \226\138\162 <pers> (\226\136\128 a, \206\168 a).
Time Proof.
Time (eapply bi_mixin_persistently_forall_2, bi_bi_mixin).
Time Qed.
Time
Lemma persistently_exist_1 {A} (\206\168 : A \226\134\146 PROP) :
  <pers> (\226\136\131 a, \206\168 a) \226\138\162 \226\136\131 a, <pers> \206\168 a.
Time Proof.
Time (eapply bi_mixin_persistently_exist_1, bi_bi_mixin).
Time Qed.
Time Lemma persistently_absorbing P Q : <pers> P \226\136\151 Q \226\138\162 <pers> P.
Time Proof.
Time (eapply (bi_mixin_persistently_absorbing bi_entails), bi_bi_mixin).
Time Qed.
Time Lemma persistently_and_sep_elim P Q : <pers> P \226\136\167 Q \226\138\162 P \226\136\151 Q.
Time Proof.
Time (eapply (bi_mixin_persistently_and_sep_elim bi_entails), bi_bi_mixin).
Time Qed.
Time End bi_laws.
Time Section sbi_laws.
Time Context {PROP : sbi}.
Time Implicit Type \207\134 : Prop.
Time Implicit Types P Q R : PROP.
Time #[global]
Instance internal_eq_ne  (A : ofeT):
 (NonExpansive2 (@sbi_internal_eq PROP A)).
Time Proof.
Time (eapply sbi_mixin_internal_eq_ne, sbi_sbi_mixin).
Time Qed.
Time Lemma internal_eq_refl {A : ofeT} P (a : A) : P \226\138\162 a \226\137\161 a.
Time Proof.
Time (eapply sbi_mixin_internal_eq_refl, sbi_sbi_mixin).
Time Qed.
Time
Lemma internal_eq_rewrite {A : ofeT} a b (\206\168 : A \226\134\146 PROP) :
  NonExpansive \206\168 \226\134\146 a \226\137\161 b \226\138\162 \206\168 a \226\134\146 \206\168 b.
Time Proof.
Time (eapply sbi_mixin_internal_eq_rewrite, sbi_sbi_mixin).
Time Qed.
Time
Lemma fun_ext {A} {B : A \226\134\146 ofeT} (f g : ofe_fun B) :
  (\226\136\128 x, f x \226\137\161 g x) \226\138\162@{ PROP} f \226\137\161 g.
Time Proof.
Time (eapply sbi_mixin_fun_ext, sbi_sbi_mixin).
Time Qed.
Time
Lemma sig_eq {A : ofeT} (P : A \226\134\146 Prop) (x y : sig P) :
  `x \226\137\161 `y \226\138\162@{ PROP} x \226\137\161 y.
Time Proof.
Time (eapply sbi_mixin_sig_eq, sbi_sbi_mixin).
Time Qed.
Time
Lemma discrete_eq_1 {A : ofeT} (a b : A) :
  Discrete a \226\134\146 a \226\137\161 b \226\138\162@{ PROP} \226\140\156a \226\137\161 b\226\140\157.
Time Proof.
Time (eapply sbi_mixin_discrete_eq_1, sbi_sbi_mixin).
Time Qed.
Time #[global]Instance later_contractive : (Contractive (@sbi_later PROP)).
Time Proof.
Time (eapply sbi_mixin_later_contractive, sbi_sbi_mixin).
Time Qed.
Time
Lemma later_eq_1 {A : ofeT} (x y : A) : Next x \226\137\161 Next y \226\138\162@{ PROP} \226\150\183 (x \226\137\161 y).
Time Proof.
Time (eapply sbi_mixin_later_eq_1, sbi_sbi_mixin).
Time Qed.
Time
Lemma later_eq_2 {A : ofeT} (x y : A) : \226\150\183 (x \226\137\161 y) \226\138\162@{ PROP} Next x \226\137\161 Next y.
Time Proof.
Time (eapply sbi_mixin_later_eq_2, sbi_sbi_mixin).
Time Qed.
Time Lemma later_mono P Q : (P \226\138\162 Q) \226\134\146 \226\150\183 P \226\138\162 \226\150\183 Q.
Time Proof.
Time (eapply sbi_mixin_later_mono, sbi_sbi_mixin).
Time Qed.
Time Lemma later_intro P : P \226\138\162 \226\150\183 P.
Time Proof.
Time (eapply sbi_mixin_later_intro, sbi_sbi_mixin).
Time Qed.
Time Lemma later_forall_2 {A} (\206\166 : A \226\134\146 PROP) : (\226\136\128 a, \226\150\183 \206\166 a) \226\138\162 \226\150\183 (\226\136\128 a, \206\166 a).
Time Proof.
Time (eapply sbi_mixin_later_forall_2, sbi_sbi_mixin).
Time Qed.
Time
Lemma later_exist_false {A} (\206\166 : A \226\134\146 PROP) :
  \226\150\183 (\226\136\131 a, \206\166 a) \226\138\162 \226\150\183 False \226\136\168 (\226\136\131 a, \226\150\183 \206\166 a).
Time Proof.
Time (eapply sbi_mixin_later_exist_false, sbi_sbi_mixin).
Time Qed.
Time Lemma later_sep_1 P Q : \226\150\183 (P \226\136\151 Q) \226\138\162 \226\150\183 P \226\136\151 \226\150\183 Q.
Time Proof.
Time (eapply sbi_mixin_later_sep_1, sbi_sbi_mixin).
Time Qed.
Time Lemma later_sep_2 P Q : \226\150\183 P \226\136\151 \226\150\183 Q \226\138\162 \226\150\183 (P \226\136\151 Q).
Time Proof.
Time (eapply sbi_mixin_later_sep_2, sbi_sbi_mixin).
Time Qed.
Time Lemma later_persistently_1 P : \226\150\183 <pers> P \226\138\162 <pers> \226\150\183 P.
Time Proof.
Time (eapply (sbi_mixin_later_persistently_1 bi_entails), sbi_sbi_mixin).
Time Qed.
Time Lemma later_persistently_2 P : <pers> \226\150\183 P \226\138\162 \226\150\183 <pers> P.
Time Proof.
Time (eapply (sbi_mixin_later_persistently_2 bi_entails), sbi_sbi_mixin).
Time Qed.
Time Lemma later_false_em P : \226\150\183 P \226\138\162 \226\150\183 False \226\136\168 (\226\150\183 False \226\134\146 P).
Time Proof.
Time (eapply sbi_mixin_later_false_em, sbi_sbi_mixin).
Time Qed.
Time End sbi_laws.
Time End bi.

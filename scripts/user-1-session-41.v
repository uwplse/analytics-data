(*3:*) Add Search Blacklist "Private_" "_subproof". 
(*4:*) Set Diffs "off". 
(*5:*) Set Printing Depth 50. 
(*6:*) Remove Search Blacklist "Private_" "_subproof". 
(*7:*) Add Search Blacklist "Private_" "_subproof". 
(*8:*) Set Printing Width 71. 
(*9:*) Set Silent. 
(*10:*) Set Bullet Behavior "Strict Subproofs". 
(*11:*) Require Import Coq.Sets.Powerset_facts. 
(*12:*) Require Import library. 
(*13:*) Definition set_map_fst {ST : Type} (e : Ensemble (ST * ST)%type) :=
  SetPMap e (fun x => Some (fst x)). 
(*14:*) Definition set_map_snd {ST : Type} (e : Ensemble (ST * ST)%type) :=
  SetPMap e (fun x => Some (snd x)). 
(*15:*) Theorem in_set_map_fst {ST : Type} :
  forall l x, In ST (set_map_fst l) x -> exists y, In _ l (x, y). 
(*16:*) Proof. 
(*17:*) (intros). 
(*18:*) (unfold set_map_fst in *). 
(*19:*) (inversion H). 
(*20:*) (destruct x0). 
(*21:*) (cbn in *). 
(*22:*) (inversion H1). 
(*23:*) subst. 
(*24:*) eauto. 
(*25:*) Qed. 
(*26:*) Theorem in_set_map_snd {ST : Type} :
  forall l y, In ST (set_map_snd l) y -> exists x, In _ l (x, y). 
(*27:*) Proof. 
(*28:*) (intros). 
(*29:*) (unfold set_map_snd in *). 
(*30:*) (inversion H). 
(*31:*) (destruct x). 
(*32:*) (cbn in *). 
(*33:*) (inversion H1). 
(*34:*) subst. 
(*35:*) eauto. 
(*36:*) Qed. 
(*37:*) Module AGT_Spec. 
(*38:*) Parameter (ST : Type). 
(*39:*) Parameter (GT : Type). 
(*40:*) Definition SetST := Ensemble ST. 
(*41:*) Parameter (Gamma : GT -> SetST). 
(*42:*) Parameter (Alpha : SetST -> GT -> Prop). 
(*43:*) Parameter
  (alpha_is_partial_function :
     forall S G G', Alpha S G -> Alpha S G' -> G = G'). 
(*44:*) Definition evidence := (GT * GT)%type. 
(*45:*) Parameter (static_pred : ST -> ST -> Prop). 
(*46:*) Definition SetST2 := Ensemble (ST * ST). 
(*47:*) Definition R (e : evidence) : SetST2 :=
  fun pair =>
  let (T1, T2) := pair in
  static_pred T1 T2 /\
  In _ (Gamma (fst e)) T1 /\ In _ (Gamma (snd e)) T2. 
(*48:*) Definition Gamma2 (e : evidence) : SetST2 :=
  fun pair =>
  let (T1, T2) := pair in
  In _ (Gamma (fst e)) T1 /\ In _ (Gamma (snd e)) T2. 
(*49:*) Record Alpha2 (eta : SetST2) (e : evidence) : Prop :=
 alpha2_c {proj1 : Alpha (set_map_fst eta) (fst e);
           proj2 : Alpha (set_map_snd eta) (snd e)}. 
(*50:*) Definition transitive_closure (left right : SetST2) : SetST2 :=
  fun pair : ST * ST =>
  let (T1, T3) := pair in
  exists T2, In _ left (T1, T2) /\ In _ right (T2, T3). 
(*51:*) Definition evidence_composition (e1 e2 e3 : evidence) : Prop :=
  Alpha2 (transitive_closure (R e1) (R e2)) e3. 
(*52:*) Parameter
  (gamma_completeness :
     forall e1 e2 e3,
     evidence_composition e1 e2 e3 ->
     transitive_closure (R e1) (R e2) = R e3). 
(*53:*) Theorem tc_assoc :
  forall s1 s2 s3 : SetST2,
  transitive_closure (transitive_closure s1 s2) s3 =
  transitive_closure s1 (transitive_closure s2 s3). 
(*54:*) Proof. 
(*55:*) (intros). 
(*56:*) (eapply Extensionality_Ensembles). 
(*57:*) (split; unfold Included; intros). 
(*58:*) - 
(*59:*) (unfold transitive_closure in *). 
(*60:*) (unfold In in *). 
(*61:*) (cbn in *). 
(*62:*) (destruct x). 
(*63:*) (destruct H). 
(*64:*) (destruct H). 
(*65:*) (destruct H). 
(*66:*) (destruct H). 
(*67:*) eauto. 
(*68:*) - 
(*69:*) (unfold transitive_closure in *). 
(*70:*) (unfold In in *). 
(*71:*) (cbn in *). 
(*72:*) (destruct x). 
(*73:*) (destruct H). 
(*74:*) (destruct H). 
(*75:*) (destruct H0). 
(*76:*) (destruct H0). 
(*77:*) eauto. 
(*78:*) Qed. 
(*79:*) Hint Constructors Alpha2. 
(*80:*) Transparent evidence_composition. 
(*81:*) Theorem ec_assoc :
  forall e1 e2 e3 e12 e23 el er : evidence,
  evidence_composition e1 e2 e12 ->
  evidence_composition e2 e3 e23 ->
  evidence_composition e12 e3 el ->
  evidence_composition e1 e23 er -> el = er. 
(*82:*) Proof. 
(*83:*) (intros). 
(*84:*) (inversion H). 
(*85:*) (inversion H0). 
(*86:*) (inversion H1). 
(*87:*) (inversion H2). 
(*88:*) subst. 
(*89:*) (enough
  (transitive_closure (R e12) (R e3) =
   transitive_closure (R e1) (R e23))). 
(*90:*) subst. 
(*91:*) (rewrite surjective_pairing). 
(*92:*) (rewrite surjective_pairing with (p := el)). 
(*93:*) (f_equal; eapply alpha_is_partial_function; eauto; rewrite H3; eauto). 
(*94:*) (eapply Extensionality_Ensembles). 
(*95:*) (split; unfold Included; intros). 
(*96:*) - 
(*97:*) (eapply gamma_completeness in H). 
(*98:*) (eapply gamma_completeness in H0). 
(*99:*) (rewrite <- H in *). 
(*100:*) (rewrite <- H0 in *). 
(*101:*) (rewrite tc_assoc in H3). 
(*102:*) eauto. 
(*103:*) - 
(*104:*) (eapply gamma_completeness in H). 
(*105:*) (eapply gamma_completeness in H0). 
(*106:*) (rewrite <- H in *). 
(*107:*) (rewrite <- H0 in *). 
(*108:*) (rewrite <- tc_assoc in H3). 
(*109:*) eauto. 
(*110:*) Qed. 
(*111:*) Parameter
  (alpha_complete : forall S, Inhabited _ S -> exists G, Alpha S G). 
(*112:*) Parameter
  (alpha_implies_inhabited : forall S G, Alpha S G -> Inhabited _ S). 
(*113:*) Theorem tc_left :
  forall l r x,
  In _ (set_map_fst (transitive_closure l r)) x ->
  In _ (set_map_fst l) x. 
(*114:*) Proof. 
(*115:*) (intros). 
(*116:*) (unfold set_map_fst in *). 
(*117:*) (unfold transitive_closure in *). 
(*118:*) (cbn in *). 
(*119:*) (inversion H). 
(*120:*) subst. 
(*121:*) (destruct x0). 
(*122:*) (cbn in *). 
(*123:*) (destruct H0). 
(*124:*) (destruct H0). 
(*125:*) (econstructor; eauto). 
(*126:*) Qed. 
(*127:*) Theorem tc_right :
  forall l r x,
  In _ (set_map_snd (transitive_closure l r)) x ->
  In _ (set_map_snd r) x. 
(*128:*) Proof. 
(*129:*) (intros). 
(*130:*) (unfold set_map_snd in *). 
(*131:*) (unfold transitive_closure in *). 
(*132:*) (cbn in *). 
(*133:*) (inversion H). 
(*134:*) subst. 
(*135:*) (destruct x0). 
(*136:*) (cbn in *). 
(*137:*) (destruct H0). 
(*138:*) (destruct H0). 
(*139:*) (econstructor; eauto). 
(*140:*) Qed. 
(*141:*) Theorem ec_r_exists :
  forall e1 e2 e12 e3 e4,
  evidence_composition e1 e2 e12 ->
  evidence_composition e12 e3 e4 ->
  exists e5, evidence_composition e2 e3 e5. 
(*142:*) Proof. 
(*143:*) (intros). 
(*144:*) (inversion H). 
(*145:*) (inversion H0). 
(*146:*) subst. 
(*147:*) (enough (Inhabited _ (set_map_fst (transitive_closure (R e2) (R e3))))). 
(*148:*) (enough (Inhabited _ (set_map_snd (transitive_closure (R e2) (R e3))))). 
(*149:*) (eapply alpha_complete in H2). 
(*150:*) (eapply alpha_complete in H1). 
(*151:*) (destruct H1). 
(*152:*) (destruct H2). 
(*153:*) exists (x, x0). 
(*154:*) (econstructor; cbn; eauto). 
(*155:*) - 
(*156:*) (unfold set_map_snd in *). 
(*157:*) (unfold transitive_closure in *). 
(*158:*) (cbn in *). 
(*159:*) (inversion H1). 
(*160:*) (inversion H2). 
(*161:*) (destruct x0). 
(*162:*) (inversion H4). 
(*163:*) subst. 
(*164:*) (unfold In in H3). 
(*165:*) (destruct H3). 
(*166:*) (cbn). 
(*167:*) exists s0. 
(*168:*) (unfold In). 
(*169:*) (cbn). 
(*170:*) (exists (x, s0); eauto). 
(*171:*) (cbn). 
(*172:*) (exists x0; eauto). 
(*173:*) - 
(*174:*) (eapply gamma_completeness in H0). 
(*175:*) (eapply gamma_completeness in H). 
(*176:*) (rewrite <- H in proj5). 
(*177:*) (rewrite <- H in proj6). 
(*178:*) (rewrite tc_assoc in proj6). 
(*179:*) (rewrite tc_assoc in proj5). 
(*180:*) (eapply alpha_implies_inhabited in proj6). 
(*181:*) (inversion proj6). 
(*182:*) (apply tc_right in H1). 
(*183:*) (apply in_set_map_snd in H1). 
(*184:*) (destruct H1). 
(*185:*) (unfold set_map_fst). 
(*186:*) econstructor. 
(*187:*) (econstructor; eauto). 
(*188:*) Qed. 
(*189:*) Theorem ec_l_exists :
  forall e1 e2 e3 e23 e4,
  evidence_composition e2 e3 e23 ->
  evidence_composition e1 e23 e4 ->
  exists e5, evidence_composition e1 e2 e5. 
(*190:*) Proof. 
(*191:*) (intros). 
(*192:*) (inversion H). 
(*193:*) (inversion H0). 
(*194:*) subst. 
(*195:*) (enough (Inhabited _ (set_map_fst (transitive_closure (R e1) (R e2))))). 
(*196:*) (enough (Inhabited _ (set_map_snd (transitive_closure (R e1) (R e2))))). 
(*197:*) (eapply alpha_complete in H2). 
(*198:*) (eapply alpha_complete in H1). 
(*199:*) (destruct H1). 
(*200:*) (destruct H2). 
(*201:*) exists (x, x0). 
(*202:*) (econstructor; eauto). 
(*203:*) - 
(*204:*) (unfold set_map_snd in *). 
(*205:*) (unfold transitive_closure in *). 
(*206:*) (cbn in *). 
(*207:*) (inversion H1). 
(*208:*) (inversion H2). 
(*209:*) (destruct x0). 
(*210:*) (inversion H4). 
(*211:*) subst. 
(*212:*) (unfold In in H3). 
(*213:*) (destruct H3). 
(*214:*) (cbn). 
(*215:*) exists s0. 
(*216:*) (unfold In). 
(*217:*) (cbn). 
(*218:*) (exists (x, s0); eauto). 
(*219:*) (cbn). 
(*220:*) (exists x0; eauto). 
(*221:*) - 
(*222:*) (eapply gamma_completeness in H0). 
(*223:*) (eapply gamma_completeness in H). 
(*224:*) (rewrite <- H in proj5). 
(*225:*) (rewrite <- H in proj6). 
(*226:*) (rewrite <- tc_assoc in proj6). 
(*227:*) (rewrite <- tc_assoc in proj5). 
(*228:*) (eapply alpha_implies_inhabited in proj5). 
(*229:*) (inversion proj5). 
(*230:*) (apply tc_left in H1). 
(*231:*) (apply in_set_map_fst in H1). 
(*232:*) (destruct H1). 
(*233:*) (unfold set_map_snd). 
(*234:*) econstructor. 
(*235:*) (econstructor; eauto). 
(*236:*) Qed. 
(*237:*) End AGT_Spec. 
(*238:*) Require Import Coq.Lists.List. 
(*239:*) Module AGT_Bounded_Rows_Details. 
(*240:*) Definition label := nat. 
(*241:*) Inductive ST : Type :=
  | SInt : ST
  | SBool : ST
  | SFun : ST -> ST -> ST
  | SRec : list (option ST) -> ST. 
(*242:*) Inductive Ann : Type :=
  | R : Ann
  | O : Ann. 
(*243:*) Inductive GT : Type :=
  | GDyn : GT
  | GInt : GT
  | GBool : GT
  | GFun : GT -> GT -> GT
  | GRec : list (option (Ann * GT)) -> GT
  | GRow : list (option (option (Ann * GT))) -> GT. 
(*244:*) Definition SetST := Ensemble ST. 
(*245:*) Fixpoint Gamma (G : GT) : SetST :=
  match G with
  | GDyn => Full_set _
  | GInt => Singleton _ SInt
  | GBool => Singleton _ SBool
  | GFun G_1 G_2 => zipWith_ensembles SFun (Gamma G_1) (Gamma G_2)
  | GRec l =>
      fun X =>
      exists l',
        X = SRec l' /\
        Forall2
          (fun (S' : option ST) (G' : option (Ensemble (option ST)))
           =>
           match S', G' with
           | None, None => True
           | S', Some G' => Ensembles.In _ G' S'
           | _, _ => False
           end) l'
          (map
             (option_map
                (fun pair =>
                 match pair return (Ensemble (option ST)) with
                 | (R, G) =>
                     fun OS =>
                     match OS with
                     | None => False
                     | Some T => Ensembles.In _ (Gamma G) T
                     end
                 | (O, G) =>
                     fun OS =>
                     match OS with
                     | None => True
                     | Some T => Ensembles.In _ (Gamma G) T
                     end
                 end)) l)
  | GRow l =>
      fun X =>
      exists l',
        X = SRec l' /\
        Forall2
          (fun (S' : option ST)
             (G' : option (option (Ensemble (option ST)))) =>
           match S', G' with
           | S', None => True
           | S', Some (Some G') => Ensembles.In _ G' S'
           | None, Some None => True
           | _, _ => False
           end) l'
          (map
             (option_map
                (option_map
                   (fun pair =>
                    match pair return (Ensemble (option ST)) with
                    | (R, G) =>
                        fun OS =>
                        match OS with
                        | None => False
                        | Some T => Ensembles.In _ (Gamma G) T
                        end
                    | (O, G) =>
                        fun OS =>
                        match OS with
                        | None => True
                        | Some T => Ensembles.In _ (Gamma G) T
                        end
                    end))) l)
  end. 
(*246:*) Unset Silent. 
(*247:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2). 
(*CANCEL 245*) 
(*249:*) Unset Silent. 
(*250:*) Set Diffs "off". 
(*251:*) Search -Ensemble -(list _). 
(*252:*) Search -(Ensemble (list _)). 
(*CANCEL 238*) 
(*254:*) Unset Silent. 
(*255:*) Set Diffs "off". 
(*256:*) Import Coq.Lists.List.ListNotations. 
(*257:*) Set Silent. 
(*258:*) Module AGT_Bounded_Rows_Details. 
(*259:*) Definition label := nat. 
(*260:*) Inductive ST : Type :=
  | SInt : ST
  | SBool : ST
  | SFun : ST -> ST -> ST
  | SRec : list (option ST) -> ST. 
(*261:*) Inductive Ann : Type :=
  | R : Ann
  | O : Ann. 
(*262:*) Inductive GT : Type :=
  | GDyn : GT
  | GInt : GT
  | GBool : GT
  | GFun : GT -> GT -> GT
  | GRec : list (option (Ann * GT)) -> GT
  | GRow : list (option (option (Ann * GT))) -> GT. 
(*263:*) Definition SetST := Ensemble ST. 
(*264:*) Fixpoint Gamma (G : GT) : SetST :=
  match G with
  | GDyn => Full_set _
  | GInt => Singleton _ SInt
  | GBool => Singleton _ SBool
  | GFun G_1 G_2 => zipWith_ensembles SFun (Gamma G_1) (Gamma G_2)
  | GRec l =>
      fun X =>
      exists l',
        X = SRec l' /\
        Forall2
          (fun (S' : option ST) (G' : option (Ensemble (option ST)))
           =>
           match S', G' with
           | None, None => True
           | S', Some G' => Ensembles.In _ G' S'
           | _, _ => False
           end) l'
          (map
             (option_map
                (fun pair =>
                 match pair return (Ensemble (option ST)) with
                 | (R, G) =>
                     fun OS =>
                     match OS with
                     | None => False
                     | Some T => Ensembles.In _ (Gamma G) T
                     end
                 | (O, G) =>
                     fun OS =>
                     match OS with
                     | None => True
                     | Some T => Ensembles.In _ (Gamma G) T
                     end
                 end)) l)
  | GRow l =>
      fun X =>
      exists l',
        X = SRec l' /\
        Forall2
          (fun (S' : option ST)
             (G' : option (option (Ensemble (option ST)))) =>
           match S', G' with
           | S', None => True
           | S', Some (Some G') => Ensembles.In _ G' S'
           | None, Some None => True
           | _, _ => False
           end) l'
          (map
             (option_map
                (option_map
                   (fun pair =>
                    match pair return (Ensemble (option ST)) with
                    | (R, G) =>
                        fun OS =>
                        match OS with
                        | None => False
                        | Some T => Ensembles.In _ (Gamma G) T
                        end
                    | (O, G) =>
                        fun OS =>
                        match OS with
                        | None => True
                        | Some T => Ensembles.In _ (Gamma G) T
                        end
                    end))) l)
  end. 
(*265:*) Unset Silent. 
(*266:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec nil)) (GRec []). 
(*CANCEL 264*) 
(*268:*) Unset Silent. 
(*269:*) Set Diffs "off". 
(*270:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec []). 
(*CANCEL 269*) 
(*272:*) Unset Silent. 
(*273:*) Set Diffs "off". 
(*274:*) Search -Infinite. 
(*FAILED 273*)
(*274:*) Search -list. 
(*276:*) Print nth. 
(*277:*) Print nth. 
(*278:*) Print SRec. 
(*279:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_req :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => SRec tl
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec ((R, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow []). 
(*FAILED 278*)
(*279:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_req :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec ((R, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow []). 
(*FAILED 278*)
(*279:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec ((R, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow []). 
(*FAILED 278*)
(*279:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (R, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow []). 
(*CANCEL 278*) 
(*284:*) Unset Silent. 
(*285:*) Set Diffs "off". 
(*286:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_none :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists tl, X = SRec (None :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) -> Alpha S (GRec (None :: tl))
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (R, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow []). 
(*FAILED 285*)
(*286:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists tl, X = SRec (None :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) -> Alpha S (GRec (None :: tl))
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (R, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow []). 
(*CANCEL 285*) 
(*289:*) Unset Silent. 
(*290:*) Set Diffs "off". 
(*291:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists tl, X = SRec (None :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) -> Alpha S (GRec (None :: tl))
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (R, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow []). 
(*CANCEL 290*) 
(*293:*) Unset Silent. 
(*294:*) Set Diffs "off". 
(*295:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists tl, X = SRec (None :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) -> Alpha S (GRec (None :: tl))
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (R, hd) :: tl))
  | alpha_rec_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (O, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow []). 
(*CANCEL 294*) 
(*297:*) Unset Silent. 
(*298:*) Set Diffs "off". 
(*299:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists tl, X = SRec (None :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) -> Alpha S (GRec (None :: tl))
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (R, hd) :: tl))
  | alpha_rec_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (O, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow []). 
(*CANCEL 298*) 
(*301:*) Unset Silent. 
(*302:*) Set Diffs "off". 
(*303:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists tl, X = SRec (None :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) -> Alpha S (GRec (None :: tl))
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (R, hd) :: tl))
  | alpha_rec_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (O, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow [])
  | alpha_row_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists tl, X = SRec (None :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) -> Alpha S (GRow (None :: tl))
  | alpha_row_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRow (Some (R, hd) :: tl))
  | alpha_row_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRow (Some (O, hd) :: tl)). 
(*FAILED 302*)
(*CANCEL 262*) 
(*305:*) Unset Silent. 
(*306:*) Set Diffs "off". 
(*307:*) Definition FromRow : option (option (Ann * GT)) := None. 
(*308:*) Definition AbsentLabel : option (option (Ann * GT)) := Some None. 
(*309:*) Definition SetST := Ensemble ST. 
(*310:*) Fixpoint Gamma (G : GT) : SetST :=
  match G with
  | GDyn => Full_set _
  | GInt => Singleton _ SInt
  | GBool => Singleton _ SBool
  | GFun G_1 G_2 => zipWith_ensembles SFun (Gamma G_1) (Gamma G_2)
  | GRec l =>
      fun X =>
      exists l',
        X = SRec l' /\
        Forall2
          (fun (S' : option ST) (G' : option (Ensemble (option ST)))
           =>
           match S', G' with
           | None, None => True
           | S', Some G' => Ensembles.In _ G' S'
           | _, _ => False
           end) l'
          (map
             (option_map
                (fun pair =>
                 match pair return (Ensemble (option ST)) with
                 | (R, G) =>
                     fun OS =>
                     match OS with
                     | None => False
                     | Some T => Ensembles.In _ (Gamma G) T
                     end
                 | (O, G) =>
                     fun OS =>
                     match OS with
                     | None => True
                     | Some T => Ensembles.In _ (Gamma G) T
                     end
                 end)) l)
  | GRow l =>
      fun X =>
      exists l',
        X = SRec l' /\
        Forall2
          (fun (S' : option ST)
             (G' : option (option (Ensemble (option ST)))) =>
           match S', G' with
           | S', None => True
           | S', Some (Some G') => Ensembles.In _ G' S'
           | None, Some None => True
           | _, _ => False
           end) l'
          (map
             (option_map
                (option_map
                   (fun pair =>
                    match pair return (Ensemble (option ST)) with
                    | (R, G) =>
                        fun OS =>
                        match OS with
                        | None => False
                        | Some T => Ensembles.In _ (Gamma G) T
                        end
                    | (O, G) =>
                        fun OS =>
                        match OS with
                        | None => True
                        | Some T => Ensembles.In _ (Gamma G) T
                        end
                    end))) l)
  end. 
(*311:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X ->
       X = SRec [] \/ (exists tl, X = SRec (None :: tl))) ->
      (exists tl, X = SRec (None :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) -> Alpha S (GRec (None :: tl))
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (R, hd) :: tl))
  | alpha_rec_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (O, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow [])
  | alpha_row_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X ->
       X = SRec [] \/ (exists tl, X = SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) -> Alpha S (GRow (AbsentLabel :: tl))
  | alpha_row_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRow (Some (R, hd) :: tl))
  | alpha_row_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd ->
      hd <> GDyn -> Alpha S (GRow (Some (O, hd) :: tl))
  | alpha_row_cons_row_skip_hd :
      forall S tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) Dyn -> Alpha S (GRow (FromRow :: tl)). 
(*FAILED 310*)
(*311:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X ->
       X = SRec [] \/ (exists tl, X = SRec (None :: tl))) ->
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) -> Alpha S (GRec (None :: tl))
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (R, hd) :: tl))
  | alpha_rec_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (O, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow [])
  | alpha_row_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X ->
       X = SRec [] \/ (exists tl, X = SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) -> Alpha S (GRow (AbsentLabel :: tl))
  | alpha_row_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRow (Some (R, hd) :: tl))
  | alpha_row_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd ->
      hd <> GDyn -> Alpha S (GRow (Some (O, hd) :: tl))
  | alpha_row_cons_row_skip_hd :
      forall S tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) Dyn -> Alpha S (GRow (FromRow :: tl)). 
(*FAILED 310*)
(*311:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X ->
       X = SRec [] \/ (exists tl, X = SRec (None :: tl))) ->
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) -> Alpha S (GRec (None :: tl))
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (R, hd) :: tl))
  | alpha_rec_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (O, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow [])
  | alpha_row_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X ->
       X = SRec [] \/ (exists tl, X = SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) -> Alpha S (GRow (AbsentLabel :: tl))
  | alpha_row_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRow (Some (Some (R, hd)) :: tl))
  | alpha_row_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd ->
      hd <> GDyn -> Alpha S (GRow (Some (Some (O, hd)) :: tl))
  | alpha_row_cons_row_skip_hd :
      forall S tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) Dyn -> Alpha S (GRow (FromRow :: tl)). 
(*FAILED 310*)
(*311:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X ->
       X = SRec [] \/ (exists tl, X = SRec (None :: tl))) ->
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) -> Alpha S (GRec (None :: tl))
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (R, hd) :: tl))
  | alpha_rec_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (O, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow [])
  | alpha_row_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X ->
       X = SRec [] \/ (exists tl, X = SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) -> Alpha S (GRow (AbsentLabel :: tl))
  | alpha_row_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRow (Some (Some (R, hd)) :: tl))
  | alpha_row_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd ->
      hd <> GDyn -> Alpha S (GRow (Some (Some (O, hd)) :: tl))
  | alpha_row_cons_row_skip_hd :
      forall S tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) Dyn -> Alpha S (GRow (FromRow :: tl)). 
(*FAILED 310*)
(*311:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X ->
       X = SRec [] \/ (exists tl, X = SRec (None :: tl))) ->
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) -> Alpha S (GRec (None :: tl))
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (R, hd) :: tl))
  | alpha_rec_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (O, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow [])
  | alpha_row_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X ->
       X = SRec [] \/ (exists tl, X = SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) -> Alpha S (GRow (AbsentLabel :: tl))
  | alpha_row_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRow (Some (Some (R, hd)) :: tl))
  | alpha_row_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd ->
      hd <> GDyn -> Alpha S (GRow (Some (Some (O, hd)) :: tl))
  | alpha_row_cons_row_skip_hd :
      forall S tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) GDyn -> Alpha S (GRow (FromRow :: tl)). 
(*CANCEL 310*) 
(*317:*) Unset Silent. 
(*318:*) Set Diffs "off". 
(*319:*) Inductive Alpha : SetST -> GT -> Prop :=
  | alpha_int : Alpha (Singleton _ SInt) GInt
  | alpha_bool : Alpha (Singleton _ SBool) GBool
  | alpha_fun :
      forall S G_1 G_2,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_1
            | _ => None
            end)) G_1 ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SFun S_1 S_2 => Some S_2
            | _ => None
            end)) G_2 -> Alpha S (GFun G_1 G_2)
  | alpha_rec_mt : Alpha (Singleton _ (SRec [])) (GRec [])
  | alpha_rec_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X ->
       X = SRec [] \/ (exists tl, X = SRec (None :: tl))) ->
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) -> Alpha S (GRec (None :: tl))
  | alpha_rec_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (R, hd) :: tl))
  | alpha_rec_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRec tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRec (Some (O, hd) :: tl))
  | alpha_row_mt :
      forall S,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (forall n,
       exists l_1,
         Ensembles.In _ S (SRec l_1) /\
         nth n l_1 None = None /\
         Alpha
           (SetPMap S
              (fun S =>
               match S with
               | SRec l => nth n l None
               | _ => None
               end)) GDyn) -> Alpha S (GRow [])
  | alpha_row_cons_none :
      forall S tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X ->
       X = SRec [] \/ (exists tl, X = SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) -> Alpha S (GRow (AbsentLabel :: tl))
  | alpha_row_cons_req :
      forall S hd tl,
      Inhabited _ S ->
      (forall X,
       Ensembles.In _ S X -> exists hd tl, X = SRec (Some hd :: tl)) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd -> Alpha S (GRow (Some (Some (R, hd)) :: tl))
  | alpha_row_cons_opt :
      forall S hd tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) hd ->
      hd <> GDyn -> Alpha S (GRow (Some (Some (O, hd)) :: tl))
  | alpha_row_cons_row_skip_hd :
      forall S tl,
      Inhabited _ S ->
      (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
      (exists hd tl, Ensembles.In _ S (SRec (Some hd :: tl))) ->
      Ensembles.In _ S (SRec []) \/
      (exists tl, Ensembles.In _ S (SRec (None :: tl))) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => Some (SRec tl)
            | _ => None
            end)) (GRow tl) ->
      Alpha
        (SetPMap S
           (fun S =>
            match S with
            | SRec (hd :: tl) => hd
            | _ => None
            end)) GDyn -> Alpha S (GRow (FromRow :: tl))
  | alpha_gdyn :
      forall S,
      Inhabited _ S ->
      S <> Singleton _ SInt ->
      S <> Singleton _ SBool ->
      ~
      (forall x,
       Ensembles.In _ S x -> exists T1, exists T2, x = SFun T1 T2) ->
      ~ (forall x, Ensembles.In _ S x -> exists l, x = SRec l) ->
      Alpha S GDyn. 
(*320:*) Theorem alpha_is_partial_function :
  forall S G G', Alpha S G -> Alpha S G' -> G = G'. 
(*321:*) Set Printing Width 94. 
(*323:*) Show. 
(*324:*) Proof. 
(*325:*) (intros). 
(*326:*) generalize dependent G'. 
(*327:*) (induction H). 
(*328:*) - 
(*329:*) (intros). 
(*CANCEL 327*) 
(*331:*) Unset Silent. 
(*334:*) Set Diffs "off". 
(*336:*) Set Printing Width 94. 
(*338:*) Show. 
(*339:*) - 
(*340:*) (intros; inversion H; eauto). 
(*FAILED 339*)
(*340:*) (intros). 
(*CANCEL 339*) 
(*343:*) Unset Silent. 
(*346:*) Set Diffs "off". 
(*348:*) Set Printing Width 94. 
(*350:*) Show. 
(*351:*) (intros; inversion H0; eauto). 
(*CANCEL 350*) 
(*353:*) Unset Silent. 
(*356:*) Set Diffs "off". 
(*358:*) Set Printing Width 94. 
(*360:*) Show. 
(*361:*) (intros; inversion H0; subst; eauto). 
(*362:*) intuition. 
(*CANCEL 362*) 
(*364:*) Unset Silent. 
(*367:*) Set Diffs "off". 
(*CANCEL 361*) 
(*370:*) Unset Silent. 
(*373:*) Set Diffs "off". 
(*375:*) Set Printing Width 94. 
(*377:*) Show. 
(*378:*) congruence. 
(*FAILED 377*)
(*378:*) Search -Singleton. 
(*380:*) Search -(Singleton _ _ = Singleton _ _). 
(*CANCEL 319*) 
(*382:*) Unset Silent. 
(*384:*) Set Diffs "off". 
(*385:*) Create HintDb agt discriminated. 
(*386:*) Hint Resolve Singleton_eq: agt. 
(*FAILED 385*)
(*386:*) Hint Resolve singleton_eq: agt. 
(*388:*) Theorem alpha_is_partial_function :
  forall S G G', Alpha S G -> Alpha S G' -> G = G'. 
(*389:*) Set Printing Width 94. 
(*391:*) Show. 
(*392:*) Proof. 
(*393:*) (intros). 
(*394:*) generalize dependent G'. 
(*395:*) (induction H). 
(*396:*) - 
(*397:*) (intros; inversion H0; subst; eauto with agt). 
(*CANCEL 396*) 
(*399:*) Unset Silent. 
(*402:*) Set Diffs "off". 
(*404:*) Set Printing Width 94. 
(*406:*) Show. 
(*407:*) (intros; inversion H0; subst; eapply singleton_eq). 
(*CANCEL 394*) 
(*409:*) Unset Silent. 
(*412:*) Set Diffs "off". 
(*414:*) Set Printing Width 94. 
(*416:*) Show. 
(*417:*) (induction H). 
(*418:*) - 
(*419:*) (intros; inversion H0; subst; eapply singleton_eq; eauto). 
(*420:*) subst. 
(*421:*) Show. 
(*CANCEL 419*) 
(*423:*) Unset Silent. 
(*426:*) Set Diffs "off". 
(*428:*) Set Printing Width 94. 
(*430:*) Show. 
(*431:*) eauto. 
(*CANCEL 430*) 
(*433:*) Unset Silent. 
(*436:*) Set Diffs "off". 
(*CANCEL 418*) 
(*439:*) Unset Silent. 
(*442:*) Set Diffs "off". 
(*444:*) Set Printing Width 94. 
(*446:*) Show. 
(*447:*) (intros; inversion H0; subst; eapply singleton_eq; try rewrite H1; eauto). 
(*CANCEL 446*) 
(*449:*) Unset Silent. 
(*452:*) Set Diffs "off". 
(*454:*) Set Printing Width 94. 
(*456:*) Show. 
(*457:*) (intros; inversion H0; subst; eapply singleton_eq; eauto). 
(*CANCEL 456*) 
(*459:*) Unset Silent. 
(*462:*) Set Diffs "off". 
(*464:*) Set Printing Width 94. 
(*466:*) Show. 
(*467:*) (intros; inversion H0; subst; eapply singleton_eq; eauto; try rewrite H1; eauto). 
(*CANCEL 466*) 
(*469:*) Unset Silent. 
(*472:*) Set Diffs "off". 
(*474:*) Set Printing Width 94. 
(*476:*) Show. 
(*477:*) (intros; inversion H0; subst). 
(*CANCEL 476*) 
(*479:*) Unset Silent. 
(*482:*) Set Diffs "off". 
(*484:*) Set Printing Width 94. 
(*486:*) Show. 
(*487:*) (intros; inversion H0; subst; eauto). 
(*488:*) all: (try rewrite singleton_eq in H1; eauto). 
(*CANCEL 487*) 
(*490:*) Unset Silent. 
(*493:*) Set Diffs "off". 
(*495:*) Set Printing Width 94. 
(*497:*) Show. 
(*498:*) all: (try rewrite singleton_eq in H1; congruence). 
(*FAILED 497*)
(*498:*) all: (try rewrite singleton_eq in H1). 
(*CANCEL 497*) 
(*501:*) Unset Silent. 
(*504:*) Set Diffs "off". 
(*506:*) Set Printing Width 94. 
(*508:*) Show. 
(*509:*) all: (try apply singleton_eq in H1). 
(*CANCEL 508*) 
(*511:*) Unset Silent. 
(*514:*) Set Diffs "off". 
(*516:*) Set Printing Width 94. 
(*518:*) Show. 
(*519:*) all: (try apply singleton_eq in H1; congruence). 
(*FAILED 518*)
(*519:*) all: (try (apply singleton_eq in H1; congruence)). 
(*521:*) Search -(Ensembles.In _ (Singleton _ _) _). 
(*522:*) all: (try specialize (H1 _ (In_singleton _ _ _))). 
(*523:*) specialize (H1 _ (In_singleton _ _ _)). 
(*FAILED 522*)
(*523:*) specialize (H1 _ (In_singleton _ _)). 
(*CANCEL 522*) 
(*526:*) Unset Silent. 
(*529:*) Set Diffs "off". 
(*531:*) Show Intros. 
(*532:*) Set Printing Width 94. 
(*534:*) Show. 
(*535:*) all: (try specialize (H1 _ (In_singleton _))). 
(*536:*) Show. 
(*CANCEL 534*) 
(*538:*) Unset Silent. 
(*541:*) Set Diffs "off". 
(*543:*) Set Printing Width 94. 
(*545:*) Show. 
(*546:*) all: (try specialize (H1 _ (In_singleton _ _))). 
(*547:*) all: (try congruence). 
(*CANCEL 546*) 
(*549:*) Unset Silent. 
(*552:*) Set Diffs "off". 
(*554:*) Show. 
(*555:*) Set Printing Width 94. 
(*557:*) Show. 
(*558:*) destruct_pairs. 
(*FAILED 557*)
(*558:*) all: (repeat match goal with
             | H:exists _, _ |- _ => destruct H
             end). 
(*560:*) all: congruence. 
(*FAILED 559*)
(*560:*) all: (try congruence). 
(*CANCEL 557*) 
(*563:*) Unset Silent. 
(*566:*) Set Diffs "off". 
(*568:*) Set Printing Width 94. 
(*570:*) Show. 
(*571:*) all:
 (repeat
   match goal with
   | H:exists _, _ |- _ => destruct H
   | H:_ \/ _ |- _ => inversion H; clear H
   end). 
(*572:*) all: (try congruence). 
(*CANCEL 416*) 
(*574:*) Unset Silent. 
(*577:*) Set Diffs "off". 
(*579:*) Set Printing Width 94. 
(*581:*) Show. 
(*582:*) (induction H). 
(*583:*) Set Silent. 
(*585:*) - 
(*586:*) (intros; inversion H0; subst; eauto). 
(*587:*) all: (try (apply singleton_eq in H1; congruence)). 
(*588:*) all: (try specialize (H1 _ (In_singleton _ _ _))). 
(*589:*) all: (try specialize (H1 _ (In_singleton _ _))). 
(*590:*) all:
 (repeat
   match goal with
   | H:exists _, _ |- _ => destruct H
   | H:_ \/ _ |- _ => inversion H; clear H
   end). 
(*591:*) all: (try congruence). 
(*592:*) - 
(*593:*) (intros; inversion H0; subst; eauto). 
(*594:*) all: (try (apply singleton_eq in H1; congruence)). 
(*595:*) all: (try specialize (H1 _ (In_singleton _ _ _))). 
(*596:*) all: (try specialize (H1 _ (In_singleton _ _))). 
(*597:*) all:
 (repeat
   match goal with
   | H:exists _, _ |- _ => destruct H
   | H:_ \/ _ |- _ => inversion H; clear H
   end). 
(*598:*) Unset Silent. 
(*600:*) all: (try congruence). 
(*601:*) Set Silent. 
(*603:*) - 
(*604:*) (intros; inversion H0; subst; eauto). 
(*CANCEL 603*)
(*604:*) Unset Silent. 
(*607:*) Show. 
(*608:*) specialize (IHAlpha1 _ H1). 
(*CANCEL 607*) 
(*610:*) Unset Silent. 
(*613:*) Set Diffs "off". 
(*615:*) Set Printing Width 94. 
(*617:*) Show. 
(*618:*) (intros). 
(*CANCEL 387*) 
(*620:*) Unset Silent. 
(*622:*) Set Diffs "off". 
(*623:*) Set Printing Width 94. 
(*624:*) Lemma alpha_fun_inversion :
  forall S,
  (forall X, Ensembles.In _ S X -> exists S_1 S_2, X = SFun S_1 S_2) ->
  forall G, Alpha S G -> exists G_1 G_2, G = GFun G_1 G_2. 
(*625:*) Proof. 
(*626:*) (intros). 
(*627:*) (inversion H0). 
(*CANCEL 626*) 
(*629:*) Unset Silent. 
(*632:*) Set Diffs "off". 
(*634:*) Set Printing Width 94. 
(*636:*) Show. 
(*637:*) (inversion H0). 
(*CANCEL 636*) 
(*639:*) Unset Silent. 
(*642:*) Set Diffs "off". 
(*644:*) Set Printing Width 94. 
(*646:*) Show. 
(*647:*) (inversion H0). 
(*CANCEL 646*) 
(*649:*) Unset Silent. 
(*652:*) Set Diffs "off". 
(*654:*) Set Printing Width 94. 
(*656:*) Show. 
(*657:*) (inversion H0; subst). 
(*658:*) - 
(*659:*) specialize (H _ (In_singleton _ _)). 
(*660:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*CANCEL 659*) 
(*662:*) Unset Silent. 
(*665:*) Set Diffs "off". 
(*667:*) Set Printing Width 94. 
(*669:*) Show. 
(*670:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*671:*) congruence. 
(*672:*) Set Silent. 
(*674:*) - 
(*675:*) specialize (H _ (In_singleton _ _)). 
(*676:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*677:*) Unset Silent. 
(*679:*) congruence. 
(*680:*) Set Silent. 
(*682:*) - 
(*683:*) specialize (H _ (In_singleton _ _)). 
(*CANCEL 682*)
(*683:*) Unset Silent. 
(*686:*) Show. 
(*CANCEL 679*) 
(*688:*) Unset Silent. 
(*691:*) Set Diffs "off". 
(*693:*) Set Printing Width 94. 
(*695:*) Show. 
(*696:*) Set Silent. 
(*698:*) - 
(*699:*) Unset Silent. 
(*701:*) eauto. 
(*702:*) - 
(*703:*) specialize (H _ (In_singleton _ _)). 
(*704:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*705:*) congruence. 
(*706:*) - 
(*707:*) (destruct H3). 
(*708:*) (apply H in H3). 
(*709:*) Set Silent. 
(*711:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*712:*) Unset Silent. 
(*714:*) congruence. 
(*715:*) - 
(*716:*) (inversion H1). 
(*717:*) specialize (H _ H5). 
(*718:*) specialize (H2 _ H5). 
(*719:*) Set Silent. 
(*721:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*722:*) Unset Silent. 
(*724:*) congruence. 
(*725:*) Set Silent. 
(*727:*) - 
(*728:*) (inversion H1). 
(*729:*) specialize (H _ H5). 
(*CANCEL 728*)
(*729:*) Unset Silent. 
(*732:*) Show. 
(*CANCEL 727*) 
(*734:*) Unset Silent. 
(*737:*) Set Diffs "off". 
(*739:*) Set Printing Width 94. 
(*741:*) Show. 
(*742:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*743:*) specialize (H _ H7). 
(*744:*) specialize (H2 _ H7). 
(*745:*) congruence. 
(*FAILED 744*)
(*745:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*747:*) congruence. 
(*748:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*CANCEL 747*) 
(*750:*) Unset Silent. 
(*753:*) Set Diffs "off". 
(*755:*) Set Printing Width 94. 
(*757:*) Show. 
(*758:*) specialize (H _ H4). 
(*759:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*760:*) congruence. 
(*CANCEL 744*) 
(*762:*) Unset Silent. 
(*765:*) Set Diffs "off". 
(*767:*) Set Printing Width 94. 
(*769:*) Show. 
(*770:*) 2: specialize (H _ H4). 
(*771:*) all:
 (repeat
   match goal with
   | H:exists _, _ |- _ => destruct H
   | H:_ \/ _ |- _ => inversion H; clear H
   end). 
(*772:*) all: congruence. 
(*773:*) - 
(*CANCEL 772*) 
(*775:*) Unset Silent. 
(*778:*) Set Diffs "off". 
(*780:*) Set Printing Width 94. 
(*782:*) Show. 
(*783:*) Set Silent. 
(*785:*) - 
(*786:*) (destruct H3). 
(*CANCEL 785*)
(*786:*) Unset Silent. 
(*789:*) Show. 
(*CANCEL 782*) 
(*791:*) Unset Silent. 
(*794:*) Set Diffs "off". 
(*796:*) Set Printing Width 94. 
(*798:*) Show. 
(*799:*) Set Silent. 
(*801:*) - 
(*802:*) (inversion H1). 
(*803:*) specialize (H _ H5). 
(*CANCEL 802*)
(*803:*) Unset Silent. 
(*806:*) Show. 
(*807:*) specialize (H _ H4). 
(*808:*) specialize (H2 _ H4). 
(*809:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*810:*) congruence. 
(*811:*) - 
(*CANCEL 810*) 
(*813:*) Unset Silent. 
(*816:*) Set Diffs "off". 
(*818:*) Set Printing Width 94. 
(*820:*) Show. 
(*821:*) Set Silent. 
(*823:*) - 
(*824:*) (inversion H1). 
(*825:*) specialize (H _ H4). 
(*826:*) specialize (H2 _ H4). 
(*827:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*828:*) Unset Silent. 
(*830:*) congruence. 
(*CANCEL 827*) 
(*832:*) Unset Silent. 
(*835:*) Set Diffs "off". 
(*CANCEL 826*) 
(*838:*) Unset Silent. 
(*841:*) Set Diffs "off". 
(*CANCEL 825*) 
(*844:*) Unset Silent. 
(*847:*) Set Diffs "off". 
(*849:*) Set Printing Width 94. 
(*851:*) Show. 
(*852:*) specialize (H2 _ H4). 
(*853:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end; congruence). 
(*854:*) - 
(*CANCEL 853*) 
(*856:*) Unset Silent. 
(*859:*) Set Diffs "off". 
(*861:*) Set Printing Width 94. 
(*863:*) Show. 
(*864:*) Set Silent. 
(*866:*) - 
(*867:*) (inversion H1). 
(*868:*) specialize (H _ H4). 
(*CANCEL 867*)
(*868:*) Unset Silent. 
(*871:*) Show. 
(*872:*) specialize (H _ H5). 
(*873:*) specialize (H2 _ H5). 
(*874:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end; congruence). 
(*875:*) - 
(*CANCEL 874*) 
(*877:*) Unset Silent. 
(*880:*) Set Diffs "off". 
(*882:*) Set Printing Width 94. 
(*884:*) Show. 
(*885:*) Set Silent. 
(*887:*) - 
(*888:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*889:*) specialize (H _ H7). 
(*CANCEL 888*)
(*889:*) Unset Silent. 
(*892:*) Show. 
(*893:*) specialize (H _ H8). 
(*894:*) specialize (H2 _ H8). 
(*895:*) 2: specialize (H _ H4). 
(*896:*) all:
 (repeat
   match goal with
   | H:exists _, _ |- _ => destruct H
   | H:_ \/ _ |- _ => inversion H; clear H
   end). 
(*897:*) all: congruence. 
(*898:*) - 
(*CANCEL 897*) 
(*900:*) Unset Silent. 
(*903:*) Set Diffs "off". 
(*905:*) Set Printing Width 94. 
(*907:*) Show. 
(*908:*) Set Silent. 
(*910:*) - 
(*911:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*912:*) specialize (H _ H8). 
(*CANCEL 911*)
(*912:*) Unset Silent. 
(*915:*) Show. 
(*916:*) specialize (H _ H7). 
(*917:*) specialize (H2 _ H7). 
(*918:*) 2: specialize (H _ H4). 
(*919:*) all:
 (repeat
   match goal with
   | H:exists _, _ |- _ => destruct H
   | H:_ \/ _ |- _ => inversion H; clear H
   end). 
(*920:*) all: congruence. 
(*921:*) - 
(*922:*) congruence. 
(*923:*) Qed. 
(*924:*) Lemma alpha_rec_inversion :
  forall S,
  (forall X, Ensembles.In _ S X -> exists l, X = SRec l) ->
  forall G, Alpha S G -> (exists l, G = GRec l) \/ (exists l, G = GRow l). 
(*925:*) Proof. 
(*926:*) (intros). 
(*927:*) (inversion H0; subst). 
(*928:*) - 
(*929:*) specialize (H _ (In_singleton _ _)). 
(*930:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*931:*) congruence. 
(*932:*) - 
(*933:*) specialize (H _ (In_singleton _ _)). 
(*934:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*935:*) congruence. 
(*936:*) - 
(*937:*) (inversion H1). 
(*938:*) specialize (H _ H5). 
(*939:*) specialize (H2 _ H5). 
(*940:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*941:*) congruence. 
(*942:*) - 
(*943:*) eauto. 
(*CANCEL 926*) 
(*945:*) Unset Silent. 
(*948:*) Set Diffs "off". 
(*950:*) Set Printing Width 94. 
(*952:*) Show. 
(*953:*) (inversion H0; subst; eauto). 
(*954:*) - 
(*955:*) specialize (H _ (In_singleton _ _)). 
(*956:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*957:*) congruence. 
(*958:*) - 
(*959:*) specialize (H _ (In_singleton _ _)). 
(*960:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*961:*) congruence. 
(*962:*) - 
(*963:*) (inversion H1). 
(*964:*) specialize (H _ H5). 
(*965:*) specialize (H2 _ H5). 
(*966:*) Set Silent. 
(*968:*) (repeat
  match goal with
  | H:exists _, _ |- _ => destruct H
  | H:_ \/ _ |- _ => inversion H; clear H
  end). 
(*969:*) Unset Silent. 
(*971:*) congruence. 
(*972:*) - 
(*973:*) congruence. 
(*974:*) Qed. 
(*975:*) Set Silent. 
(*976:*) Theorem alpha_is_partial_function : forall S G G', Alpha S G -> Alpha S G' -> G = G'. 
(*977:*) Proof. 
(*978:*) (intros). 
(*979:*) generalize dependent G'. 
(*980:*) (induction H). 
(*981:*) - 
(*982:*) (intros; inversion H0; subst; eauto). 
(*983:*) all: (try (apply singleton_eq in H1; congruence)). 
(*984:*) all: (try specialize (H1 _ (In_singleton _ _))). 
(*985:*) all:
 (repeat
   match goal with
   | H:exists _, _ |- _ => destruct H
   | H:_ \/ _ |- _ => inversion H; clear H
   end). 
(*986:*) all: (try congruence). 
(*987:*) - 
(*988:*) (intros; inversion H0; subst; eauto). 
(*989:*) all: (try (apply singleton_eq in H1; congruence)). 
(*990:*) all: (try specialize (H1 _ (In_singleton _ _ _))). 
(*991:*) all: (try specialize (H1 _ (In_singleton _ _))). 
(*992:*) all:
 (repeat
   match goal with
   | H:exists _, _ |- _ => destruct H
   | H:_ \/ _ |- _ => inversion H; clear H
   end). 
(*993:*) all: (try congruence). 
(*994:*) Unset Silent. 
(*996:*) - 
(*997:*) (intros). 
(*998:*) (apply alpha_rec_inversion in H0; eauto). 
(*FAILED 997*)
(*998:*) (apply alpha_fun_inversion in H0; eauto). 
(*FAILED 997*)
(*998:*) (eapply alpha_fun_inversion in H0; eauto). 
(*1001:*) all:
 (repeat
   match goal with
   | H:exists _, _ |- _ => destruct H
   | H:_ \/ _ |- _ => inversion H; clear H
   end). 
(*1002:*) subst. 
(*1003:*) (inversion H3). 
(*1004:*) subst. 
(*1005:*) f_equal. 
(*CANCEL 1004*) 
(*1007:*) Unset Silent. 
(*1010:*) Set Diffs "off". 
(*1012:*) Set Printing Width 94. 
(*1014:*) Show. 
(*1015:*) (f_equal; eauto). 
(*1016:*) - 
(*1017:*) (intros; eauto). 
(*CANCEL 1016*) 
(*1019:*) Unset Silent. 
(*1022:*) Set Diffs "off". 
(*1024:*) Set Printing Width 94. 
(*1026:*) Show. 
(*1027:*) (intros; inversion H0; subst; eauto). 
(*CANCEL 1026*) 
(*1029:*) Unset Silent. 
(*1032:*) Set Diffs "off". 
(*1034:*) Set Printing Width 94. 
(*1036:*) Show. 
(*1037:*) (intros; inversion H0; subst; eauto). 
(*1038:*) Set Silent. 
(*1040:*) all: (try (apply singleton_eq in H1; congruence)). 
(*1041:*) all: (try specialize (H1 _ (In_singleton _ _))). 
(*1042:*) all:
 (repeat
   match goal with
   | H:exists _, _ |- _ => destruct H
   | H:_ \/ _ |- _ => inversion H; clear H
   end). 
(*1043:*) Unset Silent. 
(*1045:*) all: (try congruence). 
(*1046:*) Show. 
(*CANCEL 1042*) 
(*1048:*) Unset Silent. 
(*1051:*) Set Diffs "off". 
(*CANCEL 1041*) 
(*1054:*) Unset Silent. 
(*1057:*) Set Diffs "off". 
(*CANCEL 1040*) 
(*1060:*) Unset Silent. 
(*1063:*) Set Diffs "off". 
(*CANCEL 1037*) 
(*1066:*) Unset Silent. 
(*1069:*) Set Diffs "off". 
(*CANCEL 1036*) 
(*1072:*) Unset Silent. 
(*1075:*) Set Diffs "off". 
(*1077:*) Set Printing Width 94. 
(*1079:*) Show. 
(*1080:*) (intros; inversion H0; subst; eauto). 
(*1081:*) all: (try (apply singleton_eq in H1; congruence)). 
(*1082:*) all: (try specialize (H1 _ (In_singleton _ _))). 
(*1083:*) all:
 (repeat
   match goal with
   | H:exists _, _ |- _ => destruct H
   | H:_ \/ _ |- _ => inversion H; clear H
   end). 
(*1084:*) all: (try congruence). 
(*CANCEL 1083*) 
(*1086:*) Unset Silent. 
(*1089:*) Set Diffs "off". 
(*1091:*) Set Printing Width 94. 
(*1093:*) Show. 
(*1094:*) all: (try congruence). 
(*1095:*) Show. 
(*CANCEL 306*) 
(*1097:*) Unset Silent. 
(*1099:*) Set Diffs "off". 
(*CANCEL 256*) 
(*1101:*) Unset Silent. 
(*1102:*) Set Diffs "off". 
(*1103:*) Set Printing Width 66. 
(*1104:*) Require Export Setoid. 
(*1105:*) Require Export Relation_Definitions. 
(*1106:*) Set Silent. 
(*1107:*) Module AGT_Bounded_Rows_Details. 
(*1108:*) Definition label := nat. 
(*1109:*) Inductive ST : Type :=
  | SInt : ST
  | SBool : ST
  | SFun : ST -> ST -> ST
  | SRec : list (option ST) -> ST. 
(*1110:*) Inductive Ann : Type :=
  | R : Ann
  | O : Ann. 
(*1111:*) Inductive GT : Type :=
  | GDyn : GT
  | GInt : GT
  | GBool : GT
  | GFun : GT -> GT -> GT
  | GRec : list (option (Ann * GT)) -> GT
  | GRow : list (option (option (Ann * GT))) -> GT. 
(*1112:*) Unset Silent. 
(*1113:*) Module asdf. 
(*CANCEL 1112*) 
(*1115:*) Unset Silent. 
(*1116:*) Set Diffs "off". 
(*1117:*) Set Printing Width 66. 
(*1118:*) Module GTeq. 
(*1119:*) Fixpoint eq (G_1 G_2 : GT) : Prop := True. 
(*CANCEL 1118*) 
(*1121:*) Unset Silent. 
(*1122:*) Set Diffs "off". 
(*1123:*) Set Printing Width 66. 
(*1124:*) Fixpoint eq (G_1 G_2 : GT) : Prop :=
  match G_1, G_2 with
  | GInt, GInt => True
  | GBool, GBool => True
  | GFun G_11 G_12, GFun G_21 G22 => eq G_11 G_21 /\ eq G_12 G22
  | GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2) =>
      eq hd1 hd2 /\ eq (GRec tl1) (GRec tl2)
  | _, _ => False
  end. 
(*FAILED 1123*)
(*1124:*) Fixpoint eq (G_1 G_2 : GT) : Prop :=
  match G_1, G_2 with
  | GInt, GInt => True
  | GBool, GBool => True
  | GFun G_11 G_12, GFun G_21 G22 => eq G_11 G_21 /\ eq G_12 G22
  | GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2) =>
      eq (snd hd1) (snd hd2) /\
      fst hd1 = fst hd2 /\ eq (GRec tl1) (GRec tl2)
  | _, _ => False
  end. 
(*FAILED 1123*)
(*CANCEL 1117*) 
(*1127:*) Unset Silent. 
(*1128:*) Set Diffs "off". 
(*1129:*) Check fold_right. 
(*1130:*) Set Printing Width 66. 
(*1131:*) Fixpoint size_gt (G : GT) : nat :=
  match G with
  | GFun G_1 G_2 => 1 + size_gt G_1 + size_ G_2
  | GRec l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (_, G) => size - gt G
         | _ => 0
         end + acc) 1 l
  | _ => 0
  end. 
(*FAILED 1130*)
(*1131:*) Fixpoint size_gt (G : GT) : nat :=
  match G with
  | GFun G_1 G_2 => 1 + size_gt G_1 + size_gt G_2
  | GRec l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (_, G) => size - gt G
         | _ => 0
         end + acc) 1 l
  | _ => 0
  end. 
(*FAILED 1130*)
(*1131:*) Fixpoint size_gt (G : GT) : nat :=
  match G with
  | GFun G_1 G_2 => 1 + size_gt G_1 + size_gt G_2
  | GRec l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (_, G) => size_gt G
         | _ => 0
         end + acc) 1 l
  | _ => 0
  end. 
(*CANCEL 1130*) 
(*1135:*) Unset Silent. 
(*1136:*) Set Diffs "off". 
(*1137:*) Set Printing Width 66. 
(*1138:*) Fixpoint size_gt (G : GT) : nat :=
  match G with
  | GFun G_1 G_2 => 1 + size_gt G_1 + size_gt G_2
  | GRec l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (_, G) => size_gt G
         | _ => 0
         end + acc) 1 l
  | GRow l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (Some (_, G)) => size_gt G
         | _ => 0
         end + acc) 1 l
  | _ => 0
  end. 
(*1139:*) Module GTeq. 
(*CANCEL 1105*) 
(*1141:*) Unset Silent. 
(*1142:*) Set Diffs "off". 
(*1143:*) Set Printing Width 66. 
(*1144:*) Set Silent. 
(*1145:*) Require Import FunInd. 
(*1146:*) Unset Silent. 
(*1147:*) Require Import Recdef. 
(*1148:*) Set Silent. 
(*1149:*) Module AGT_Bounded_Rows_Details. 
(*1150:*) Definition label := nat. 
(*1151:*) Inductive ST : Type :=
  | SInt : ST
  | SBool : ST
  | SFun : ST -> ST -> ST
  | SRec : list (option ST) -> ST. 
(*1152:*) Inductive Ann : Type :=
  | R : Ann
  | O : Ann. 
(*1153:*) Inductive GT : Type :=
  | GDyn : GT
  | GInt : GT
  | GBool : GT
  | GFun : GT -> GT -> GT
  | GRec : list (option (Ann * GT)) -> GT
  | GRow : list (option (option (Ann * GT))) -> GT. 
(*1154:*) Fixpoint size_gt (G : GT) : nat :=
  match G with
  | GFun G_1 G_2 => 1 + size_gt G_1 + size_gt G_2
  | GRec l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (_, G) => size_gt G
         | _ => 0
         end + acc) 1 l
  | GRow l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (Some (_, G)) => size_gt G
         | _ => 0
         end + acc) 1 l
  | _ => 0
  end. 
(*1155:*) Module GTeq. 
(*1156:*) Unset Silent. 
(*1157:*) Function
 eq (G_1 G_2 : GT) : Prop {measure size_gt G_1} :=
   match G_1, G_2 with
   | GInt, GInt => True
   | GBool, GBool => True
   | GFun G_11 G_12, GFun G_21 G22 => eq G_11 G_21 /\ eq G_12 G22
   | GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2) =>
       eq (snd hd1) (snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1) (GRec tl2)
   | _, _ => False
   end. 
(*FAILED 1156*)
(*1157:*) Function
 eq (G_1 G_2 : GT) {measure size_gt G_1} : Prop :=
   match G_1, G_2 with
   | GInt, GInt => True
   | GBool, GBool => True
   | GFun G_11 G_12, GFun G_21 G22 => eq G_11 G_21 /\ eq G_12 G22
   | GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2) =>
       eq (snd hd1) (snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1) (GRec tl2)
   | _, _ => False
   end. 
(*1159:*) all: (intros; subst; eauto with math). 
(*FAILED 1158*)
(*CANCEL 1147*) 
(*1161:*) Unset Silent. 
(*1163:*) Set Diffs "off". 
(*1164:*) Set Printing Width 66. 
(*1165:*) Create HintDb math discriminated. 
(*CANCEL 1164*) 
(*1167:*) Unset Silent. 
(*1168:*) Set Diffs "off". 
(*1169:*) Set Printing Width 66. 
(*1170:*) Set Silent. 
(*1171:*) Require Import Arith. 
(*1172:*) Require Import Lia. 
(*1173:*) Create HintDb math discriminated. 
(*1174:*) Hint Resolve le_lt_n_Sm: math. 
(*1175:*) Hint Extern 100  => lia: math. 
(*1176:*) Unset Silent. 
(*1177:*) Hint Extern 100  => congruence: math. 
(*1178:*) Set Silent. 
(*1179:*) Module AGT_Bounded_Rows_Details. 
(*1180:*) Definition label := nat. 
(*1181:*) Inductive ST : Type :=
  | SInt : ST
  | SBool : ST
  | SFun : ST -> ST -> ST
  | SRec : list (option ST) -> ST. 
(*1182:*) Inductive Ann : Type :=
  | R : Ann
  | O : Ann. 
(*1183:*) Inductive GT : Type :=
  | GDyn : GT
  | GInt : GT
  | GBool : GT
  | GFun : GT -> GT -> GT
  | GRec : list (option (Ann * GT)) -> GT
  | GRow : list (option (option (Ann * GT))) -> GT. 
(*1184:*) Fixpoint size_gt (G : GT) : nat :=
  match G with
  | GFun G_1 G_2 => 1 + size_gt G_1 + size_gt G_2
  | GRec l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (_, G) => size_gt G
         | _ => 0
         end + acc) 1 l
  | GRow l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (Some (_, G)) => size_gt G
         | _ => 0
         end + acc) 1 l
  | _ => 0
  end. 
(*1185:*) Module GTeq. 
(*1186:*) Function
 eq (G_1 G_2 : GT) {measure size_gt G_1} : Prop :=
   match G_1, G_2 with
   | GInt, GInt => True
   | GBool, GBool => True
   | GFun G_11 G_12, GFun G_21 G22 => eq G_11 G_21 /\ eq G_12 G22
   | GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2) =>
       eq (snd hd1) (snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1) (GRec tl2)
   | _, _ => False
   end. 
(*1187:*) Unset Silent. 
(*1189:*) all: (intros; subst; eauto with math). 
(*CANCEL 1186*) 
(*1191:*) Unset Silent. 
(*1194:*) Set Diffs "off". 
(*1196:*) Set Printing Width 66. 
(*1198:*) Show. 
(*1199:*) all: (intros; subst; simpl; eauto with math). 
(*1200:*) (destruct hd1; simpl; eauto with math). 
(*CANCEL 1199*) 
(*1202:*) Unset Silent. 
(*1205:*) Set Diffs "off". 
(*CANCEL 1184*) 
(*1208:*) Unset Silent. 
(*1210:*) Set Diffs "off". 
(*1211:*) Set Printing Width 66. 
(*1212:*) Theorem size_gt_g0 : forall x, 0 < size_gt x. 
(*1213:*) Proof. 
(*1214:*) (induction x; intros; eauto with math). 
(*CANCEL 1213*) 
(*1216:*) Unset Silent. 
(*1219:*) Set Diffs "off". 
(*1221:*) Set Printing Width 66. 
(*1223:*) Show. 
(*1224:*) (induction x; intros; simpl; eauto with math). 
(*CANCEL 1183*) 
(*1226:*) Unset Silent. 
(*1228:*) Set Diffs "off". 
(*1229:*) Set Printing Width 66. 
(*1230:*) Fixpoint size_gt (G : GT) : nat :=
  match G with
  | GFun G_1 G_2 => 1 + size_gt G_1 + size_gt G_2
  | GRec l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (_, G) => size_gt G
         | _ => 0
         end + acc) 1 l
  | GRow l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (Some (_, G)) => size_gt G
         | _ => 0
         end + acc) 1 l
  | _ => 1
  end. 
(*1231:*) Theorem size_gt_g0 : forall x, 0 < size_gt x. 
(*1232:*) Proof. 
(*1233:*) (induction x; intros; simpl; eauto with math). 
(*1234:*) all: (induction l; eauto with math). 
(*CANCEL 1233*) 
(*1236:*) Unset Silent. 
(*1239:*) Set Diffs "off". 
(*1241:*) Set Printing Width 66. 
(*1243:*) Show. 
(*1244:*) all: (induction l; simpl; eauto with math). 
(*1245:*) Qed. 
(*CANCEL 1230*) 
(*1247:*) Unset Silent. 
(*1248:*) Set Diffs "off". 
(*CANCEL 1229*) 
(*1250:*) Unset Silent. 
(*1251:*) Set Diffs "off". 
(*1252:*) Set Printing Width 66. 
(*1253:*) Fixpoint size_gt (G : GT) : nat :=
  match G with
  | GFun G_1 G_2 => 1 + size_gt G_1 + size_gt G_2
  | GRec l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (_, G) => 1 + size_gt G
         | _ => 0
         end + acc) 1 l
  | GRow l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (Some (_, G)) => 1 + size_gt G
         | _ => 0
         end + acc) 1 l
  | _ => 1
  end. 
(*1254:*) Module GTeq. 
(*1255:*) Function
 eq (G_1 G_2 : GT) {measure size_gt G_1} : Prop :=
   match G_1, G_2 with
   | GInt, GInt => True
   | GBool, GBool => True
   | GFun G_11 G_12, GFun G_21 G22 => eq G_11 G_21 /\ eq G_12 G22
   | GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2) =>
       eq (snd hd1) (snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1) (GRec tl2)
   | _, _ => False
   end. 
(*1256:*) all: (intros; subst; simpl; eauto with math). 
(*1257:*) (destruct hd1; simpl; eauto with math). 
(*CANCEL 1256*) 
(*1259:*) Unset Silent. 
(*1262:*) Set Diffs "off". 
(*1264:*) Set Printing Width 66. 
(*1266:*) Show. 
(*1267:*) all: (destruct hd1; simpl; eauto with math). 
(*CANCEL 1252*) 
(*1269:*) Unset Silent. 
(*1271:*) Set Diffs "off". 
(*1272:*) Set Printing Width 66. 
(*1273:*) Fixpoint size_gt (G : GT) : nat :=
  match G with
  | GFun G_1 G_2 => 1 + size_gt G_1 + size_gt G_2
  | GRec l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (_, G) => 1 + size_gt G
         | _ => 0
         end + acc) 1 l
  | GRow l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (Some (_, G)) => 1 + size_gt G
         | _ => 0
         end + acc) 1 l
  | _ => 0
  end. 
(*1274:*) Module GTeq. 
(*1275:*) Function
 eq (G_1 G_2 : GT) {measure size_gt G_1} : Prop :=
   match G_1, G_2 with
   | GInt, GInt => True
   | GBool, GBool => True
   | GFun G_11 G_12, GFun G_21 G22 => eq G_11 G_21 /\ eq G_12 G22
   | GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2) =>
       eq (snd hd1) (snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1) (GRec tl2)
   | _, _ => False
   end. 
(*1276:*) all: (intros; subst; simpl; eauto with math). 
(*1277:*) all: (destruct hd1; simpl; eauto with math). 
(*1278:*) Defined. 
(*CANCEL 1274*) 
(*1280:*) Unset Silent. 
(*1281:*) Set Diffs "off". 
(*1282:*) Set Printing Width 66. 
(*1283:*) Function
 eq (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq (G_11, G_21) /\ eq (G_12, G22)
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq (GRec tl1, GRec tl2)
   | _, _ => False
   end. 
(*FAILED 1282*)
(*1283:*) Function
 eq (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq (G_11, G_21) /\ eq (G_12, G22)
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq (GRec tl1, GRec tl2)
   | _ => False
   end. 
(*1285:*) all: (intros; subst; simpl; eauto with math). 
(*1286:*) all: (destruct hd1; simpl; eauto with math). 
(*FAILED 1285*)
(*1286:*) all: (try destruct hd1; try destruct hd2; simpl; eauto with math). 
(*CANCEL 1272*) 
(*1289:*) Unset Silent. 
(*1291:*) Set Diffs "off". 
(*1292:*) Set Printing Width 66. 
(*1293:*) Fixpoint size_gt (G : GT) : nat :=
  match G with
  | GFun G_1 G_2 => 1 + size_gt G_1 + size_gt G_2
  | GRec l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (_, G) => 1 + size_gt G
         | _ => 1
         end + acc) 1 l
  | GRow l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (Some (_, G)) => 1 + size_gt G
         | _ => 1
         end + acc) 1 l
  | _ => 0
  end. 
(*1294:*) Module GTeq. 
(*1295:*) Function
 eq (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq (G_11, G_21) /\ eq (G_12, G22)
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq (GRec tl1, GRec tl2)
   | _ => False
   end. 
(*1296:*) all: (intros; subst; simpl; eauto with math). 
(*1297:*) all: (try destruct hd1; try destruct hd2; simpl; eauto with math). 
(*CANCEL 1294*) 
(*1299:*) Unset Silent. 
(*1301:*) Set Diffs "off". 
(*1302:*) Set Printing Width 66. 
(*1303:*) Function
 eq (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq (G_11, G_21) /\ eq (G_12, G22)
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec []) => eq (GRec tl1, GRec [])
   | _ => False
   end. 
(*1304:*) all: (intros; subst; simpl; eauto with math). 
(*1305:*) all: (try destruct hd1; try destruct hd2; simpl; eauto with math). 
(*CANCEL 1302*) 
(*1307:*) Unset Silent. 
(*1309:*) Set Diffs "off". 
(*1310:*) Set Printing Width 66. 
(*1311:*) Function
 eq (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq (G_11, G_21) /\ eq (G_12, G22)
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec []) => eq (GRec tl1, GRec [])
   | (GRec [], GRec (None :: tl1)) => eq (GRec [], GRec tl1)
   | _ => False
   end. 
(*CANCEL 1310*) 
(*1313:*) Unset Silent. 
(*1315:*) Set Diffs "off". 
(*CANCEL 1293*) 
(*1317:*) Unset Silent. 
(*1318:*) Set Diffs "off". 
(*CANCEL 1292*) 
(*1320:*) Unset Silent. 
(*1321:*) Set Diffs "off". 
(*1322:*) Set Printing Width 66. 
(*1323:*) Set Silent. 
(*1324:*) Definition FromRow : option (option (Ann * GT)) := None. 
(*1325:*) Definition AbsentLabel : option (option (Ann * GT)) := Some None. 
(*1326:*) Unset Silent. 
(*1327:*) Fixpoint size_gt (G : GT) : nat :=
  match G with
  | GFun G_1 G_2 => 1 + size_gt G_1 + size_gt G_2
  | GRec l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (_, G) => 1 + size_gt G
         | _ => 1
         end + acc) 1 l
  | GRow l =>
      fold_right
        (fun x acc =>
         match x with
         | Some (Some (_, G)) => 1 + size_gt G
         | _ => 1
         end + acc) 1 l
  | _ => 0
  end. 
(*1328:*) Module GTeq. 
(*1329:*) Function
 eq (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq (G_11, G_21) /\ eq (G_12, G22)
   | (GRec [], GRec []) => True
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec []) => eq (GRec tl1, GRec [])
   | (GRec [], GRec (None :: tl1)) => eq (GRec [], GRec tl1)
   | (GRow (Some (Some hd1) :: tl1), GRow
     (Some (Some hd2) :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRow tl1, GRow tl2)
   | _ => False
   end. 
(*CANCEL 1328*) 
(*1331:*) Unset Silent. 
(*1333:*) Set Diffs "off". 
(*1334:*) Set Printing Width 66. 
(*1335:*) Function
 eq (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq (G_11, G_21) /\ eq (G_12, G22)
   | (GRec [], GRec []) => True
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec []) => eq (GRec tl1, GRec [])
   | (GRec [], GRec (None :: tl1)) => eq (GRec [], GRec tl1)
   | (GRow [], GRow []) => True
   | (GRow (Some (Some hd1) :: tl1), GRow
     (Some (Some hd2) :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRow tl1, GRow tl2)
   | eq (GRow (None :: tl1), GRow (None :: tl2)) =>
       eq (GRow tl1, GRow tl2)
   | eq (GRow (Some None :: tl1), GRow (Some None :: tl2)) =>
       eq (GRow tl1, GRow tl2)
   | _ => False
   end. 
(*FAILED 1334*)
(*1335:*) Function
 eq (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq (G_11, G_21) /\ eq (G_12, G22)
   | (GRec [], GRec []) => True
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec []) => eq (GRec tl1, GRec [])
   | (GRec [], GRec (None :: tl1)) => eq (GRec [], GRec tl1)
   | (GRow [], GRow []) => True
   | (GRow (Some (Some hd1) :: tl1), GRow
     (Some (Some hd2) :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRow tl1, GRow tl2)
   | eq (GRow (None :: tl1), GRow (None :: tl2)) =>
       eq (GRow tl1, GRow tl2)
   | eq (GRow (Some None :: tl1), GRow (Some None :: tl2)) =>
       eq (GRow tl1, GRow tl2)
   | _ => False
   end. 
(*FAILED 1334*)
(*1335:*) Function
 eq (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq (G_11, G_21) /\ eq (G_12, G22)
   | (GRec [], GRec []) => True
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec []) => eq (GRec tl1, GRec [])
   | (GRec [], GRec (None :: tl1)) => eq (GRec [], GRec tl1)
   | (GRow [], GRow []) => True
   | (GRow (Some (Some hd1) :: tl1), GRow
     (Some (Some hd2) :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRow tl1, GRow tl2)
   | (GRow (None :: tl1), GRow (None :: tl2)) =>
       eq (GRow tl1, GRow tl2)
   | eq (GRow (Some None :: tl1), GRow (Some None :: tl2)) =>
       eq (GRow tl1, GRow tl2)
   | _ => False
   end. 
(*FAILED 1334*)
(*1335:*) Function
 eq (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq (G_11, G_21) /\ eq (G_12, G22)
   | (GRec [], GRec []) => True
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec []) => eq (GRec tl1, GRec [])
   | (GRec [], GRec (None :: tl1)) => eq (GRec [], GRec tl1)
   | (GRow [], GRow []) => True
   | (GRow (Some (Some hd1) :: tl1), GRow
     (Some (Some hd2) :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRow tl1, GRow tl2)
   | (GRow (None :: tl1), GRow (None :: tl2)) =>
       eq (GRow tl1, GRow tl2)
   | (GRow (Some None :: tl1), GRow (Some None :: tl2)) =>
       eq (GRow tl1, GRow tl2)
   | _ => False
   end. 
(*CANCEL 1334*) 
(*1340:*) Unset Silent. 
(*1342:*) Set Diffs "off". 
(*1343:*) Set Printing Width 66. 
(*1344:*) Function
 eq (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq (G_11, G_21) /\ eq (G_12, G22)
   | (GRec [], GRec []) => True
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec []) => eq (GRec tl1, GRec [])
   | (GRec [], GRec (None :: tl1)) => eq (GRec [], GRec tl1)
   | (GRow [], GRow []) => True
   | (GRow (Some (Some hd1) :: tl1), GRow
     (Some (Some hd2) :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRow tl1, GRow tl2)
   | (GRow (None :: tl1), GRow (None :: tl2)) =>
       eq (GRow tl1, GRow tl2)
   | (GRow (Some None :: tl1), GRow (Some None :: tl2)) =>
       eq (GRow tl1, GRow tl2)
   | (GRow (None :: tl1), GRow []) => eq (GRow tl1, GRow [])
   | (GRow [], GRow (None :: tl1)) => eq (GRow [], GRow tl1)
   | _ => False
   end. 
(*1345:*) all: (intros; subst; simpl; eauto with math). 
(*1346:*) all: (try destruct hd1; try destruct hd2; simpl; eauto with math). 
(*1347:*) Defined. 
(*1348:*) Theorem eq_refl : forall A, reflexive _ (eq (A:=A)). 
(*FAILED 1347*)
(*CANCEL 1343*) 
(*1350:*) Unset Silent. 
(*1351:*) Set Diffs "off". 
(*1352:*) Set Printing Width 66. 
(*1353:*) Function
 eq (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq (G_11, G_21) /\ eq (G_12, G22)
   | (GRec [], GRec []) => True
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec []) => eq (GRec tl1, GRec [])
   | (GRec [], GRec (None :: tl1)) => eq (GRec [], GRec tl1)
   | (GRow [], GRow []) => True
   | (GRow (Some (Some hd1) :: tl1), GRow
     (Some (Some hd2) :: tl2)) =>
       eq (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq (GRow tl1, GRow tl2)
   | (GRow (None :: tl1), GRow (None :: tl2)) =>
       eq (GRow tl1, GRow tl2)
   | (GRow (Some None :: tl1), GRow (Some None :: tl2)) =>
       eq (GRow tl1, GRow tl2)
   | (GRow (None :: tl1), GRow []) => eq (GRow tl1, GRow [])
   | (GRow [], GRow (None :: tl1)) => eq (GRow [], GRow tl1)
   | _ => False
   end. 
(*1354:*) all: (intros; subst; simpl; eauto with math). 
(*1355:*) Set Silent. 
(*1357:*) all: (try destruct hd1; try destruct hd2; simpl; eauto with math). 
(*1358:*) Unset Silent. 
(*1360:*) Defined. 
(*CANCEL 1352*) 
(*1362:*) Unset Silent. 
(*1363:*) Set Diffs "off". 
(*1364:*) Set Printing Width 66. 
(*1365:*) Function
 eq_fn (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq_fn (G_11, G_21) /\ eq_fn (G_12, G22)
   | (GRec [], GRec []) => True
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq_fn (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq_fn (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq_fn (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec []) => eq_fn (GRec tl1, GRec [])
   | (GRec [], GRec (None :: tl1)) => eq_fn (GRec [], GRec tl1)
   | (GRow [], GRow []) => True
   | (GRow (Some (Some hd1) :: tl1), GRow
     (Some (Some hd2) :: tl2)) =>
       eq_fn (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq_fn (GRow tl1, GRow tl2)
   | (GRow (None :: tl1), GRow (None :: tl2)) =>
       eq_fn (GRow tl1, GRow tl2)
   | (GRow (Some None :: tl1), GRow (Some None :: tl2)) =>
       eq_fn (GRow tl1, GRow tl2)
   | (GRow (None :: tl1), GRow []) => eq_fn (GRow tl1, GRow [])
   | (GRow [], GRow (None :: tl1)) => eq_fn (GRow [], GRow tl1)
   | _ => False
   end. 
(*1366:*) all: (intros; subst; simpl; eauto with math). 
(*1367:*) all: (try destruct hd1; try destruct hd2; simpl; eauto with math). 
(*1368:*) Defined. 
(*1369:*) Definition eq (G_1 G_2 : GT) := eq_fn (G_1, G_2). 
(*1370:*) Theorem eq_refl : forall A, reflexive _ (eq (A:=A)). 
(*FAILED 1369*)
(*1370:*) Check reflexive. 
(*1372:*) Theorem eq_refl : forall A, reflexive _ (eq (A:=A)). 
(*FAILED 1371*)
(*1372:*) Check reflexive _. 
(*1374:*) Check reflexive GT. 
(*1375:*) Theorem eq_refl : forall A, reflexive GT (eq (A:=A)). 
(*FAILED 1374*)
(*1375:*) Theorem eq_refl : forall A, reflexive GT (eq A A). 
(*FAILED 1374*)
(*1375:*) Check relation GT. 
(*1378:*) Check relation GT. 
(*1379:*) Check relation. 
(*1380:*) Print relation. 
(*1381:*) Print eq. 
(*1382:*) Check eq. 
(*1383:*) Theorem eq_refl : forall A, reflexive GT (eq A A). 
(*FAILED 1382*)
(*1383:*) Theorem eq_refl : forall A, reflexive GT eq. 
(*FAILED 1382*)
(*1383:*) Theorem eq_refl : reflexive GT eq. 
(*1386:*) Proof. 
(*1387:*) (unfold reflexive). 
(*1388:*) (induction x). 
(*CANCEL 1387*) 
(*1390:*) Unset Silent. 
(*1393:*) Set Diffs "off". 
(*1395:*) Set Printing Width 66. 
(*1397:*) Show. 
(*1398:*) (induction x; eauto). 
(*CANCEL 1397*) 
(*1400:*) Unset Silent. 
(*1403:*) Set Diffs "off". 
(*1405:*) Set Printing Width 66. 
(*1407:*) Show. 
(*1408:*) (induction x; simpl; eauto). 
(*CANCEL 1407*) 
(*1410:*) Unset Silent. 
(*1413:*) Set Diffs "off". 
(*1415:*) Set Printing Width 66. 
(*1417:*) Show. 
(*1418:*) (induction x; unfold eq; simpl; eauto). 
(*CANCEL 1417*) 
(*1420:*) Unset Silent. 
(*1423:*) Set Diffs "off". 
(*1425:*) Set Printing Width 66. 
(*1427:*) Show. 
(*1428:*) (induction x; unfold eq; rewrite eq_fn_equation; simpl; eauto). 
(*CANCEL 1364*) 
(*1430:*) Unset Silent. 
(*1432:*) Set Diffs "off". 
(*1433:*) Set Printing Width 66. 
(*1434:*) Function
 eq_fn (G : GT * GT) {measure
 fun x => size_gt (fst x) + size_gt (snd x) G} : Prop :=
   match G with
   | (GDyn, GDyn) => True
   | (GInt, GInt) => True
   | (GBool, GBool) => True
   | (GFun G_11 G_12, GFun G_21 G22) =>
       eq_fn (G_11, G_21) /\ eq_fn (G_12, G22)
   | (GRec [], GRec []) => True
   | (GRec (Some hd1 :: tl1), GRec (Some hd2 :: tl2)) =>
       eq_fn (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq_fn (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec (None :: tl2)) =>
       eq_fn (GRec tl1, GRec tl2)
   | (GRec (None :: tl1), GRec []) => eq_fn (GRec tl1, GRec [])
   | (GRec [], GRec (None :: tl1)) => eq_fn (GRec [], GRec tl1)
   | (GRow [], GRow []) => True
   | (GRow (Some (Some hd1) :: tl1), GRow
     (Some (Some hd2) :: tl2)) =>
       eq_fn (snd hd1, snd hd2) /\
       fst hd1 = fst hd2 /\ eq_fn (GRow tl1, GRow tl2)
   | (GRow (None :: tl1), GRow (None :: tl2)) =>
       eq_fn (GRow tl1, GRow tl2)
   | (GRow (Some None :: tl1), GRow (Some None :: tl2)) =>
       eq_fn (GRow tl1, GRow tl2)
   | (GRow (None :: tl1), GRow []) => eq_fn (GRow tl1, GRow [])
   | (GRow [], GRow (None :: tl1)) => eq_fn (GRow [], GRow tl1)
   | _ => False
   end. 
(*1435:*) all: (intros; subst; simpl; eauto with math). 
(*1436:*) Set Silent. 
(*1438:*) all: (try destruct hd1; try destruct hd2; simpl; eauto with math). 
(*1439:*) Unset Silent. 
(*1441:*) Defined. 
(*1442:*) Set Silent. 
(*1443:*) Definition eq (G_1 G_2 : GT) := eq_fn (G_1, G_2). 
(*1444:*) Unset Silent. 
(*1445:*) Theorem eq_refl : reflexive GT eq. 
(*1446:*) Proof. 
(*1447:*) (unfold reflexive). 
(*1448:*) (induction x; unfold eq; rewrite eq_fn_equation; simpl; eauto). 
(*1449:*) all: (destruct l; eauto). 
(*1450:*) all: (destruct o; eauto). 
(*CANCEL 1447*) 
(*1452:*) Unset Silent. 
(*1455:*) Set Diffs "off". 
(*CANCEL 1444*) 
(*1458:*) Unset Silent. 
(*1460:*) Set Diffs "off". 
(*1461:*) Set Printing Width 66. 
(*1462:*) Notation "G_1 === G_2" := (eq G_1 G_2). 
(*FAILED 1461*)
(*1462:*) Notation "G_1 === G_2" := (eq G_1 G_2) (at level 100). 

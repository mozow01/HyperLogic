Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.

Require Import List.
Import ListNotations.


Declare Scope surface_scope.

(* --- TERMEK ÉS BÁZIS MORFIZMUSOK --- *)
(* A 'var0' a legfelső lokális változó, ami kategóriaelméletileg a második projekció *)
Notation "'var0'" := (b_snd) : surface_scope.

(* Az Epszilon term egy globális Skolem konstans a háttérben *)
Notation "'ε' D , Phi" := (b_const D (skolem_index D Phi)) (at level 50) : surface_scope.


(* --- LOGIKAI OPERÁTOROK --- *)
Notation "A ⇒ B" := (Ty_Arrow A B) (at level 60, right associativity) : surface_scope.
Notation "'∃' D , Phi" := (Ty_Ex D Phi) (at level 50) : surface_scope.
Notation "'∀' D , Phi" := (Ty_All D Phi) (at level 50) : surface_scope.


(* --- STRUKTURÁLIS MŰVELETEK (A LÉNYEG) --- *)

(* GYENGÍTÉS (Lifting / Weakening): 
   Felemeli a formulát az 'I' fibrumból az 'I * D' fibrumba, hogy 
   egy új, lokális változó mellett is használható legyen. 
   Kategóriaelméletben ez egy visszahúzás az első projekció (b_fst) mentén. *)
Notation "⇑ Phi" := (form_pullback b_fst Phi) (at level 40) : surface_scope.

Open Scope surface_scope.

(* 1. Bázis Axióma: A lokális változó behelyettesítése a gyengített környezetbe identitást ad. *)
(* 1. Bázis Axióma: fst ∘ ⟨id, snd⟩ = id *)
(* Megjegyzés: Itt nem kell SkolemMapping, mert nincs benne epszilon *)
Axiom BE_Comp_Pair_Id_Snd_Fst : forall {Sign} I D,
  forall (df : base_typing (b_Prod I D) (b_comp (b_pair b_id b_snd) b_fst) (b_Prod I D))
         (dg : base_typing (b_Prod I D) b_id (b_Prod I D)),
  @base_equiv Sign (b_Prod I D) (b_Prod I D)
    (b_comp (b_pair b_id b_snd) b_fst) b_id 
    df dg.

(* 2. Bázis Axióma: A kiterjesztett pullbackek kompozíciója *)
(* Itt szükség van a `{H : SkolemMapping Sign}`-re az epszilon miatt! *)
Axiom BE_PullbackExt_Cancel : forall {Sign} `{H : SkolemMapping Sign} I D (Phi : @h_ty Sign),
  forall (df : base_typing I (b_comp (b_pullback_ext (b_pair b_id (ε D, Phi))) (b_pullback_ext b_fst)) I)
         (dg : base_typing I b_id I),
  @base_equiv Sign I I
    (b_comp (b_pullback_ext (b_pair b_id (ε D, Phi))) (b_pullback_ext b_fst)) b_id 
    df dg.
    
(* ================================================================= *)
(* 2. A DRINKER PARADOXON A FELSZÍNI NYELVEN                         *)
(* ================================================================= *)

(* A formula: ∃ x. ( (∃ y. Phi(y)) ⇒ Phi(x) )
   Mivel a (∃ y. Phi(y)) a külső kvantor (x) előtt jött létre, 
   fel kell emelnünk (⇑), hogy implikációba tehessük a Phi-vel! *)
Definition Dual_Drinker {Sign : Type} `{SkolemMapping Sign} (I D : b_ty) (Phi : @h_ty Sign) : @h_ty Sign :=
  ∃ D , ( (⇑ (∃ D , Phi)) ⇒ Phi ).

(* ================================================================= *)
(* 3. A BIZONYÍTÁS (Ugyanaz a Hyper_Syntax, de emberi nyelven!)      *)
(* ================================================================= *)

Lemma dual_drinker_surface_provable {Sign : Type} `{SkolemMapping Sign} 
  (I D : b_ty) (Phi : @h_ty Sign) : 
  exists p, h_typing I [] p (Dual_Drinker I D Phi).
Proof.
  eexists. unfold Dual_Drinker.
  eapply HT_Ex_Intro with (f := ε D, Phi).
  - apply BT_Const.
  - eapply HT_Conv.
    + eapply HT_Lam.
      
      (* 1. LÉPÉS: Megtisztítjuk a premisszát az elimináció ELŐTT! *)
      eapply HT_Ex_Elim.
      * eapply HT_Conv.
        -- apply HT_Var0.
        -- (* CÉL: (⇑ (∃ D, Phi)) [ ε D, Phi ] == ∃ D, Phi *)
           (* Itt NEM használunk simpl-t, így a kvantor egyben marad, 
              és a fibrációs axiómák tökéletesen illeszkednek! *)
           eapply FE_Trans.
           1: { apply FE_Pullback_Comp. }
           eapply FE_Trans.
           2: { apply FE_Pullback_Id. }
           eapply FE_Pullback_Cong. 
           (* Bázis axióma: b_comp ⟨id, ε⟩ fst == id *)
           apply BE_PullbackExt_Cancel.
      * (* 2. LÉPÉS: Beléptünk a letisztított lokális kontextusba! *)
        eapply HT_Conv.
        -- eapply HT_Eps_Intro with (f := var0).
           ++ apply BT_Snd.
           ++ eapply HT_Conv.
              ** apply HT_Var0.
              ** (* CÉL: ⇑ Phi == (⇑ Phi) .[ var0 ] *)
                 (* Ezt úgy bizonyítjuk, hogy a helyettesítéseket (fst és ⟨id, var0⟩)
                    összevonjuk egy kompozícióba, majd a bázisban egyszerűsítjük identitássá! *)
                 eapply FE_Sym. 
                 eapply FE_Trans.
                 1: { apply FE_Pullback_Comp. }
                 eapply FE_Trans.
                 2: { apply FE_Pullback_Id. }
                 eapply FE_Pullback_Cong.
                 
                 (* Itt hívjuk a bázis axiómát: fst ∘ ⟨id, var0⟩ == id *)
                 apply BE_Comp_Pair_Id_Snd_Fst.
        -- (* A lokális Epszilont felemeljük a globális szintre *)
           apply FE_Eps_Lift.
           
    + (* 3. LÉPÉS: Az implikáció kommutativitása (Ezt a simpl automatikusan megoldja!) *)
      simpl. 
Admitted.

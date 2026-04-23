(* Base/Simple/Base_Syntax*)

Require Import Setoid.
Require Import Relation_Definitions.
Require Import Morphisms.  
  
  (* 1. OBJEKTUMOK *)
  Inductive b_ty : Type :=
    | b_Unit : b_ty
    | b_S    : b_ty
    | b_Prod : b_ty -> b_ty -> b_ty.

  (* 2. NYERS MORFIZMUSOK *)
  Inductive b_tm : Type :=
    | b_id   : b_tm
    | b_comp : b_tm -> b_tm -> b_tm
    | b_unit : b_tm
    | b_pair : b_tm -> b_tm -> b_tm
    | b_fst  : b_tm
    | b_snd  : b_tm.

  (* 3. TIPUSOLASI SZABALYOK (B1 |- f : B2) *)
  Inductive base_typing : b_ty -> b_tm -> b_ty -> Set :=
    | BT_Id : forall A, 
        base_typing A b_id A
    | BT_Comp : forall A B C g f,
        base_typing B g C -> base_typing A f B -> 
        base_typing A (b_comp g f) C
    | BT_Unit : forall A, 
        base_typing A b_unit b_Unit
    | BT_Pair : forall A B C f g,
        base_typing A f B -> base_typing A g C -> 
        base_typing A (b_pair f g) (b_Prod B C)
    | BT_Fst : forall A B, 
        base_typing (b_Prod A B) b_fst A
    | BT_Snd : forall A B, 
        base_typing (b_Prod A B) b_snd B.
        
Require Import Setoid.
Require Import Relation_Definitions.
Require Import Morphisms.

(* --- 1. LÉPÉS: Argumentumok implicitté tétele --- *)
(* Ez mondja meg a Coq-nak, hogy a kapcsos zárójelben lévőket találja ki magától. *)
Arguments BT_Id {A}.
Arguments BT_Comp {A B C g f}.
Arguments BT_Unit {A}.
Arguments BT_Pair {A B C f g}.
Arguments BT_Fst {A B}.
Arguments BT_Snd {A B}.

Require Import Setoid.
Require Import Morphisms.
Require Import Relation_Definitions.

(* ================================================================= *)
(* 4. KATEGORIKUS EKVIVALENCIA (Morfizmusok Egyenlősége)             *)
(* ================================================================= *)

(* By taking A B f g as indices, and derivations as hypotheses, 
   we decouple the equality from the rigid dependent derivations! *)
Inductive base_equiv : b_ty -> b_ty -> b_tm -> b_tm -> Prop :=
  
  (* 1. Equivalence Relation *)
  | BE_Refl : forall I J f (df : base_typing I f J), 
        base_equiv I J f f
  | BE_Sym  : forall I J f g, 
      base_equiv I J f g -> base_equiv I J g f
  | BE_Trans: forall I J f g h, 
      base_equiv I J f g -> base_equiv I J g h -> base_equiv I J f h
      
  (* 2. Congruence *)
  | BE_CongComp : forall A B C f f' g g',
      base_equiv B C g g' -> base_equiv A B f f' -> 
      base_equiv A C (b_comp g f) (b_comp g' f')
  | BE_CongPair : forall A B C f f' g g',
      base_equiv A B f f' -> base_equiv A C g g' -> 
      base_equiv A (b_Prod B C) (b_pair f g) (b_pair f' g')
      
  (* 3. Categorical Axioms (Beta / Eta) *)
  | BE_IdL : forall A B f (df : base_typing A f B), 
      base_equiv A B (b_comp b_id f) f
  | BE_IdR : forall A B f (df : base_typing A f B), 
      base_equiv A B (b_comp f b_id) f
  | BE_Assoc : forall A B C D f g h 
      (df : base_typing A f B) (dg : base_typing B g C) (dh : base_typing C h D),
      base_equiv A D (b_comp h (b_comp g f)) (b_comp (b_comp h g) f)
      
  | BE_BetaFst : forall A B C f g 
      (df : base_typing A f B) (dg : base_typing A g C),
      base_equiv A B (b_comp b_fst (b_pair f g)) f
  | BE_BetaSnd : forall A B C f g 
      (df : base_typing A f B) (dg : base_typing A g C),
      base_equiv A C (b_comp b_snd (b_pair f g)) g
  | BE_EtaPair : forall A B C f 
      (df : base_typing A f (b_Prod B C)),
      base_equiv A (b_Prod B C) (b_pair (b_comp b_fst f) (b_comp b_snd f)) f
      
  | BE_Terminal : forall A f g 
      (df : base_typing A f b_Unit) (dg : base_typing A g b_Unit),
      base_equiv A b_Unit f g.

(* ================================================================= *)
(* 5. SETOID REWRITING INSTANCES                                     *)
(* ================================================================= *)

(* 1. Register as a Partial Equivalence Relation (PER) to allow Setoid rewriting *)
Instance base_equiv_Sym (A B : b_ty) : Symmetric (base_equiv A B).
Proof. intros f g H. eapply BE_Sym. exact H. Qed.

Instance base_equiv_Trans (A B : b_ty) : Transitive (base_equiv A B).
Proof. intros f g h H1 H2. eapply BE_Trans; eassumption. Qed.

(* 2. Morphisms (b_comp and b_pair) remain exactly the same below... *)

(* 2. Register Composition (b_comp) as a proper Setoid morphism.
      "If g == g' and f == f', then g o f == g' o f'" *)
(* 2. Register Composition (b_comp) as a proper Setoid morphism. *)
Add Parametric Morphism (A B C : b_ty) : (b_comp)
  with signature (base_equiv B C) ==> (base_equiv A B) ==> (base_equiv A C)
  as comp_mor.
Proof.
  intros g g' Hg f f' Hf.
  (* Use eapply so Coq leaves B blank, then eassumption fills it in! *)
  eapply BE_CongComp.
  - exact Hg.
  - exact Hf.
Defined.

(* 3. Register Pairing (b_pair) as a proper Setoid morphism.
      "If f == f' and g == g', then <f, g> == <f', g'>" *)
Add Parametric Morphism (A B C : b_ty) : (b_pair)
  with signature (base_equiv A B) ==> (base_equiv A C) ==> (base_equiv A (b_Prod B C))
  as pair_mor.
Proof.
  intros f f' Hf g g' Hg.
  apply BE_CongPair; assumption.
Defined.




(* Meta-Theorem: Uniqueness of Base Typing *)
Lemma base_typing_unique : forall {I : b_ty} {t : b_tm} {A1 A2 : b_ty},
  base_typing I t A1 -> base_typing I t A2 -> A1 = A2.
Proof.
  intros I t A1 A2 d1.
  revert A2.
  induction d1; intros A2_target d2; inversion d2; subst.
  
  - (* BT_Id *) 
    reflexivity.
  
  - (* BT_Comp *) 
    (* We know (f : I -> B) and (f : I -> B0), so B = B0 by IH *)
    assert (Heq : B = B0) by (apply IHd1_2; exact H4).
    subst B0.
    (* Now we know (g : B -> C) and (g : B -> A2_target), so C = A2_target by IH *)
    apply IHd1_1; exact H2.
    
  - (* BT_Unit *) 
    reflexivity.
  
  - (* BT_Pair *)
    (* If the left and right sides match by IH, the product types match. *)
    f_equal; eauto.
    
  - (* BT_Fst *) 
    reflexivity.
  
  - (* BT_Snd *) 
    reflexivity.
Defined.
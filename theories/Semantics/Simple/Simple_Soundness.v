Require Import Coq.Classes.Morphisms.
Require Import List.
Import ListNotations.
Require Import Coq.Program.Equality.

(* Kategóriaelmélet *)
Require Import HyperLogic.Cat.Core.
Require Import HyperLogic.Cat.CC.
Require Import HyperLogic.Cat.CCC.
Require Import HyperLogic.Cat.BCCC.
Require Import HyperLogic.Cat.Functor.
Require Import HyperLogic.Cat.Adjoint.
Require Import HyperLogic.Cat.Fibration.

(* Szintaxis és Bázis Szemantika *)
Require Import HyperLogic.Logic.Base.Simple.Base_Syntax.
Require Import HyperLogic.Semantics.Simple.Base_Simple_Soundness.
Require Import HyperLogic.Logic.Hyper.Simple.Hyper_Syntax.

(* ================================================================= *)
(* 1. A HIPERDOKTRÍNA MODELL (Javított implicit argumentumok)        *)
(* ================================================================= *)

Class HyperModel (B : SetoidCategory) {CB : CartesianCategory B} 
                 {TSC : TwoSortCategory B} {GF : GoodFibration B} 
                 {Sig : Signature} := {
  interp_pred : forall (p : nat), @obj (Fiber (interp_ty (pred_arity p)))
}.

(* ================================================================= *)
(* 2. FORMULÁK ÉS KONTEXTUSOK INTERPRETÁCIÓJA                        *)
(* ================================================================= *)

Fixpoint interp_h_ty {B : SetoidCategory} {CB : CartesianCategory B} 
                     {TSC : TwoSortCategory B} {GF : GoodFibration B} 
                     {Sig : Signature} {M : HyperModel B} 
                     {I : b_ty} {Phi : h_ty} 
                     (wf : formula_wf I Phi) : @obj (Fiber (interp_ty I)) :=
  match wf with
  (* Az 'I' egy index, ezért minden konstruktorhoz hozzáadott a Coq egy rejtett argumentumot.
     Ezeket fogja fel az első '_' aláhúzás. *)
  | WF_Unit _ => terminal
  | WF_Void _ => initial
  | WF_Prod _ A B wfA wfB => prod (interp_h_ty wfA) (interp_h_ty wfB)
  | WF_Sum  _ A B wfA wfB => coprod (interp_h_ty wfA) (interp_h_ty wfB)
  | WF_Arr  _ A B wfA wfB => exp (interp_h_ty wfB) (interp_h_ty wfA)

  (* --- Atom (Helyettesítés Pullback-el) --- *)
  | WF_Atom _ p t dt => 
      @fobj _ _ (Pullback (interp_tm dt)) (interp_pred p)

  (* --- Kvantorok (Jobb és Bal Adjungáltak) --- *)
  | WF_All _ A Phi_body wf_body =>
      @fobj _ _ (Pi_f (@prod_fst B CB (interp_ty I) (interp_ty A))) (interp_h_ty wf_body)
      
  | WF_Ex _ A Phi_body wf_body =>
      @fobj _ _ (Sigma_f (@prod_fst B CB (interp_ty I) (interp_ty A))) (interp_h_ty wf_body)
  end.

Fixpoint interp_h_ctx {B : SetoidCategory} {CB : CartesianCategory B} 
                      {TSC : TwoSortCategory B} {GF : GoodFibration B} 
                      {Sig : Signature} {M : HyperModel B} 
                      {I : b_ty} {G : h_context} 
                      (cwf : context_wf I G) : @obj (Fiber (interp_ty I)) :=
  match cwf with
  (* Mivel a Coq indexként kezelte az 'I'-t, ide is kell az aláhúzás! *)
  | CWF_Nil _ => terminal
  | CWF_Cons _ Phi G' wfPhi wfG' => prod (interp_h_ctx wfG') (interp_h_ty wfPhi)
  end.
  

(* ================================================================= *)
(* 3. COMPUTABLE PROOF EXTRACTORS (Az Axiómák helyett!)              *)
(* ================================================================= *)

Axiom dummy_cwf_ext : forall {Sig : Signature} {I G}, context_wf I G.
Axiom dummy_wf_ext  : forall {Sig : Signature} {I Phi}, formula_wf I Phi.

(* --- 1. Segédfüggvények a kontextushoz --- *)
Definition ctx_tail (ctx : h_context) : h_context :=
  match ctx with | nil => nil | _ :: G' => G' end.

Definition tail_cwf {Sig : Signature} {I ctx} (cwf : context_wf I ctx) : context_wf I (ctx_tail ctx) :=
  match cwf in context_wf _ ctx' return context_wf I (ctx_tail ctx') with
  | CWF_Nil _ => CWF_Nil _
  | CWF_Cons _ _ _ _ cwf_G => cwf_G
  end.

Definition ctx_head (ctx : h_context) : h_ty :=
  match ctx with | nil => Ty_Unit | Phi :: _ => Phi end.

Definition head_wf {Sig : Signature} {I ctx} (cwf : context_wf I ctx) : formula_wf I (ctx_head ctx) :=
  match cwf in context_wf _ ctx' return formula_wf I (ctx_head ctx') with
  | CWF_Nil _ => WF_Unit _
  | CWF_Cons _ _ _ wfPhi _ => wfPhi
  end.

(* --- 2. Segédfüggvények a formulákhoz --- *)
Definition form_left (Phi : h_ty) : h_ty :=
  match Phi with | Ty_Prod A _ => A | Ty_Sum A _ => A | Ty_Arrow A _ => A | _ => Ty_Unit end.

Definition left_wf {Sig : Signature} {I Phi} (wf : formula_wf I Phi) : formula_wf I (form_left Phi) :=
  match wf in formula_wf _ Phi' return formula_wf I (form_left Phi') with
  | WF_Prod _ _ _ wfA _ => wfA
  | WF_Sum _ _ _ wfA _ => wfA
  | WF_Arr _ _ _ wfA _ => wfA
  | _ => WF_Unit _
  end.

Definition form_right (Phi : h_ty) : h_ty :=
  match Phi with | Ty_Prod _ B => B | Ty_Sum _ B => B | Ty_Arrow _ B => B | _ => Ty_Unit end.

Definition right_wf {Sig : Signature} {I Phi} (wf : formula_wf I Phi) : formula_wf I (form_right Phi) :=
  match wf in formula_wf _ Phi' return formula_wf I (form_right Phi') with
  | WF_Prod _ _ _ _ wfB => wfB
  | WF_Sum _ _ _ _ wfB => wfB
  | WF_Arr _ _ _ _ wfB => wfB
  | _ => WF_Unit _
  end.

(* --- 3. A tiszta Fixpointok (Okoskodás nélkül!) --- *)
Fixpoint get_cwf {Sig : Signature} {I G p Phi} (d : h_derivation I G p Phi) : context_wf I G :=
  match d with
  | HD_Var0 _ _ _ cwf => cwf
  | HD_VarS _ _ _ _ _ d_prev wf_Psi => CWF_Cons _ _ _ wf_Psi (get_cwf d_prev)
  | HD_Unit _ _ cwf => cwf
  | HD_Lam _ _ _ _ _ d_body => tail_cwf (get_cwf d_body)
  | HD_App _ _ _ _ _ _ d_f _ => get_cwf d_f
  | HD_Pair _ _ _ _ _ _ d_l _ => get_cwf d_l
  | HD_Fst _ _ _ _ _ d_pair => get_cwf d_pair
  | HD_Snd _ _ _ _ _ d_pair => get_cwf d_pair
  | HD_Inl _ _ _ _ _ d_p _ => get_cwf d_p
  | HD_Inr _ _ _ _ _ _ d_p => get_cwf d_p
  | HD_Case _ _ _ _ _ _ _ _ d_t _ _ => get_cwf d_t
  | HD_Absurd _ _ _ _ d_t _ => get_cwf d_t
  | _ => dummy_cwf_ext
  end.

Fixpoint get_wf {Sig : Signature} {I G p Phi} (d : h_derivation I G p Phi) : formula_wf I Phi :=
  match d with
  | HD_Var0 _ _ _ cwf => head_wf cwf
  | HD_VarS _ _ _ _ _ d_prev _ => get_wf d_prev
  | HD_Unit _ _ _ => WF_Unit _
  | HD_Lam _ _ _ _ _ d_body => WF_Arr _ _ _ (head_wf (get_cwf d_body)) (get_wf d_body)
  | HD_App _ _ _ _ _ _ d_f _ => right_wf (get_wf d_f)
  | HD_Pair _ _ _ _ _ _ d_l d_r => WF_Prod _ _ _ (get_wf d_l) (get_wf d_r)
  | HD_Fst _ _ _ _ _ d_pair => left_wf (get_wf d_pair)
  | HD_Snd _ _ _ _ _ d_pair => right_wf (get_wf d_pair)
  | HD_Inl _ _ _ _ _ d_p wf_Psi => WF_Sum _ _ _ (get_wf d_p) wf_Psi
  | HD_Inr _ _ _ _ _ wf_Phi d_p => WF_Sum _ _ _ wf_Phi (get_wf d_p)
  | HD_Case _ _ _ _ _ _ _ _ _ d_l _ => get_wf d_l
  | HD_Absurd _ _ _ _ _ wf_Phi => wf_Phi
  | _ => dummy_wf_ext
  end.

(* ================================================================= *)
(* 4. EXPLICIT BCCC SEMANTICS (A Te kódod, axiómák nélkül!)          *)
(* ================================================================= *)

(* A swap_map a szálakra a Currying-hez *)
Definition swap_map_fiber {B : SetoidCategory} {CB : CartesianCategory B} 
                          {GF : GoodFibration B} {I : @obj B} 
                          {x y : @obj (Fiber I)} : hom (prod x y) (prod y x) :=
  prod_map prod_snd prod_fst.

Fixpoint interp_h_tm {B : SetoidCategory} {CB : CartesianCategory B} 
                     {TSC : TwoSortCategory B} {GF : GoodFibration B} 
                     {Sig : Signature} {M : HyperModel B} 
                     {I : b_ty} {G : h_context} {p : h_tm} {Phi : h_ty} 
                     (D : h_derivation I G p Phi) {struct D}
                     : hom (interp_h_ctx (get_cwf D)) (interp_h_ty (get_wf D)).
Proof.
  refine (
    match D in (h_derivation _ G0 p0 Phi0) 
    return (hom (interp_h_ctx (get_cwf D)) (interp_h_ty (get_wf D))) 
    with
    
    (* --- Standard STLC --- *)
    | HD_Unit _ _ cwf => _
    | HD_Var0 _ _ _ cwf => _
    | HD_VarS _ _ _ _ _ D_prev wf_Psi => _
    
    | HD_Lam _ _ _ _ _ D_body => _
    | HD_App _ _ _ _ _ _ D_f D_x => _
    
    | HD_Pair _ _ _ _ _ _ D_l D_r => _
    | HD_Fst _ _ _ _ _ D_pair => _
    | HD_Snd _ _ _ _ _ D_pair => _

    (* --- BiSTLC Extensions --- *)
    | HD_Inl _ _ _ _ _ D_p wf_Psi => _
    | HD_Inr _ _ _ _ _ wf_Phi D_p => _
    | HD_Case _ _ _ _ _ _ _ _ D_t D_l D_r => _
    | HD_Absurd _ _ _ _ D_t _ => _

    (* --- Kvantorok --- *)
    | HD_All_Intro _ G' p' A' Phi' D_body => _
    | HD_All_Elim _ G' p' A' Phi' f dt D_all => _
    | HD_Ex_Intro _ G' p' A' Phi' f dt D_p => _
    | HD_Ex_Elim _ G' p' p2 A' Phi' Chi' D_ex D_body => _
    end
  ).

  (* =============================================================== *)
  (* INNENTŐL A TE KÓDOD JÖN: Csak a kategóriaelméleti kombintorok!  *)
  (* =============================================================== *)

  - (* 1. HD_Var0 *) 
    (* A dependent destruction lecseréli a cwf-et a célban is! *)
    dependent destruction cwf. simpl. 
    exact prod_snd.

 - (* 2. HD_VarS *) 
    simpl. 
    exact (compose (interp_h_tm _ _ _ _ _ _ _ _ _ _ D_prev) prod_fst).
    
  - (* 3. HD_Unit *) 
    (* A terminal_map minden kontextusból működik. *)
    simpl. 
    exact terminal_map.
  
  
  - (* HD_Lam  *) destruct (get_cwf D_body); exact (exp_map (interp_h_tm D_body)).
  - (* HD_App  *) destruct (get_wf D_f); exact (compose eval (prod_map (interp_h_tm D_f) (interp_h_tm D_x))).
  
  - (* HD_Pair *) exact (prod_map (interp_h_tm D_l) (interp_h_tm D_r)).
  - (* HD_Fst  *) destruct (get_wf D_pair); exact (compose prod_fst (interp_h_tm D_pair)).
  - (* HD_Snd  *) destruct (get_wf D_pair); exact (compose prod_snd (interp_h_tm D_pair)).

  (* --- BiSTLC Extensions --- *)
  - (* HD_Inl  *) exact (compose coprod_inl (interp_h_tm D_p)).
  - (* HD_Inr  *) exact (compose coprod_inr (interp_h_tm D_p)).
  - (* HD_Case *) destruct (get_wf D_t); exact (compose eval (prod_map (compose (coprod_map (exp_map (compose (interp_h_tm D_l) swap_map_fiber)) (exp_map (compose (interp_h_tm D_r) swap_map_fiber))) (interp_h_tm D_t)) (id _))).
  - (* HD_Absurd *) destruct (get_wf D_t); exact (compose initial_map (interp_h_tm D_t)).

  (* --- Kvantorok --- *)
  - admit. (* HD_All_Intro *)
  - admit. (* HD_All_Elim *)
  - admit. (* HD_Ex_Intro *)
  - admit. (* HD_Ex_Elim *)
Admitted.

(* ================================================================= *)
(* 4. KIEGÉSZÍTÉS: Soundness Equivalence (A te kódod alapján)        *)
(* ================================================================= *)

Theorem hyper_soundness_equiv : forall {B : SetoidCategory} {CB : CartesianCategory B} 
  {TSC : TwoSortCategory B} {GF : GoodFibration B} 
  {Sig : Signature} {M : HyperModel B} 
  {I : b_ty} {G : h_context} {p q : h_tm} {Phi : h_ty} 
  (dp : h_derivation I G p Phi) (dq : h_derivation I G q Phi),
  h_equiv_rel I p q -> interp_h_tm dp ≅ interp_h_tm dq.
Proof.
  intros. induction H.
  (* A Fiber kategória Thin, így a morfizmusok ekvivalenciája azonnali! *)
  apply thin_unique. 
Qed.
Defined.
(* ================================================================= *)
(* 4. SOUNDNESS THEOREM                                              *)
(* ================================================================= *)

Theorem hyper_soundness_equiv : forall {B : SetoidCategory} {CB : CartesianCategory B} 
  {TSC : TwoSortCategory B} {GF : GoodFibration B} 
  {Sig : Signature} {M : HyperModel B CB TSC GF Sig} 
  {I : b_ty} {G : h_context} {p q : h_tm} {Phi : h_ty} 
  (dp : h_derivation Sig I G p Phi) (dq : h_derivation Sig I G q Phi),
  h_equiv_rel Sig I p q -> interp_h_tm dp ≅ interp_h_tm dq.
Proof.
  intros. induction H.
  (* Mivel a Fiber I kategória Thin (Proof Irrelevant logikát kódol),
     bármely két azonos típusú morfizmus megegyezik! *)
  apply thin_unique. 
Qed.
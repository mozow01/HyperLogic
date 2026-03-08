Require Import HyperLogic.Logic.Base.Epsilon.Base_Syntax.
Require Import HyperLogic.Logic.Hyper.Epsilon.Hyper_Syntax.

Require Import List.
Import ListNotations.

(* ================================================================= *)
(* A GENERIKUS DUÁLIS DRINKER PARADOXON (Minden formulára)           *)
(* ================================================================= *)

(* A formula: \exists x. ( (\exists y. Phi(y)) -> Phi(x) )
   Itt a Phi BÁRMILYEN formula lehet, ami az I x D kontextusban értelmezett! *)
Definition Dual_Drinker_Generic {Sign : Type} (I D : b_ty) (Phi : @h_ty Sign) : @h_ty Sign :=
  Ty_Ex D ( 
    (* KIKÉNYSZERÍTJÜK, hogy a hiperdoktrína (h_ty) nyílját használja a Coq, 
       és ne az STLC-s propozicionális nyilat! *)
    (Ty_Arrow : @h_ty Sign -> @h_ty Sign -> @h_ty Sign) 
    (form_pullback b_fst (Ty_Ex D Phi)) 
    Phi 
  ).

(* A FŐTÉTEL: Bármely I, D bázis felett és BÁRMELY Phi formulára igaz! *)
Lemma dual_drinker_general {Sign : Type} `{SkolemMapping Sign} 
  (I D : b_ty) (Phi : @h_ty Sign) : 
  exists (p : @h_tm Sign), h_typing I [] p (Dual_Drinker_Generic I D Phi).
Proof.
Admitted.
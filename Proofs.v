(**************************************************************************)
(*  This is part of STATES, it is distributed under the terms of the      *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                        *)
(**************************************************************************)

Require Import Relations Morphisms.
Require Import Program.
Require Memory Terms Decorations Axioms Derived_Pairs Derived_Products.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export ProofsExp := Derived_Products.Make(M). 

(* --- Main Proofs --- *)

 (** Annihilation update lookup **)
 Theorem ALU: forall i: Loc, 
         update i o lookup i == id.
 Proof.
     intro i. apply local_global. intro k.
     destruct (Loc_dec i k) as [e|n]. rewrite <- e.
     (*Case k = i*)
     rewrite assoc.
     rewrite ax1, ids, idt. reflexivity.
     (*Case k <> i*)
     rewrite assoc. rewrite ax2; [| exact n].
       rewrite <- assoc. rewrite s_unit; [| decorate].
       cut (forget == id). intro H1. rewrite H1.
       reflexivity.
       (* forget == id *)
         symmetry. apply s_unit. decorate.
 Qed.

 (** Interaction lookup lookup **)
 Theorem interaction_lookup_lookup: forall i,
         lookup i o forget o lookup i == lookup i.
 Proof.
     intro i. rewrite <- assoc.
       rewrite s_unit; [| decorate].
         cut (forget == id).
         intro H0. rewrite H0, ids. reflexivity.
           symmetry. apply s_unit; decorate.
 Qed.

 (** Interaction update update **)
 Theorem IUU: forall i: Loc, 
         update i o pi2 o rprod (update i) (@id (Val i)) 
         == 
         update i o @pi2 (Val i) (Val i).
 Proof.
    intro i. apply local_global. intro k. destruct (Loc_dec i k) as [e|n]. rewrite <- e.
    (*Case k = i*)
    do 2 rewrite assoc. rewrite ax1.
    setoid_rewrite assoc at 2. rewrite ax1.
      do 2 rewrite idt.
    unfold rprod, permut. rewrite assoc.
      rewrite s_lpair_eq; [| decorate].
      rewrite w_lpair_eq; [rewrite idt; reflexivity| decorate].
    (*Case k <> i*)
    do 2 rewrite assoc. rewrite ax2; [| exact n].
    setoid_rewrite <- assoc at 2.
      cut(forget o pi2 == (@pi1 unit (Val i))).
      intro H. rewrite H.
      unfold rprod, permut. 
      do 2 setoid_rewrite assoc at 1. setoid_rewrite <- assoc at 2.
        cut (pi1 o pair pi2 pi1 == (@pi2 (Val i) unit)). intro H1. rewrite H1.
        rewrite <- assoc. rewrite s_lpair_eq; [| decorate]. rewrite assoc.
        setoid_rewrite ax2; [| decorate| decorate].
        setoid_rewrite <- assoc. setoid_rewrite s_unit;
          [reflexivity| decorate| decorate].
        (*2nd cut*)
        apply wtos; [decorate| decorate| apply w_lpair_eq; decorate].
      (*1st cut*)
      apply wtos; [decorate| decorate| apply w_unit].
 Qed.

 (** Interaction update lookup **)
 Theorem IUL: forall i: Loc,
         lookup i o update i ~ id. (* Prop: 2.4: All Cases *)
 Proof. intro i. apply ax1. Qed.

 Theorem commutation_lookup_lookup: forall i j: Loc, i<>j ->
         (lprod id (lookup j)) o (inv_pi1 o lookup i)
         == 
         permut o (lprod id (lookup i)) o (inv_pi1 o lookup j). 
         (* Prop: 2.5: All Cases *)
 Proof.
    intros i j n. apply lpair_u. split.
    (*Case pi1*)
    unfold lprod at 1. rewrite assoc. 
    rewrite w_lpair_eq; [| decorate].
      rewrite idt.
      unfold inv_pi1 at 1.
    rewrite assoc, w_lpair_eq; [| decorate].
      rewrite idt.
    unfold permut, lprod. rewrite assoc. setoid_rewrite assoc at 2.
      rewrite w_lpair_eq; [| decorate].
    rewrite assoc, s_lpair_eq; [| decorate].
    do 2 rewrite <- assoc. setoid_rewrite assoc at 2. unfold inv_pi1.
      rewrite s_lpair_eq; [| decorate].
    rewrite s_unit; [| decorate].
    cut (forget == (@id unit)). intro H. rewrite H.
      rewrite ids. reflexivity.
    (*1st cut*)
    symmetry. apply s_unit; decorate.
    (*Case pi2*)
    unfold lprod at 1.
    rewrite assoc. rewrite s_lpair_eq; [| decorate].
    unfold inv_pi1 at 1.
    rewrite <- assoc. setoid_rewrite assoc at 2.
    rewrite s_lpair_eq; [| decorate].
    rewrite s_unit; [| decorate].
      cut (forget == (@id unit)).
      intro H. rewrite H. rewrite ids.
      unfold permut, lprod. do 3 rewrite assoc.
        rewrite s_lpair_eq; [| decorate].
        rewrite <- assoc.
        apply wtos; [decorate| decorate| ].
        rewrite w_lpair_eq, idt; [| decorate].
        unfold inv_pi1. rewrite assoc.
        rewrite w_lpair_eq; [rewrite idt; reflexivity| decorate]. 
      (*1st cut*)
      symmetry. apply s_unit; decorate.
 Qed.

 (** Commutation update update **)
 Theorem commutation_update_update: forall i j: Loc, i<>j ->
         update j o (pi2 o (rprod (update i) (@id (Val j)))) 
         == 
         update i o (pi1 o (lprod (@id (Val i)) (update j))). 
 Proof.
   intros i j m. apply local_global. intro k.
     destruct (Loc_dec k i) as [s|t]. rewrite s.
     (* k = i *)
     rewrite assoc. rewrite ax2; [| auto].
     unfold rprod, permut. setoid_rewrite assoc at 2.
       rewrite s_lpair_eq; [| decorate].
       rewrite <- assoc. setoid_rewrite assoc at 2.
       cut (forget o pi1 == (@pi2 (Val j) unit)).
         intro H. rewrite H.
       rewrite s_lpair_eq; [| decorate].
       rewrite assoc, ax1, idt.
     rewrite assoc, ax1, idt.
     unfold lprod. rewrite w_lpair_eq, idt; [| decorate].
     reflexivity.
       (*1st cut*)
       setoid_rewrite s_unit; [reflexivity| decorate| decorate].
     (* k <> i *)
       (* k = j *)
       destruct (Loc_dec k j) as [n | r]. rewrite n.
       rewrite assoc, ax1, idt. 
       unfold rprod, permut.
       rewrite assoc. rewrite s_lpair_eq; [| decorate].
       rewrite w_lpair_eq; [| decorate]. rewrite idt.
       (**)
       rewrite assoc. rewrite ax2; [| auto].
       rewrite assoc. setoid_rewrite <- assoc at 2.
       cut (forget o pi1 == (@pi2 (Val i) unit)).
         intro H. rewrite H.
         rewrite <- assoc. unfold lprod.
         rewrite s_lpair_eq; [| decorate].
         rewrite assoc, ax1, idt.
         reflexivity.
       (*1st cut*)
       setoid_rewrite s_unit; [reflexivity| decorate| decorate].
       (* k <> j *)
       unfold rprod, permut.
       setoid_rewrite assoc at 3.
       rewrite s_lpair_eq; [| decorate].
       setoid_rewrite assoc; setoid_rewrite ax2; [| auto| auto].
       setoid_rewrite <- assoc. setoid_rewrite assoc at 2.
       cut(forget o pi1 == (@pi2 (Val j) unit)).
         intro H. rewrite H.
         rewrite s_lpair_eq; [| decorate].
       setoid_rewrite assoc at 3.
       cut(forget o pi1 == (@pi2 (Val i) unit)).
         intro H1. rewrite H1. unfold lprod.
         rewrite s_lpair_eq; [| decorate].
       setoid_rewrite assoc; setoid_rewrite ax2; [| auto| auto].
       setoid_rewrite <- assoc.
       setoid_rewrite s_unit; [reflexivity| decorate| decorate].
         (*1st cut*)
       setoid_rewrite s_unit; [reflexivity| decorate| decorate].
         (*2nd cut*)
       setoid_rewrite s_unit; [reflexivity| decorate| decorate].
 Qed.     

 (** Commutation update lookup **)
 Theorem commutation_update_lookup: forall i j: Loc, i<>j -> 
          lookup j o update i 
          == 
          pi2 o (rprod (update i) id o (lprod (@id (Val i)) (lookup j) o (inv_pi1))). 
 Proof.
   intros i j n. apply effect.
     (* Case 1: <> o f == <> o g *)
     rewrite assoc.
     (* 1st cut *)
     cut (forget o lookup j == (@id (unit))).
       intro H0. rewrite H0, idt.
       unfold lprod, rprod, permut.
       setoid_rewrite assoc at 2. setoid_rewrite assoc at 3.
       rewrite s_lpair_eq; [| decorate].
       setoid_rewrite <- assoc. rewrite assoc at 1.
       (* 2nd cut *)
       cut (forget o pi1 == (@pi2 (Val j) unit)).
         intro H1. rewrite H1.
         rewrite assoc.
         rewrite s_lpair_eq; [| decorate].
         rewrite <- assoc. setoid_rewrite assoc at 2.
         (* 3rd cut *)
         cut (pi1 o pair (id o pi1) (lookup j o pi2) == id o (@pi1 (Val i) unit)).
           intro H2. rewrite H2, idt.
           unfold inv_pi1.
           (* 4th cut *)
           cut (pi1 o pair id forget == (@id (Val i))).
             intro H3. rewrite H3, ids.
             reflexivity.
           (* 4th cut *)
           apply wtos; [decorate| decorate| apply w_lpair_eq; decorate].
         (* 3rd cut *)
         apply wtos; [decorate| decorate| rewrite w_lpair_eq; [reflexivity| decorate]].
       (* 2nd cut *)
       setoid_rewrite s_unit; [reflexivity| decorate| decorate].
     (* 1st cut *)
     setoid_rewrite s_unit; [reflexivity| decorate| decorate].
     (* Case 2: f ~ g *)
     unfold lprod, rprod, permut.
     setoid_rewrite assoc at 1. setoid_rewrite assoc at 2.
     rewrite s_lpair_eq; [| decorate].
     rewrite w_lpair_eq; [| decorate].
     rewrite idt. rewrite assoc.
     rewrite s_lpair_eq; [| decorate].
     unfold inv_pi1. rewrite <- assoc.
     rewrite s_lpair_eq; [| decorate].
     apply ax2; exact n.
 Qed.

 (** Commutation lookup constant **)
 Theorem CLC: forall i j: Loc, forall c: (Val i), 
         (lookup i o (update i o (constant c)))
         == 
         (constant c) o update i o (constant c).
 Proof.
     intros i j c. apply effect.
     (* Case 1: <> o f == <> o g *)
     rewrite assoc.
     cut (forget o lookup i == (@id unit)).
       intro H. rewrite H, idt.
       do 2 rewrite assoc.
       cut (forget o constant c == (@id unit)).
         intro H1; rewrite H1, idt.
         reflexivity.
       (*1st cut*)
       setoid_rewrite s_unit; [reflexivity| decorate| decorate].
     (*2nd cut*)
     setoid_rewrite s_unit; [reflexivity| decorate| decorate].
     (* Case 2: f ~ g *)
     rewrite assoc, ax1, idt.
     rewrite <- assoc.
     cut (update i o constant c ~ (@id unit)).
       intro H; rewrite H, ids.
       reflexivity.
     (*1st cut*)
     apply w_unit.
 Qed.

(* -------------------- End of Main Proofs -------------------- *)

End Make.



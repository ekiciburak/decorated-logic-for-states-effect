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
Require Memory Terms Decorations Axioms.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export Derived_PairsExp := Axioms.Make(M). 

 Definition permut {X Y}: term (X*Y) (Y*X) := pair pi2 pi1.
 Definition rpair {X Y Z} (f: term Y X) (g: term Z X): term (Y*Z) X := permut o pair g f.

 Definition inv_pi1 {X}: term (X*unit) X := pair id forget. 

 Lemma is_rpair: forall k X Y Z (f1: term Y X) (f2: term Z X), RO f2 -> is k f1 -> is k f2 -> is k (rpair f1 f2). (* FIXED *)
 Proof. intros k X Y Z f1 f2 H1 H2 H3. induction k; decorate. Qed.

 Lemma is_permut X Y: is pure (@permut X Y).
 Proof. decorate. Qed.

 Lemma is_inv_pi1 X: is pure (@inv_pi1 X).
 Proof. decorate. Qed.

 Lemma s_rpair_eq: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   RO f2 -> pi1 o rpair f1 f2 == f1.
 Proof.
     intros X Y' Y f1 f2 H0. unfold rpair. unfold permut. rewrite assoc.
     cut (pi1 o pair pi2 pi1 == (@pi2 Y' Y)).
       intro H1. rewrite H1.
       apply s_lpair_eq. exact H0.
     apply wtos; try decorate. apply w_lpair_eq; decorate.
 Qed.

 Lemma w_rpair_eq: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   RO f2 -> pi2 o rpair f1 f2 ~ f2.
 Proof.
     intros X Y' Y f1 f2 H0. unfold rpair. unfold permut. rewrite assoc.
     rewrite s_lpair_eq; [apply w_lpair_eq; decorate| decorate].
 Qed.

 Lemma lpair_u: forall X Y Y'(f g: term (Y'*Y) X),
   (pi1 o f ~ pi1 o g) /\ (pi2 o f == pi2 o g) -> f == g.
 Proof.
     intros X Y Y' f g (H0&H1). apply effect. 
     cut(forget o (@pi2 Y' Y) == forget).
       intro H2. rewrite <- H2.
       setoid_rewrite <- assoc. apply replsubs; [reflexivity| exact H1].
     (* 1st cut *)
     setoid_rewrite s_unit; [reflexivity| decorate].
     apply lpair_ueq. exact H0. apply stow. exact H1.
 Qed.

 Lemma rpair_u: forall X Y Y'(f g: term (Y'*Y) X),
   (pi1 o f == pi1 o g) /\ (pi2 o f ~ pi2 o g) -> f == g.
 Proof.
     intros X Y Y' f g (H0&H1). apply effect.
     cut(forget o (@pi1 Y' Y) == forget).
       intro H2. rewrite <- H2.
       setoid_rewrite <- assoc. apply replsubs; [reflexivity| exact H0].
     (* 1st cut *)
     setoid_rewrite s_unit; [reflexivity| decorate].
     apply lpair_ueq. apply stow. exact H0. exact H1.
 Qed.

(* -------------------- End of Derived Pairs -------------------- *)

End Make.


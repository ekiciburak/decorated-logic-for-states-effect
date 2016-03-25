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
Require Memory Terms Decorations Axioms Derived_Pairs.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export Derived_ProductsExp := Derived_Pairs.Make(M). 

 Definition lprod {X Y X' Y'} (f: term X X') (g: term Y Y'): term (X*Y) (X'*Y') := pair (f o pi1) (g o pi2).
 Definition rprod {X Y X' Y'} (f: term X X') (g: term Y Y') := permut o pair (g o pi2) (f o pi1).

 Lemma is_lprod: forall k X' X Y' Y (f1: term X X') (f2: term Y Y'), RO f1 -> is k f1 -> is k f2 ->  is k (lprod f1 f2). (* FIXED *)
 Proof. intros. induction k; decorate. Qed.  
 
 Lemma is_rprod: forall k X' X Y' Y (f1: term X X') (f2: term Y Y'), is k f1 -> RO f2 -> is k f2 -> is k (rprod f1 f2).  (* FIXED *)
 Proof. intros k X' X Y' Y f1 f2 H1 H2 H3. induction k; decorate. Qed.

 Lemma w_lprod: forall X' X Y' Y (f: term X' X) (g: term Y' Y), RO f -> pi1 o (lprod f g) ~ f o pi1.
 Proof. intros X' X Y' Y f g H1. apply w_lpair_eq; decorate. Qed.

 Lemma s_lprod: forall X' X Y' Y (f: term X' X) (g: term Y' Y), RO f -> pi2 o (lprod f g) == g o pi2.
 Proof. intros intros X' X Y' Y f g. apply s_lpair_eq; decorate. Qed.

 Lemma w_prod: forall X' X Y' Y (f: term X' X) (g: term Y' Y), RO g -> pi2 o rprod f g ~ g o pi2.
 Proof. intros X' X Y' Y f g H1. apply w_rpair_eq; decorate. Qed.

 Lemma s_rprod: forall X' X Y' Y (f: term X' X) (g: term Y' Y), RO g -> pi1 o (rprod f g) == f o pi1.
 Proof. intros X' X Y' Y f g H1. apply s_rpair_eq; decorate. Qed.

 Lemma lprod_u: forall X X' Y Y'(f g: term (Y*Y') (X*X')), (pi1 o f ~ pi1 o g) /\ (pi2 o f == pi2 o g) -> f == g.
 Proof. intros X X' Y Y' f g (H0&H1). apply lpair_u. split; [exact H0| exact H1]. Qed.

 Lemma sprod_u: forall X X' Y Y'(f g: term (Y*Y') (X*X')), (pi1 o f == pi1 o g) /\ (pi2 o f ~ pi2 o g) -> f == g.
 Proof. intros X X' Y Y' f g (H0&H1). apply rpair_u. split; [exact H0| exact H1]. Qed.

End Make.


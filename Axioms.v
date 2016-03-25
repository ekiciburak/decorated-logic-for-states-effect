(**************************************************************************)
(*  This is part of STATES, it is distributed under the terms of the      *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*             Burak Ekici, Damien Pous.                                  *)
(**************************************************************************)

Require Import Relations Morphisms.
Require Import Program.
Require Memory Terms Decorations.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export AxiomsExp := Decorations.Make(M).

 Reserved Notation "x == y" (at level 80).
 Reserved Notation "x ~ y" (at level 80).

 Definition idem X Y (x y: term X Y) := x = y.

 Inductive strong: forall X Y, relation (term X Y) :=
 | refl X Y: Reflexive (@strong X Y)
 | sym: forall X Y, Symmetric (@strong X Y)
 | trans: forall X Y, Transitive (@strong X Y)
 | replsubs: forall X Y Z, Proper (@strong X Y ==> @strong Y Z ==> @strong X Z) comp
 | ids: forall X Y (f: term X Y), f o id == f
 | idt: forall X Y (f: term X Y), id o f == f
 | assoc: forall X Y Z T (f: term X Y) (g: term Y Z) (h: term Z T), f o (g o h) == (f o g) o h
 | wtos: forall X Y (f g: term X Y), RO f -> RO g -> f ~ g -> f == g
 | s_lpair_eq: forall X Y' Y (f1: term Y X) (f2: term Y' X), RO f1 -> pi2 o pair f1 f2 == f2
 | effect: forall X Y (f g: term Y X), forget o f == forget o g -> f ~ g -> f == g
 | local_global: forall X (f g: term unit X), (forall i: Loc, lookup i o f ~ lookup i o g) -> f == g
 | tcomp: forall X Y Z (f: Z -> Y) (g: Y -> X), tpure (compose g f) == tpure g o tpure f
 with weak: forall X Y, relation (term X Y) :=
 | wsym: forall X Y, Symmetric (@weak X Y)
 | wtrans: forall X Y, Transitive (@weak X Y)
 | pwrepl: forall A B C (g: term C B), (PURE g) ->  Proper (@weak B A ==> @weak C A) (comp g)
 | wsubs: forall A B C, Proper (@weak C B ==> @idem B A ==> @weak C A) comp
 | stow: forall  X Y (f g: term X Y), f == g -> f ~ g
 | w_lpair_eq: forall X Y' Y (f1: term Y X) (f2: term Y' X), RO f1 -> pi1 o pair f1 f2 ~ f1
 | w_unit: forall X (f g: term unit X), f ~ g    
 | ax1: forall i, lookup i o update i ~ id
 | ax2: forall i j, i<>j -> lookup j o update i ~ lookup j o forget
 | lpair_ueq: forall  X Y Y'(f g: term (Y*Y') X), pi1 o f ~ pi1 o g -> pi2 o f ~ pi2 o g -> f ~ g
   where "x == y" := (strong x y)
   and "x ~ y" := (weak x y).

 Instance wisrefl X Y: Reflexive (@weak X Y).
 Proof. intro f. apply stow, refl. Qed.
 
 Instance strong_is_equivalence X Y: Equivalence (@strong X Y).
 Proof. constructor; intro. apply refl. apply sym. apply trans. Qed.

 Instance weak_is_equivalence X Y: Equivalence (@weak X Y).
 Proof. constructor; intro. apply stow. apply refl. intros. apply wsym. assumption. apply wtrans. Qed.

 Instance strong_is_weak_equivalence: forall X Y, subrelation (@strong X Y) (@weak X Y).
 Proof. constructor. apply stow,sym. assumption. Qed.

 Lemma s_unit: forall X (f: term unit X), (RO f) ->  f == forget.
 Proof. intros X f H. apply wtos; [exact H| decorate| apply w_unit]. Qed.


 (*
 Parameters X Y Z: Type.
 Check (respectful (@strong Y Z) (@strong X Z)).
 Check (respectful (@strong Y Z) (@weak X Z)).
 Check respectful (@strong X Y) (respectful (@strong Y Z) (@strong X Z)).
 Check ((@strong X Y) ==> (@strong Y Z) ==> (@strong X Z)).
 Check  Proper (@strong X Y ==> @strong Y Z ==> @strong X Z) comp. *)

 Existing Instance wsubs.
 Existing Instance pwrepl.
 Existing Instance replsubs.

 Goal forall X Y Z (f f': term Y Z) (g: term X Y), PURE g -> f ~ f' ->  g o f ~ g o f'.
 Proof. intros X Y Z f f' g H0 H1. setoid_rewrite <- H1. reflexivity. Qed. 

 Goal forall X Y Z (f f': term X Y) (g: term Y Z), f ~ f' -> f o g ~ f' o g.
 Proof. intros X Y Z f f' g H0. setoid_rewrite <- H0. reflexivity. Qed.
 
End Make.


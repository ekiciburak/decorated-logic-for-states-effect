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
Require Memory Terms.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export DecorationsExp := Terms.Make(M). 

 Inductive kind := pure | ro | rw.

 Inductive is: kind -> forall X Y, term X Y -> Prop :=
  | is_tpure: forall X Y (f: X -> Y), is pure (@tpure X Y f)
  | is_comp: forall k X Y Z (f: term X Y) (g: term Y Z), is k f -> is k g -> is k (f o g)
  | is_pair: forall k X Y Z (f: term X Z) (g: term Y Z), is ro f -> is k f -> is k g -> is k (pair f g) (* FIXED *)
  | is_lookup: forall i, is ro (lookup i)   
  | is_update: forall i, is rw (update i)
  | is_pure_ro: forall X Y (f: term X Y), is pure f -> is ro f
  | is_ro_rw: forall X Y  (f: term X Y), is ro f -> is rw f.

 Hint Constructors is.

(*---*)

 Lemma is_id X: is pure (@id X).
 Proof. unfold id. apply is_tpure. Qed.

 Lemma is_pi1 X Y: is pure (@pi1 X Y).
 Proof. apply is_tpure. Qed.

 Lemma is_pi2 X Y: is pure (@pi2 X Y).
 Proof. apply is_tpure. Qed.

 Lemma is_forget X: is pure (@forget X).
 Proof. apply is_tpure. Qed. 

 Lemma is_constant {X: Type} (v: X): is pure (constant v).
 Proof. apply is_tpure. Qed.

(*---*)

 Hint Constructors is.

 Ltac decorate :=  solve[
                          repeat (apply is_comp || apply is_pair)
                            ||
		                 (apply is_tpure || apply is_lookup || apply is_update || assumption)
			    || 
                                 (apply is_pure_ro)
			    || 
		                 (apply is_ro_rw)
                        ].

 Class PURE {A B: Type} (f: term A B) := isp : is pure f.
 Hint Extern 0 (PURE _) => decorate : typeclass_instances.

 Class RO {A B: Type} (f: term A B) := isro : is ro f.
 Hint Extern 0 (RO _) => decorate : typeclass_instances.

 Class RW {A B: Type} (f: term A B) := isrw : is rw f.
 Hint Extern 0 (RW _) => decorate : typeclass_instances.

End Make.

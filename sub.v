Require Import ssreflect.
From Coq.Relations Require Import Relations Relation_Operators.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A stupid property of the transitive closure. *)


(* We have two sub-relations A and B of V, which we now is a strict
  partial order: then we want to show that if V is a strict partial
  order, then thw tranisitive closure of A union B cannot have cycles
  *)

(* e.g. A is PO, B is RF, AUBT is CO/HB and V = is visibility *)

Section RelFacts.

Variable X : Type.
Variables (A B V: relation X).

Definition irreflexive (f : relation X) := forall x, f x x -> False.

Definition contains (f g : relation X) :=  forall x y, f x y -> g x y.

Hypothesis AinV: contains A V.
Hypothesis BinV: contains B V.

Hypothesis transV: transitive X V.
Hypothesis irrV: irreflexive V.
Hypothesis antiV: antisymmetric X V.

Hypothesis transA: transitive X A.
Hypothesis irrA: irreflexive A.
Hypothesis antiA: antisymmetric X A.

Definition AUBT : relation X := clos_trans _ (union _ A B).

(* This holds trivially then *) 

Lemma AUBTinV : contains AUBT V.
Proof.  
move=> x y /= H; elim:H=>{x y}x0 y0; first by case; [move/AinV|move/BinV].
by move=>z _ /transV H1 _ /H1.
Qed.

(* AUBT cannot have cycles, because V does not ahve them *)

Lemma irrAUBT : irreflexive AUBT.
Proof. by move=>x /= /AUBTinV /irrV. Qed.

End RelFacts.
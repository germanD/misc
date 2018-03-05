Require Import ssreflect.
From Coq.Relations Require Import Relations Relation_Operators.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A stupid property of the transitive closure *)

Section RelFacts.

Variable X : Type.
Variables (A B V: relation X).

Definition irreflexive (f : relation X) := reflexive X A -> False.

Definition contains (f g : relation X) :=  forall x y: X, f x y -> g x y.

Hypothesis AinV: contains A V.
Hypothesis BinV: contains B V.

Hypothesis transV: transitive X V.

Definition AUBT : relation X := clos_trans _ (union _ A B).

(* This holds trivially then *) 

Lemma AUBTinV : contains AUBT V.
Proof.  
move=> x y /= H; elim:H=>{x y}x0 y0; first by case; [move/AinV|move/BinV].
by move=>z _ /transV H1 _ /H1.
Qed.

End RelFacts.
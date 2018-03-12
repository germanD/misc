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

Hypothesis AinV: inclusion X A V.
Hypothesis BinV: inclusion X B V.

Hypothesis transV: transitive X V.
Hypothesis irrV: irreflexive V.

Hypothesis transA: transitive X A.
Hypothesis irrA: irreflexive A.

Definition AUBT : relation X := clos_trans _ (union _ A B).

(* Transitive + IRR => Anti *) 

Lemma antiV: antisymmetric _ V.
Proof. move=>x y /transV H1 /H1 /irrV //. Qed.

Lemma AUBTinV : inclusion _ AUBT V.
Proof.  
move=> x y /= H; elim:H=>{x y}x0 y0; first by case; [move/AinV|move/BinV].
by move=>z _ /transV H1 _ /H1.
Qed.

(* AUBT cannot have cycles, because V does not have them *)

Lemma irrAUBT : irreflexive AUBT.
Proof. by move=>x /= /AUBTinV /irrV. Qed.

(* AUBT trans: this should be trivial *)

Lemma transAUBT : transitive _ AUBT.
Proof. by exact:t_trans. Qed.

(* AUBT anti: this is trivial as it is irreflexive and transitive*)

Lemma antiAUBT : antisymmetric _ AUBT.
Proof. move=>x y /transAUBT H2 /H2 /irrAUBT //. Qed. 

Definition close {X} (r:relation X) (o:X) :=
  fun x y =>  r x o /\ r y o /\ r x y.  

End RelFacts.




 
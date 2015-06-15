(* scratch.v  *)

Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.

Variables A : Type.

Parameter RR: A * A -> A * A  -> Prop.

Axiom RR_refl: forall ab, RR ab ab.
Axiom RR_trans: forall a b c, RR a b -> RR b c -> RR a c.

Parameter O : A -> A -> Prop.
Axiom O_refl: forall ab, RR ab ab.
Axiom O_trans: forall a b c, RR a b -> RR b c -> RR a c.
Parameter P : A -> A -> Prop.
Axiom P_refl: forall ab, RR ab ab.
Axiom P_trans: forall a b c, RR a b -> RR b c -> RR a c.
Parameter S: A * A -> A.

Fixpoint R (n: nat) (i j :A ) : Prop:=
  match n with 
    | 0 => i = j
    | n.+1 => exists h, (O i h \/ P i h) /\ R n h j
  end.

(* Axiom e0: forall ab j, R 0 ab j -> E j ab. *)

Axiom R_refl: forall ab, RR ab ab.
Axiom R_trans: forall a b c, RR a b -> RR b c -> RR a c.

Definition H1 a b j:= exists n, R n (S (a , b)) j.


Lemma Lcross: forall (a b: A) (j : A),
   (H1 a b j) -> exists a' b', j = (S (a',b')) /\ RR (a,b) (a',b').
Proof. 
move=> a b j [n] H; elim: n a b H=>[|n IH]a0 b0 /=.
+ by move=> H; exists a0, b0; split=>//; apply: RR_refl.
move=>[h]H.
suff: exists a1 b1, h = S (a1,b1) /\ RR (a0,b0) (a1,b1).
+ move=>[a1][b1][E]; rewrite E in H *; case: H=>H /IH[a2][b2][->].
 by move/(RR_trans _ _ _ _)=> H1 /H1 T; exists a2, b2;split=>//. 
Admitted.
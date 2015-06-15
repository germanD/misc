(* scratch.v  *)

Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.


Inductive e : Type :=
  | enil : e
  | eC : e -> e
  | eP : e ->e.

Inductive evol : e -> e -> Prop :=
 | er : forall j k, j = k ->  evol j k
 | ep : forall j k, evol j k -> evol j (eP k).

Lemma e_refl: forall e, evol e e.
Proof. by move=> H //; constructor. Qed.

Lemma evol_eP i j: evol (eP i) j -> evol i j.
Proof.
move=> H2; elim: j H2=>[|e IH| e IH]H2; inversion H2; try (by discriminate H).
+ by rewrite -H; apply: ep; constructor.
by apply: ep; apply: IH.
Qed.

Lemma e_trans: forall i j k, evol i j -> evol j k -> evol i k.
Proof. 
move=> i; elim=>//=[||]k/=. case=>//.

move=>i j k H1; elim=>//. IH H1 H2.
apply: H1. 


elim=> i1 j1; first by move=>->.
 [|H IH H2].
 H1 H2.
elim: H1. 
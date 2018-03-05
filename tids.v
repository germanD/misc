(* scratch.v  *)
Require Import ssreflect ssrbool.
From mathcomp Require Import ssrnat eqtype seq.

(* tids Implemented from scratch *)

Inductive tid : Type :=
  | enil : tid
  | eC : tid -> tid
  | eP : tid -> tid.

Inductive evol : tid -> tid -> Prop :=
 | er : forall j k, j = k ->  evol j k
 | ep : forall j k, evol j k -> evol j (eP k).


(* We need to reason about suffixes in order to prove the transitivity
of congruence, and to proof left inversion lemmas *) 

Fixpoint allP (e : tid) : Prop := 
  match e with 
    | enil => True 
    | eC x => False 
    | eP x => allP x 
  end.


Lemma allp_ep: forall e, allP e -> allP (eP e).
Proof. by []. Qed.

Lemma evol_enil: forall e, evol e enil <-> e = enil.
Proof.
split=>//[H|->]; last by constructor.
by inversion H; rewrite H0.
Qed.

Lemma evol_nile: forall e, allP e <-> evol enil e.
Proof. 
split; first by elim: e=>//[_| e IH /IH /ep]//; constructor.
elim: e=>//= e IH H; first by inversion H; discriminate H0.
inversion H; first by discriminate H0.
by apply: IH.
Qed.

Lemma evol_ec: forall e e1, evol e (eC e1) <-> e = eC e1.
Proof.
split=>//[H|->]; last by constructor.
by inversion H; rewrite H0.
Qed.

Lemma evol_ep: forall e e1, evol e (eP e1) <-> e = eP e1 \/ evol e e1.
Proof. 
split;last by case=>[->|/ep//]; constructor.
move=> H; inversion H; first (by left); by right.
Qed.

Lemma evol_epW i j: evol (eP i) j -> evol i j.
Proof.
move=> H2; elim: j H2=>[|e IH| e IH]H2; inversion H2; try (by discriminate H).
+ by rewrite -H; apply: ep; constructor.
by apply: ep; apply: IH.
Qed.

Lemma evol_epS i j: evol (eP i) j -> evol i (eP j).
Proof. by move/evol_epW/ep. Qed.

Lemma e_refl: forall e, evol e e.
Proof. by move=> H //; constructor. Qed.

Lemma e_trans: forall i j k, evol i j -> evol j k -> evol i k.
Proof. 
move=>i j; elim:j i=>//=[i k|j IH i k|j IH i k]//;first by move/evol_enil=>->.
+ by move/evol_ec=>->.
by move/evol_ep=>[->//|H H3]; apply:(@IH _ _ H); apply: evol_epW.
Qed.

Lemma e_anti: forall i j, evol i j -> evol j i -> i = j.
Proof. 
elim=>//=[j H|i IH j H|i IH j]//; first by move/evol_enil=>->.
+ by move/evol_ec=>->.
move=> H; inversion H; first by rewrite H0.
move=> H3; inversion H3; first by rewrite H4.
by rewrite (IH _  (evol_epW _ _ H0) (evol_epW _ _ H6)).
Qed.


Fixpoint tidcat (t1 t2: tid) : tid :=
  match t2 with
      | enil => t1
      | eC t => eC (tidcat t1 t)
      | eP t => eP (tidcat t1 t)
  end.

Lemma tidcate0 t: tidcat t enil = t.
Proof. by done. Qed.

Lemma tidcat0e t: tidcat enil t = t.
Proof. by elim: t=>//= t ->. Qed.

Lemma tidcatec t0 t1: tidcat t0 (eC t1) = eC (tidcat t0 t1).
Proof. by done. Qed.

Lemma tidcatep t0 t1: tidcat t0 (eP t1) = eP (tidcat t0 t1).
Proof. by done. Qed.

Lemma tidcatce t0 t1: tidcat (eC t0) t1 = tidcat t0 (tidcat (eC enil) t1).
Proof. 
elim: t1 t0=>//t1 IH t0.
+ by rewrite [in y in _=y]tidcatec [in y in _=y]IH tidcat0e !tidcatec IH.
+ by rewrite [in y in _=y]tidcatep [in y in _=y]IH tidcat0e !tidcatep IH.
Qed.

Lemma tidcatpe t0 t1: tidcat (eP t0) t1 = tidcat t0 (tidcat (eP enil) t1).
Proof. 
elim: t1 t0=>//t1 IH t0.
+ by rewrite [in y in _=y]tidcatec [in y in _=y]IH tidcat0e !tidcatec IH.
+ by rewrite [in y in _=y]tidcatep [in y in _=y]IH tidcat0e !tidcatep IH.
Qed.

Lemma tidcatA t0 t1 t2 : tidcat t0 (tidcat t1 t2) = tidcat (tidcat t0 t1) t2.
Proof. 
elim: t1 t0 t2=>//[|e IH|e IH]t0 t2; first by rewrite tidcate0 tidcat0e.
+ by rewrite tidcatec tidcatce [in y in _=y]tidcatce IH.
+ by rewrite tidcatep tidcatpe [in y in _=y]tidcatpe IH.
Qed.


Lemma evol_tidcatS i k: allP k -> evol i (tidcat i k).
Proof. 
elim: k=>//=[_|e IH E]; first by constructor.
by apply: ep; apply:IH.
Qed.



Lemma evol_allP i j: evol i j <-> exists k, allP k /\ j = tidcat i k.
Proof.
split=>[|[k][H]->]; last by apply evol_tidcatS.
elim: j=>/=[|e _|e IH]. 
- by move/evol_enil=>->; exists enil; rewrite tidcate0 //.
+ by move/evol_ec=>->; exists enil; rewrite tidcate0 //.
move/evol_ep=>[->|/IH[k][H]->]; first by exists enil; rewrite tidcate0 //.
by exists (eP k); rewrite /=.
Qed.

Lemma evol_tidcatR i j k: evol i j -> allP k -> evol (tidcat i k) (tidcat j k). 
Proof. 
elim: j i k=>//= [|t IH|t IH] i k; first by move/evol_enil=>->; constructor.
+ by move/evol_ec=>->; constructor.
move/evol_ep=>[->|H H1]; first by constructor.
move:(@IH _ _ H H1)=>/ep; rewrite -tidcatep tidcatpe. 
suff: (eP k) = tidcat (eP enil) k by  move=><-.
by elim: k {IH H} H1=>//= k IH /IH ->.
Qed.

(* from this side, reasoning in terms of suffixes is better *)
Lemma evol_tidcatL i j k: evol j k -> evol (tidcat i j) (tidcat i k). 
Proof. 
by move/evol_allP=>[x][H]->; rewrite evol_allP; exists x; rewrite tidcatA //.
Qed.

(* We do a symmetric closure of evol, to generate a new equality of
 tids modulo evolution *) 
(* Equivalence *) 

Definition eqq (i j : tid) : Prop := evol i j \/ evol j i.

Lemma allp_eqq j k: allP j -> allP k -> eqq k j. 
Proof. 
elim: j k=>//=[k _|j IH k H0]H. 
+by right; rewrite evol_allP; exists k; rewrite tidcat0e //.
case:(IH _ H0 H)=>[/ep |/evol_allP[x][H2]->]{IH H}; first by left.
elim: x j H2 H0=>//[j _ | x IH /= j H0 H1].
+ by left; rewrite tidcate0; apply:ep; constructor.
(* some reasoning about suffixes missing here *)
Admitted.


Lemma eqq_refl: forall j,  eqq j j.
Proof. by move=>j; left; constructor. Qed.

Lemma eqq_sym: forall i j,  eqq i j -> eqq j i.
Proof. by move=> i j; case; [ right | left]. Qed.


Lemma eqq_trans: forall i j k,  eqq i j -> eqq j k -> eqq i k.
Proof. 
move=>i j k [H1|H1]. 
+ case=>[|H2]; first by move/(@e_trans i j k H1); left.
 elim: j H1 H2=>[|j _|j IH] ; first 
            by move/evol_enil=>-> /evol_enil ->; left; constructor.
 - by move/evol_ec=>-> /evol_ec ->; left; constructor.
 move/evol_ep=>[<-|H]; first by right.
 by move/evol_ep=>[->|/(IH H)]//; left; apply: ep.
case=>[/evol_allP [x][H2]->|]; last by move/e_trans/(_ H1); right.
move: H1;case/evol_allP=>[y][H3]->.
by case: (allp_eqq x y H2 H3); [left |right]; apply:evol_tidcatL.
Qed.
(* Clearly, reasoning about suffixes of
  lists is a better idea than baked in tids
*)





(* boolean equivalence for reflection purposes *)


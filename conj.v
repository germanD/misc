Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq.
From FCSL Require Import pred prelude idynamic domain pcm unionmap heap.
From FCSL Require Import coding feap state zigzag world rely inject atomic.
From FCSL Require Import schedule refine hide process always model stsep. 


(* Lets look at the conjunction rule as expressed in the ESOP paper,
     it says: 
     
       {P_1} e {Q_1} {P_2} e {Q_2}
     ----------------------------- 
       {P_1 /\ P_2} e {Q_1 /\ Q_2}
  
  Given the interpretation of ST Types this is an issue, as we have
   two judgements e : STsep (p1,q1) and e : STsep (p2,q2)

We could implement it using a program constructor (conj e)
which takes as a hypothesis the code of e has both specs s1 and s2,
and then show that the code of (conj e) (= code_of e) satisfies the
has_spec predicate for conj_spec. This will be a quirky and deep-ish
embedding of the rule, which would require a program constructor for
the conjunction rule.

We don't want that, we want to implement structural rules as derived
lemmas.

The first derived lemma we build allow us to show that stepping a program 
on an assertion which is a conjunction, can be flipped to the conjunction of 
the verify lemmas.

Where the verify lemma implements the wp inside the definition of the triple.

 *)

Section Floyd.
Variables (W : mod) (A : Type) (e : ST W A).
  
Lemma vrfC i (k1 k2 :cont A) : 
  verify i e k1 -> verify i e k2 ->
     verify i e (fun r m =>  k1 r m /\ k2 r m).
Proof.
move=>E1 E2 P t T ss.
move:(E1 P t T ss)(E2 P t T ss).
elim:ss i t {E1 E2 P T} =>//=.
- move=> i t [W0 H1][_ H2].
 by split=>// s M v T; split; [apply: H1| apply:H2].
move=>s l HI i t [W0] H3 [_] H4; split=>// ss Ms.
case:(H3 ss Ms)(H4 ss Ms)=>TS H1 A1 {H3 H4}[_] H2 A2.
split=>//; first by move=>v T; split; [apply:H1 | apply:H2].
- move=> sf tf TT.
by apply:(HI sf tf);[ apply:A1 =>// | apply:A2=>//].
Qed.

(* we will need then this one for pulling out the binarified
implication, using after lemmas. It is just a wrapper for calls to
vrf_mono, but I just write it to avoid instantiating the goal later *)

Lemma vrfI i (P : Prop) (k :cont A) :
   verify i e k -> verify i e (fun r m => P -> k r m).
Proof. by apply:vrf_mono=>/= y m //. Qed.
       
(* Then we want to implement the rule properly, so we resort to Hoare
weakening, which is implemented using conseq,

Print conseq.

Since a program e cannot have a spec s1 and s2 at the same time via
type ascription, we use hoare weakening to do so.

The spec of e is such that it can be weakened both to s <= (p1,q1),
and s <= (p2,q2), then we can prove using the "do" notation that we
can weaken the spec of e by the conjunction rule:

 {P_1 /\ Q_1} (do e) {P_2 /\ Q2} *)

(* Lift to Conseq, using binary posts *)

Definition conj_spec (s1 s2: spec A) :=
  (fun i => s1.1 i /\ s2.1 i,
          fun i r m => s1.2 i r m /\ s2.2 i r m).

Lemma conseqConj (s1 s2: spec A) :
      conseq e s1 -> conseq e s2 -> conseq e (conj_spec s1 s2).
Proof.
by move=>H1 H2 i [/H1 V1 /H2 V2]; apply:vrfC=>//.
Qed.
End Floyd.

(* However, we do not need the lemma above when verifying a full
client program, because on how FCSL infer specs, and the presence of
the top level Do, what we get is the following proof-outline and the
rule vrfC does suffice. *)

Section ExampleUse.
Variables (W : mod) (A : Type) (e : ST W A).
Variables (p1 p2 : pre) (q1 q2: cont A).

Hypotheses (pf_1: conseq e (binarify p1 q1)) (pf_2: conseq e (binarify p2 q2)).

Definition conj_pre (p1 p2: pre) : pre := fun i => p1 i /\ p2 i.
Definition conj_pos {A} (q1 q2: cont A) : cont A := fun r m => q1 r m /\ q2 r m.

Program Definition my_conj :
  STsep [W] (conj_pre p1 p2, conj_pos q1 q2) := Do e.
Next Obligation.
move=>i/= [P1 P2]; apply:vrfI; apply:vrfC=>//=.
- move:(pf_1 i P1)=>/=; apply:vrf_mono =>// y m /(_ P1)//.
by move:(pf_2 i P2)=>/=; apply:vrf_mono =>// y m /(_ P2)//.
Qed.
End ExampleUse.


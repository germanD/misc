Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq.
From FCSL Require Import pred prelude idynamic domain pcm unionmap heap.
From FCSL Require Import coding feap state zigzag world rely inject atomic.
From FCSL Require Import schedule refine hide process always model stsep lemmas. 

(* A bit of an explanation of how the structural rules of separation logic
 are implemented in FCSL, showcased by one which we haven't implemented 
before, the CONJUNCTION rule, as it is not that useful in a shallow embedding.

Lets look at the conjunction rule as expressed in the ESOP paper: 
     
       {P_1} e {Q_1} {P_2} e {Q_2}
     ----------------------------- 
       {P_1 /\ P_2} e {Q_1 /\ Q_2}
  
In FCSL we implement these structural rules, as opposed to "constructor" rules,
as derived Floyd-style verification lemmas (in lemmas.v and stsep.v)


We don't want this approach, as it would require the programming language to mark, 
we want to implement structural rules as derived lemmas. These are expressed 
in terms of the verify predicate (which implements some sort of wp_calculus).

Print verify.

verify = 
  fun (W : mod) (A : Type) (i : state) (e : ST W A) (r : A -> state -> Prop) =>
   i \In Mod.coh W -> forall t : tree W A, t \In code_of e -> after i t r
 
Here, after entails that al possible executions step i ; t into a m; (Ret v)' state, 
where the unary postcondition ("conts") (s.2 i) holds of v and m. We use the 
verify lemmas to implement three things:

1. The meaning of a triple.

The meaning of the explicit triple type Stbin in model.v is a record packing 
the set of models of a program (T below), and a proof that it "has_spec"

Print has_spec.

has_spec = 
   fun (W : mod) (A : Type) (s : spec A) =>
        [Pred T | forall (i : state) (t : tree W A),
          s.1 i -> i \In Mod.coh W -> t \In T -> after i t (s.2 i)]


2. The weakening between specifications, and the rule of consequence, 
which is a program in FCSL.

Print conseq.

conseq = 
  fun (W : mod) (A : Type) (e : ST W A) (s : spec A) =>
    forall i : state, s.1 i -> verify i e (s.2 i)

The type e : ST W A, is a sigma packs=ing a specification and a 
program which supports it:


Print ST.

Inductive ST W A :=  with_spec : forall s : spec A, STbin W s -> ST W A

Intuitively, this is saying that: given a program e with an implicit, 
and usually inferred by the typechecker, spec s', if we have a state i that
satisfies the stronger pre condition s.1 then we can run all the denotations
in e and, if and when they finish every state satisfies the weaker 
post-condition (s.2 i). 

CLearly, we can use conseq to reflect that a program has its own spec:

conseq_refl  : forall (W : mod) (A : Type) (e : ST W A), conseq e (spec_of e)

However, the main use of conseq is implementing the rule of consequence: 
unlike other traditional Hoare/Separation Logics, here Do is a constructor 
which implements explicit weakeinings:

Check do'.

do' : forall (W : mod) (A : Type) (s2 : spec A) (e : ST W A),
    conseq e s2 -> STbin W (A:=A) s2

That is why whenever we write a program in FCSL it has a top-level do:

Program c : STsep [W] A (p,q) := do e'.

this will generate a conseq statement between the inferred 
specification of the code e' and the specification ascribed by the user.
 
3. We use the verify lemma to implement Floyd-style stepping rules 
to stepwise reduce proof outlines: proof obligations that arise of 
assigning a triple to a program: val_do, step, etc.

Check val_do.
Check step.

4. And finally, we use the verify lemma to implement different derived
lemmas: e.g the frame rule, or rules for pulling nested logical
variables to the top level.

Check frame_do.

Check frame_do4.

The latter frame lemma is the one which corresponds to the rule "on paper", 
which is not necessarily the one you rather use in programs.

*)


Section Floyd.
Variables (W : mod) (A : Type) (e : ST W A).


(* On to the conjunction rule:

The first derived lemma we define enables us to show that stepping a
program on a continuation which is a conjunction, can be flipped to 
proving  the conjunction of the verify lemmas. i.e. our implementation 
of the conjunction rule is a statement that the vrf_predicate commutes 
with the conjunction of post_conditions.

*)
  
Lemma vrfC i (k1 k2 :cont A) : 
  verify i e k1 -> verify i e k2 ->
     verify i e (fun r m =>  k1 r m /\ k2 r m).
Proof.
move=>E1 E2 P t T ss; move:(E1 P t T ss)(E2 P t T ss).
elim:ss i t {E1 E2 P T} =>//=.
- move=> i t [W0 H1][_ H2].
 by split=>// s M v T; split; [apply: H1| apply:H2].
move=>s l HI i t [W0] H3 [_] H4; split=>// ss Ms.
case:(H3 ss Ms)(H4 ss Ms)=>TS H1 A1 {H3 H4}[_] H2 A2.
split=>//; first by move=>v T; split; [apply:H1 | apply:H2].
- move=> sf tf TT.
by apply:(HI sf tf);[ apply:A1 =>// | apply:A2=>//].
Qed.

(* TO DO: Can I refactor the proof using some of the 
  already existing always/after lemmas instead of doing induction on 
  the scheduler ss? *)

(* We will need the following lemma in the example below in order to pull 
out  the binarified implication, using after lemmas. It is just a wrapper 
for a  call to vrf_mono, but I just write it to avoid instantiating 
explicit parameters in the goal later *)

Lemma vrfI i (P : Prop) (k :cont A) :
   verify i e k -> verify i e (fun r m => P -> k r m).
Proof. by apply:vrf_mono=>/= y m //. Qed.
       
(* For completeness, even if it would not be much useful, 
we implement a conseq based lemma which is closer to the statement of
the traditional CONJUNCTION rule.

Since a program e cannot have a spec s1 and s2 at the same time via
type ascription, we use hoare weakening to do so. Then, the spec of e 
is such that it can be weakened both to s <= (p1,q1), and s <= (p2,q2), 
then we can prove using the "do" notation that we can weaken the 
spec of e to the spec in the conjunction rule:

  {Sp} e {Sq}  (Sp,Sq)<= (P1,Q1)  (Sp, Sq) <= (P2,Q2)
----------------------------------------------------------
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

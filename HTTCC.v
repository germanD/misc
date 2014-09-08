(* HTTcc vol 2.0 : now with High Order State *)

(*******************************************************************************
** A toy implementation of HTTcc using Coq 8.5 Universe Polymorphism
** support: 
** 
** This looks promising!
**
** References: software.imdea.org/~germand/HTTcc
**
*******************************************************************************)

Set Universe Polymorphism.
Set Printing All.

(* 
** Some toy state: until we get full ssreflect support and can
** re-implement HTT's heaps
*)

Parameter state : Type -> Type.
(* Some algebra over  state *)

Parameter write: forall W,  W -> state W -> state W.
Parameter read: forall  W, state W -> W.

Axiom read_write : forall W h w,  read W (write W w h) = w.  

Axiom write_write : forall W h w v,  
                      write W w (write W w h) = write W v (write W w h).  

Axiom write_read: forall W h, write W (read W h) h = h.

Parameter safe: forall W, state W -> Prop.

Definition pre W := state W -> Prop.
Definition post W X := X -> state W -> state W -> Prop.
Definition spec W A := (pre W * post W A)%type.


(* A polymorphic HTT + State + Continuation monad *)

Polymorphic 
Definition SK {A X W: Type} 
            (s : spec W A) : Type :=
  forall i: state W, (fst s) i -> 
                  (forall x m, (snd s) x i m -> X) -> X.

Inductive SigSK {A X W : Type } := 
  BigSK {spec_of: spec W A;
         comm: @SK A X W spec_of}.

Polymorphic
Definition Kont {A X W: Type}  (s : spec W A) : Type := 
    forall k, 
      @SK A X W  (fun i => (fst s) i /\ i = k, snd s) -> (fst s) k ->  X.

Arguments Kont {A} X {W} s.
Arguments SigSK A {X W}. 
Arguments SK {A} X {W} s.
Arguments BigSK {A X W spec_of} _. 

Definition verify {A W} (i: state W) (s : spec W A) 
           (r : A -> state W -> Prop) :=
  (fst s) i /\ forall y m, (snd s) y i m -> r y m.

Definition conseq {A W} (s: spec W A) ( p : pre W) (q : post W A) := 
  forall i, p i -> verify i s (fun y m => q y i m).

Local Notation conseq' := 
  (fun W A (s1 s2 : spec W A) => 
     conseq s1 (let (x, _) := s2 in x) 
               (let (_, x) := s2 in x)).

Section Ret.
Variables (X W R :Type) (x:X).

Definition ret_s  : spec W X :=
  (fun _ => True, fun r i m => i = m /\ r = x).

Lemma retQ_refl: forall s,  (snd ret_s) x s s.
Proof. intro; unfold ret_s; simpl; auto. Qed.

Polymorphic 
Definition ret : SK R ret_s :=
  fun s p k => @k x s (retQ_refl s).

End Ret.
Arguments ret {X} W R x i _ _.


Section Bind.
Variables (A B W R: Type).
Variables (s1: spec W A).
Variables (s2 : A -> spec W B).
Variables (e1 : SK R s1) (e2 : forall x, SK R (s2 x)).

Definition bind_pre : pre W := 
  fun i => 
     (fst s1) i /\ forall x m, (snd s1) x i m -> (fst (s2 x)) m.

Definition bind_post : post W B := 
   fun y i m => exists x, exists h, 
     (snd s1) x i h /\ (snd (s2 x)) y h m.

Definition bind_s :spec W B := (bind_pre, bind_post).

Lemma bindP1 h : bind_pre h -> (fst s1) h.
Proof. intro H; case H; auto. Qed. 

Lemma bindP2 i x h : bind_pre i -> (snd s1) x i h -> (fst (s2 x)) h.
Proof. intros P Q; destruct P; apply H0; auto. Qed.
 
Lemma bindQ i x h y m : 
        (snd s1) x i h -> (snd (s2 x)) y h m -> bind_post y i m.
Proof. intros; exists x; exists h; auto. Qed.

Definition bind : SK R bind_s :=
 fun i pf1 k => 
          e1 i (bindP1 i pf1) 
           (fun x h p2 => (e2 x) h (bindP2 i x h pf1 p2) 
           (fun y m p3 => k y m (bindQ i x h y m p2 p3))).
End Bind.
Arguments bind {A B W R s1 s2} e1 e2 _ _ _ .

Section Store.
Variables (X R :Type) (x:X).

Definition write_s : spec X unit :=
  (fun i => safe X i,
            fun r i m => m = write X x i /\ r = tt).

Lemma writeQ s:  (snd write_s) tt s (write X x s).
Proof. unfold write_s; simpl;auto. Qed.

Polymorphic 
Definition store : SK R write_s  :=
  fun s p k => k tt (write X x s) (writeQ s).
End Store.
Arguments store {X} R x _ _ _. 

Section Fetch.
Variables (X R :Type).

Definition read_P : pre X := fun i => exists v j,  
                                        i = write X v j.
Definition read_Q  : post X X :=
  fun r i m =>  forall v j, i = write X v j ->
                  m = i /\ r = v.

Definition read_s := (read_P, read_Q).

Lemma fetchQ s :  read_Q (read X s) s s.
Proof. intros v j H; split ;[|rewrite H ;rewrite (read_write X j)]; auto. Qed.

Polymorphic 
Definition fetch : SK R read_s :=
  fun s p k => k (read X s) s (fetchQ s).
End Fetch.
Arguments fetch {X R} _ _ _.


Section Consequence.
Variables (A W R: Type) (s1 s2: spec W A).
Variables (e1 : SK R s1)  (pf : conseq' W A s1 s2).

Lemma doP i : (fst s2) i -> (fst s1) i.
Proof. simpl; intro; case (pf i H); auto. Qed.

Lemma doQ i : 
       (fst s2) i -> (forall y m, (snd s2) y i m ->  R) ->  R.
Proof.
intros P2 K.
case (pf i P2).
intros P1 H1.
apply (e1 i P1).
intros x m Q1.
exact (K x m (H1 x m Q1)).
Qed.

Polymorphic
Definition Do : SK R s2 :=  doQ.

End Consequence.

Arguments Do {A W R s1 s2} e1 pf _ _ _.


(* Some examples *)


Polymorphic 
Definition rr1 {A: Type}
  := ret A nat (ret A nat 5).

Polymorphic 
Definition st1 {A B : Type} 
            := store A (ret B unit 5). 

Polymorphic
Definition  br1 {X: Type} 
  := bind (store X 4) 
          (fun _ => bind fetch (ret _ _ )).

Polymorphic Definition id {A : Type} (a : A) := a.

(* I can Join rets *)

Definition brr1 {A: Type} := bind (@rr1 A) id.

(* However, I have to explicitly mention the state type here *)





(* I can store a program and then read it *)
Polymorphic 
Definition bsf {A B: Type} := bind (@st1 A B) (fun _ => fetch).

(* 
** Can I flatten it straight away?  
**    join : SK (SK A) -> SK A := fun m => bind m id
**
*)

Fail Polymorphic 
Definition bsf' := 
    bind bsf id.

(* 
** Well, I guess that I  would still need 
**   Sigma types for pulling something like this.
** Or a  proper join. 
*)


Polymorphic 
Definition stC1 {X: Type} 
            := store X (BigSK (@br1 X)). 

Polymorphic 
Definition stC2 {X: Type} 
            :=  bind (@stC1 X) (fun _ => fetch). 

Fail
Polymorphic 
Definition stC3 {X : Type} 
            :=  bind (@stC2 X) (fun p => (comm p)). 
 

(*
The command has indeed failed with message:
=> Error:
In environment
X : Type
p : @SigSK nat X nat
The term "@comm nat X nat p" has type "@SK nat X nat (@spec_of nat X nat p)"
while it is expected to have type "@SK ?112 X (@SigSK nat X nat) (?116 p)"
(cannot unify "state (@SigSK nat X nat)" and "state nat").
*)






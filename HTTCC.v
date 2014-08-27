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

Parameter (state : Type -> Type).

(* Some algebra over  state *)

Definition pre W := state W -> Prop.
Definition post W X := X -> state W -> state W -> Prop.

Parameter write: forall W,  W -> state W -> state W.
Parameter read: forall  W, state W -> W.

Axiom read_write : forall W h w,  read W (write W w h) = w.  

Axiom write_write : forall W h w v,  
                      write W w (write W w h) = write W v (write W w h).  

Axiom write_read: forall W h, write W (read W h) h = h.


(* A polymorphic HTT + State + Continuation monad *)

Polymorphic Definition SK {A X W: Type} 
            (P : pre W) (Q: post W A) : Type :=
  forall s: state W, P s -> 
                  (forall x m, Q x s m -> X) -> X.

Arguments SK {A} X {W} P Q .

Section Ret.
Variables (X W R :Type) (x:X).

Definition ret_P : pre W := fun _ => True.
Definition ret_s  : post W X :=
  fun r i m => i = m /\ r = x.

Lemma retQ_refl: forall s,  ret_s x s s.
Proof. intro; unfold ret_s; auto. Qed.

Polymorphic 
Definition ret : SK R ret_P ret_s :=
  fun s p k => @k x s (retQ_refl s).

End Ret.
Arguments ret {X} W R x s _ _ .


Section Bind.
Variables (A B W R: Type).
Variables (p1: pre W) (q1: post W A).
Variables (p2 : A -> pre W) (q2 : A -> post W B).
Variables (e1 : SK R p1 q1) (e2 : forall x, SK R (p2 x) (q2 x)).

Definition bind_pre : pre W := 
  fun i => 
     p1 i /\ forall x m, q1 x i m -> (p2 x) m.

Definition bind_post : post W B := 
   fun y i m => exists x, exists h, 
     q1 x i h /\ (q2 x) y h m.


Lemma bindP1 h : bind_pre h -> p1 h.
Proof. intro H; case H; auto. Qed. 

Lemma bindP2 i x h : bind_pre i -> q1 x i h -> (p2 x) h.
Proof. intros P Q; destruct P; apply H0; auto. Qed.
 
Lemma bindQ i x h y m : 
        q1 x i h -> (q2 x) y h m -> bind_post y i m.
Proof. intros; exists x; exists h; auto. Qed.

Definition bind : SK R bind_pre bind_post :=
 fun i pf1 k => 
          e1 i (bindP1 i pf1) 
           (fun x h p2 => (e2 x) h (bindP2 i x h pf1 p2) 
           (fun y m p3 => k y m (bindQ i x h y m p2 p3))).
End Bind.
Arguments bind {A B W R p1 q1 p2 q2} e1 e2 _ _ _ .

Section Store.
Variables (X R :Type) (x:X).

Definition write_P : pre X := fun _ => True.
Definition write_Q  : post X unit :=
  fun r i m =>  m = write X x i /\ r = tt.

Lemma writeQ s:  write_Q tt s (write X x s).
Proof. unfold write_Q; auto. Qed.

Polymorphic 
Definition store : SK R write_P write_Q :=
  fun s p k => k tt (write X x s) (writeQ s).
End Store.
Arguments store {X} R x _  _ _. 

Section Fetch.
Variables (X R :Type).

Definition read_P : pre X := fun i => exists v j,  
                                        i = write X v j.
Definition read_Q  : post X X :=
  fun r i m =>  forall v j, i = write X v j ->
                  m = i /\ r = v.

Lemma fetchQ s :  read_Q (read X s) s s.
Proof. intros v j H; split ;[|rewrite H ;rewrite (read_write X j)]; auto. Qed.

Polymorphic 
Definition fetch : SK R read_P read_Q :=
  fun s p k => k (read X s) s (fetchQ s).
End Fetch.
Arguments fetch {X R} _ _ _.


(* Some examples *)


Polymorphic 
Definition rr1 {A: Type}
  := ret A nat (ret A nat 5).

Polymorphic 
Definition st1 {A B : Type} 
            := store A (ret B unit 5). 

Definition  br1 
  := bind (store nat 4) 
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









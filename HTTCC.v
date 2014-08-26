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

(* some toy state: until we get full ssreflect support and can
re-implement HTT's heap *)

Parameter (heap : Type -> Type).

Definition pre W := heap W -> Prop.
Definition post W X := X -> heap W -> heap W -> Prop.

Parameter write: forall W,  W -> heap W -> heap W.
Parameter read: forall  W, heap W -> W.


(* A polymorphic HTT + State + Continuation monad *)

Polymorphic Definition SK {A X W: Type} 
            (P : pre W) (Q: post W A) : Type :=
  forall s: heap W, P s -> 
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

Definition rr1:= ret False nat (ret False nat 5).

(* not-using the heap lets you get away with murder *)

Definition st1:= store nat (ret nat nat 5). 

Definition sst1 := store unit (st1).

Set Printing Universes.

Check st1.

Check sst1.

(*  st1 = 
@store (@SK nat nat N (ret_P N) (ret_s nat N (S (S (S (S (S O))))))) nat
  (@ret nat N nat (S (S (S (S (S O))))))
     : @SK unit nat
         (@SK nat nat N (ret_P N) (ret_s nat N (S (S (S (S (S O)))))))
         (write_P
            (@SK nat nat N (ret_P N) (ret_s nat N (S (S (S (S (S O))))))))
         (write_Q
            (@SK nat nat N (ret_P N) (ret_s nat N (S (S (S (S (S O)))))))
            (@ret nat N nat (S (S (S (S (S O)))))))

st1 is universe polymorphic

*)











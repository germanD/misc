(* Requires Coq 8.5 / trunk *)
Set Universe Polymorphism.
Set Printing All.

Parameter (heap : Type -> Type).

Definition pre W := heap W -> Prop.
Definition post W X := X -> heap W -> heap W -> Prop.

Parameter write: forall W,  W -> heap W -> heap W.
Parameter read: forall  W, heap W -> W.

Polymorphic Definition ST {A X W: Type} 
            (P : pre W) (Q: post W A) : Type :=
  forall s: heap W, P s -> 
                  (forall x m, Q x s m -> X) -> X.


Arguments ST {A} X {W} P Q .

Section Ret.
Variables (X W R :Type) (x:X).

Definition ret_P : pre W := fun _ => True.
Definition ret_s  : post W X :=
  fun r i m => i = m /\ r = x.

Lemma retQ_refl: forall s,  ret_s x s s.
Proof. intro; unfold ret_s; auto. Qed.

Polymorphic 
Definition ret : ST R ret_P ret_s :=
  fun s p k => @k x s (retQ_refl s).

End Ret.

Arguments ret {X} W R x s _ _ .

Parameter (N: Type).

Definition rr1:= ret N nat (ret N nat 5).

Section Store.
Variables (X R :Type) (x:X).

Definition write_P : pre X := fun _ => True.
Definition write_Q  : post X unit :=
  fun r i m =>  m = write X x i /\ r = tt.

Lemma writeQ s:  write_Q tt s (write X x s).
Proof. unfold write_Q; auto. Qed.

Polymorphic 
Definition store : ST R write_P write_Q :=
  fun s p k => k tt (write X x s) (writeQ s).
End Store.

Arguments store {X} R x _  _ _. 

Definition st1:= store nat (ret N nat 5). 

Print st1.

(*  st1 = 
@store (@ST nat nat N (ret_P N) (ret_s nat N (S (S (S (S (S O))))))) nat
  (@ret nat N nat (S (S (S (S (S O))))))
     : @ST unit nat
         (@ST nat nat N (ret_P N) (ret_s nat N (S (S (S (S (S O)))))))
         (write_P
            (@ST nat nat N (ret_P N) (ret_s nat N (S (S (S (S (S O))))))))
         (write_Q
            (@ST nat nat N (ret_P N) (ret_s nat N (S (S (S (S (S O)))))))
            (@ret nat N nat (S (S (S (S (S O)))))))

st1 is universe polymorphic

*)











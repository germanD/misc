(* disc1.v  *)

Require Import List.
Fixpoint g_one (l : nat) : list bool :=
  match l with
  | 0 => nil
  | 1 => true::nil
  | S l' => g_one l' ++ false::nil
  end.

Lemma one_is_one_longer :
  forall (l : nat),
    0 < l -> g_one(S l) = g_one(l) ++ false::nil.
Proof.
  intros.
  simpl.
  apply Lt.lt_0_neq in H.
  destruct l.
  contradiction.
  reflexivity.
Restart.
(* We are smarter than this*)  
 simpl => l; elim l => H ; last first; trivial.
 apply Lt.lt_0_neq in H.
 contradiction.
Qed.

Require Import ssreflect.
Lemma ssr_rules :
  forall (l : nat),
    0 < l -> g_one (S l) = g_one(l) ++ false::nil.
Proof.
by case=>//= /Lt.lt_0_neq //.
Qed.

From mathcomp Require Import ssrbool ssrnat.
(* Adds 0 <> 0 as hint *)
Lemma ssr_rules_overalles :
  forall (l : nat),
    0 < l -> g_one (S l) = g_one(l) ++ false :: nil.
Proof. by case. Qed.

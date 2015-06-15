Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
Require Import pred prelude idynamic ordtype finmap pcm coding unionmap heap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Colored histories over a lists with uniq support *)

Section ColorHistories.
Notation ts := [ordType of nat].
Variable color : eqType.

(* We need to enforce that the timestamps are unique, so we pack *)
(* this unicity requirement in a Sigma Type. *)

Notation keys_of := (map (@fst ts color)).
Notation colors_of := (map (@snd ts color)). 

Structure useq := 
  Undef | Def (usupp : seq (ts * color)) of uniq (keys_of usupp).

(* uniqueness formation lemmas *)
Section FormationLemmas.
  
Lemma uniqts_cons s t c :
  uniq (keys_of s) ->
  t \notin (keys_of s) ->
     uniq (keys_of ((t,c)::s)).
Proof. by rewrite map_cons /= => -> ->  //. Qed.

(* we will add from the tail, so snoc will come handy *)
Lemma uniqts_snoc s t c :
  uniq (keys_of s) ->
  t \notin (keys_of s) ->
     uniq (keys_of (rcons s (t,c))).
Proof. by rewrite map_rcons rcons_uniq /= => -> ->. Qed.

(* cats will come handy *)
Lemma uniqts_cat s1 s2 :
  uniq (keys_of s1) ->
    ~~ has (mem (keys_of s1)) (keys_of s2) ->
      uniq (keys_of s2) ->
          uniq (keys_of (cat s1 s2)).
Proof. by rewrite map_cat cat_uniq => -> -> ->. Qed.

(* and filter for creating projections *)
Lemma uniqts_filter s p:
  uniq (keys_of s) ->
            uniq (keys_of (filter p s)).
Proof. 
elim: s=>// [[t]]c l IH /= /andP [H1]/IH H2.
case: ifP=>//P; rewrite map_cons /= H2 andbT /=.
suff: t \notin [seq i.1 | i <- l] ->
      t \notin [seq i.1 | i <- l & p i] by move/(_ H1).
elim: l {IH H1 H2 c P}=>//= [[t2]]c l IH.
rewrite in_cons; case:norP=>//= [[H1] H2] _.
case:ifP=>// P; last by apply: (IH H2).
rewrite map_cons in_cons /=; case:norP=>// F.
by apply: False_ind; apply: F; split=>//; apply:IH.
Qed.

(* destructors *)

Lemma uniqts_tail s:
  uniq (keys_of s) ->
            uniq (keys_of (behead s)).
Proof. by case: s=>//[[t]c l]/= /andP[_]->. Qed.


(* re painting -- i.e. update -- preserves uniqueness *)
(* Indeed, any transformation that preserves the keys footprint, also
preserves uniqueness *)
Lemma uniqts_update t c s:
  uniq (keys_of s) ->
  uniq (keys_of (map (fun tv => if tv.1 == t
                                     then (tv.1,c)
                                else tv) s)).
Proof.
suff: keys_of s = keys_of (map (fun tv => if tv.1 == t
                                          then (tv.1,c)
                                          else tv) s) by move=>->.
by elim: s=>//[a]l IH /=; rewrite IH; case:eqP=>//.
Qed.

Lemma uniqts_repaint c s:
  uniq (keys_of s) ->
  uniq (keys_of (map (fun tv => (tv.1, c)) s)).
Proof.
suff: keys_of s = keys_of (map (fun tv => (tv.1, c)) s) by move=>->.
by elim: s=>//=[a]l ->.
Qed.

End FormationLemmas.

Implicit Types (t : ts) (c : color) (s r : useq).

Lemma useqE s r : 
        s = r <-> match s, r with
                     Def s' pfs, Def r' pfr => s' = r'
                  | Undef, Undef => true
                  | _, _ => false
                  end.
Proof.
split; first by move=>->; case: r.
case: s; case: r=>// s pfs r pfr E; rewrite {r}E in pfr *.
by congr Def; apply: bool_irrelevance.
Qed.

(* When in a hurry, taken the lift *)
Definition ulift {B: Type} x f s : B :=
  if s is Def ss pf then (f ss pf) else x.

Definition suppU s := ulift [::] (fun ss _ => ss) s.

Definition domU s := ulift [::] (fun ss _=> keys_of ss) s.

Definition validU s := if s is Def _ _ then true else false.

Definition emptyU := @Def [::] is_true_true.


(* Lifting list operations to our unique lists *) 
Definition ucons t c s :=
  if s is (Def s' pfs) then
  if decP (@idP (t \notin (keys_of s'))) is left pft then 
      Def (uniqts_cons c pfs pft)
    else Undef
  else Undef.

Definition usnoc s t c  :=
  if s is (Def s' pfs) then
  if decP (@idP (t \notin (keys_of s'))) is left pft then 
      Def (uniqts_snoc c pfs pft)
    else Undef
  else Undef.


Definition utail s := ulift Undef (fun _ pf=> Def (uniqts_tail pf)) s.  


Definition ucat s1 s2 := 
  if (s1, s2) is (Def ss1 pf1, Def ss2 pf2) then  
    if decP (@idP (~~ has (mem (keys_of ss1))
                      (keys_of ss2))) is left pfU then 
      Def (uniqts_cat pf1 pfU pf2)
    else Undef
  else Undef.

Definition ufilter p s := ulift Undef (fun _ pf =>  Def (uniqts_filter p pf)) s.

Definition uall p s := ulift false (fun ss _ => all p ss) s.

(* For the coloring invariants, I need the infrastructure to reproduce
the +,? patterns *)

(* The C+ = at least one C-colored *)
Definition umany p s :=
  ulift false (fun ss _ => if ss is tc :: sss
                           then p tc && all p sss
                           else false) s.


(* The C? = at most one C-colored is just implemented by pattern
matching *)

Definition uone p s :=
  if s is Def ss _ then
    match ss with
      | [::] => true
      | [:: tc ] => p tc
      | _ :: sss => false
    end
  else false.
                
(* looukup / last *)

Definition ulast s := ulift 0 (fun ss  _ => last 0 (keys_of ss)) s.

Definition ufind t s :=
  if s is Def ss _ then
    let i:= index t (keys_of ss)
    in if (drop i ss) is tc :: _ then Some (tc).2 else None 
  else None.                                    

(* need a find_spec to reason about found items? *)

(* surgery infrastrucrture for re-ordering tokens *)

Definition uupd t c s :=
  ulift Undef (fun _ pf => Def (uniqts_update t c pf)) s.

(* constant update--repainting-- all entries *)
Definition repaint c s:=
   ulift Undef (fun _ pf => Def (uniqts_repaint c pf)) s.


(*forwards induction on undef, empty and cons *)
Lemma u_ind (P : useq -> Prop): 
        P Undef ->
        P emptyU ->
        (forall t c s, t \notin (domU s) -> P s -> P (ucons t c s)) ->
        forall s, P s.
Proof.
move=> H0 H1 IHH; case=>//;elim=>//.
+ by move=>// H; rewrite (_: Def H = emptyU) // useqE //.
move=>[t]c l IH /= H; case: (andP H)=> T U.
move:(IH U)=> /(IHH t c) /= /(_ T) //;case:decP=>//= H4.
suff:  H = uniqts_cons c U H4 by move=>->.
by apply: bool_irrelevance.
Qed.

(* snoc induction for snoc properties *)
Lemma u_sind (P : useq -> Prop): 
        P Undef ->
        P emptyU ->
        (forall t c s, t \notin (domU s) -> P s -> P (usnoc s t c)) ->
        forall s, P s.
Proof.
move=> H0 H1 IHH; case=>//;elim/last_ind=>//[Hs|ss [t c] IH Hs].
+ by rewrite (_: Def Hs = emptyU) // useqE //.
have U: uniq [seq i.1 | i <- ss] by
  rewrite map_rcons rcons_uniq /= in Hs; case/andP:Hs.
have T: t \notin [seq i.1 | i <- ss] by
  rewrite map_rcons rcons_uniq /= in Hs; case/andP:Hs.
move:(IH U)=>/(IHH t c) /= /(_ T); case:decP=>// H.
suff: Hs = uniqts_snoc c U H by move=>->.
by apply: bool_irrelevance.
Qed.


Section VDTLemmas.

Lemma valid_ucons t c s: validU (ucons t c s) <-> validU s /\ t \notin (domU s).
Proof.
by split=>//; [case: s=>//= ss H | case: s=>[|ss h][Vs]H//=]; case:decP=>//.
Qed.

Lemma valid_usnoc s t c: validU (usnoc s t c) <-> validU s /\ t \notin (domU s).
Proof.
by split=>//; [case: s=>//= ss H | case: s=>[|ss h][Vs]H//=]; case:decP=>//.
Qed.

Lemma valid_ucat r s:
  validU (ucat r s) <->
    [/\ validU r, validU s & ~~ has (mem (domU r)) (domU s)].
Proof.
split=>//[|[vR] vS H0].
+ by case: r=>// r Hr; case: s=>//s Hs; rewrite /ucat=>//= ;case:decP=>//-> _.
case: r vR H0=>// rs HR vR; case: s vS=>//= ss HS vS H0.
by rewrite /ucat; case:decP=>//.
Qed.

Lemma valid_ufilter p s: validU s <-> validU (ufilter p s).
Proof. by case:s=>//. Qed.

Lemma valid_uupd t c s:  validU s <-> validU (uupd t c s).
Proof. by case:s=>//. Qed.

Lemma umany_valid p s: umany p s -> validU s.
Proof. by case: s=>//. Qed.

Lemma uall_valid p s: uall p s -> validU s.
Proof. by case: s=>//. Qed.

Lemma dom_validU t s: t \in domU s -> validU s.
Proof. by case: s=>//. Qed.

Lemma dom_suppU  t s: t \in domU s -> exists c, (t, c) \in suppU s.
Proof.
elim/u_ind:s=>//z c ss Z IH //=.
case: ss Z IH=>// ss Hs /= Z IH; case:decP=>//= H.
rewrite in_cons;case/orP=>[/eqP ->|/IH [c2]T].
+ by exists c; rewrite inE; case:eqP=>//.
by exists c2; rewrite inE T orbT.
Qed.                                    

Lemma dom_uupd t x s: domU (uupd t x s) = domU s.
Proof.
elim/u_ind: s=>//= z c [|ss HS]//= Z.
by case: decP=>//= H ->; case:eqP=>//.
Qed.

Lemma supp_ucons tc t x s:
  tc \in suppU (ucons t x s) = validU (ucons t x s)  &&
                                      ((tc == (t,x)) || (tc \in (suppU s))).
Proof. by case:s=>//= ss Hs; case:decP=>//. Qed.

Lemma supp_ufilter p s tc:
  tc \in suppU (ufilter p s) = validU s && p tc && (tc \in suppU s). 
Proof.  by case: s=>//= ss Hs; rewrite mem_filter. Qed.

Lemma in_ufilter_in_dom t p s: t \in domU (ufilter p s) -> t \in domU s.  
Proof.
case: s=>//; elim=>//= [[t1]]c ss IH /andP /= [T1] /IH {IH}IH.
by case:ifP=>//= P; rewrite !in_cons; case:eqP=>//.    
Qed.

Lemma valid_dom_ucons t c s:
    validU (ucons t c s) -> domU (ucons t c s) = t :: domU s.
Proof. by case: s=>//=rs rH; case: decP=>//. Qed.                   

Lemma valid_dom_usnoc s t c:
    validU (usnoc s t c) -> domU (usnoc s t c) = rcons (domU s) t.
Proof. by case: s=>//=rs rH; case: decP=>//= H _; rewrite map_rcons. Qed.

Lemma valid_dom_ucat r s:
    validU (ucat r s) -> domU (ucat r s) = domU r ++ domU s.
Proof.
case: r=>//;case: s=>//=rs rH ss sH /valid_ucat /= [vR] vS H.
by rewrite /ucat; case:decP=>//= HH; rewrite map_cat.
Qed.                   

Lemma notin_dom_ucatS t r s:
  validU (ucat r s) ->
  t \notin domU (ucat r s) -> t \notin domU (ucat s r).
Proof.
case: s=>//; case: r=>//= ss Hs rr Hr.
rewrite /ucat /=; case:decP=>//= => _ _; case:decP=>//= _.
by rewrite !map_cat !mem_cat orbC.
Qed.

Lemma notin_dom_ucat t r s:
  validU (ucat r s) ->
  t \notin domU (ucat r s) -> t \notin domU r /\ t \notin domU s.
Proof.
case: s=>//; case: r=>//= ss Hs rr Hr.
rewrite /ucat /=; case:decP=>//= => _ _.
by rewrite map_cat mem_cat;case/norP.
Qed.

(* I'm not using this version *)
(* Lemma notin_dom_ucatW t r s: *)
(*   validU (ucat r s) -> *)
(*   t \notin domU (ucat r s) -> t \notin domU s. *)
(* Proof. by move/notin_dom_ucat=>H1; case/H1. Qed. *)

End VDTLemmas.


Section UcatLemmas.

Lemma ucatUs s: ucat Undef s = Undef.
Proof. by done. Qed.

Lemma ucatsU s: ucat s Undef = Undef.
Proof. by case:s. Qed.

Lemma ucat0s s : ucat emptyU s = s.
Proof.
case: s=>//ls H; rewrite /emptyU /ucat //= useqE; case:decP =>// H2.
suff: ~~ has (mem [seq i.1 | i <- [::]]) [seq i.1 | i <- ls]
      by   move/(_ color); move=>/H2.
by move=> T; elim: ls H {H2}=>//= ts ls IH /andP[_] /IH.
Qed.

Lemma ucats0 s : ucat s emptyU = s.
Proof. by case: s=>//ls H; rewrite /emptyU /ucat //= useqE cats0. Qed.

Lemma ucats1 s t c :
    ucat s (ucons t c emptyU) = usnoc s t c.
Proof.
case: s=>//= ls H.
rewrite /ucat //=; case: decP=>//H0; case: decP=>//H1.
+ by rewrite useqE cats1.
+ by case: (norP H0)=> /H1.
by apply:False_ind; apply: H0; rewrite orbF H1.
Qed.  

Lemma ucat1s s t c :
    ucat (ucons t c emptyU) s = ucons t c s.
Proof.
case: s=>//= ls H.
rewrite /ucat //=; case: decP=>//H0; case: decP=>//H1; first by rewrite useqE.
+ by apply:False_ind; apply: H1; rewrite has_sym has_seq1 in H0; rewrite H0.
by apply:False_ind; apply: H0; rewrite has_sym has_seq1 H1.
Qed.  

(* To Do: Prove boring ucat_ucons, ucat_usnoc, ucons_ucat, ucat_usnoc *)

Lemma ucons_ucat t c r s : ucons t c (ucat r s) = ucat (ucons t c r) s.
Proof.
Admitted.  

Lemma ucat_ucons t c r s: ucat (ucons t c r) s = ucons t c (ucat r s).
Proof.
Admitted.

Lemma ucat_usnoc t c r s : ucat (usnoc r t c) s = ucat r (ucons t c s).
Proof.
Admitted.  

Lemma usnoc_ucat r s t c: usnoc (ucat r s) t c = ucat r (usnoc s t c).
Proof.
Admitted.

Lemma ucatA r s q : ucat r (ucat s q) = ucat (ucat r s) q.
Proof.
case: r;case:s=>//rs rH ss sH; case: q=>//=[|qs qH];
  rewrite /ucat //=; case:decP=>// H.
+ case:decP=>//H0; case:decP=>//H1.
 - case:decP=>//=H2; first by rewrite useqE catA.
  apply: False_ind;rewrite has_sym !map_cat !has_cat !negb_or in H2 H0.
  apply: H2; case/andP: H0=>_ H2.
  by rewrite has_sym in H H2; rewrite H has_sym H2.
 * apply: False_ind;rewrite !map_cat !has_cat !negb_or in H0.
  by apply: H1; case/andP: H0=>-> _.
 case:decP=>//H2;apply: False_ind; apply: H0; rewrite has_sym in H2.
 move: H2; rewrite !map_cat !has_cat !negb_or H1 andTb; case/andP.
 by rewrite has_sym.
case: decP=>//H0; case:decP=>//H1; apply:False_ind; apply: H.
rewrite has_sym map_cat has_cat negb_or in H1.
by case/andP: H1=>_ ;rewrite has_sym.
Qed.

End UcatLemmas.

Section UfindLemmas.
 
Lemma ufind_some t c s: ufind t s = Some c -> t \in domU s.
Proof.
Admitted.

Lemma ufind_none t c s: ufind t s = None <-> t \notin domU s.
Proof.
Admitted.

Lemma ufind_ucat_dom t c r s:
  ufind t (ucat r s) = Some c -> t \in domU r \/ t \in domU s.
Proof.
move/ufind_some=>D; move: (dom_validU D)=>V.
by move: D; rewrite valid_dom_ucat // mem_cat; case/orP; [left|right].
Qed.

Lemma ufind_ucatS t r s: ufind t (ucat r s) = ufind t (ucat s r).
Proof.
Admitted.

Lemma ufind_ucatW t r s:  t \in domU r -> ufind t (ucat r s) = ufind t r.
Proof.
Admitted.

Lemma ufind_ufilter t p s: ufind t (ufilter p s) = ufind t s.
Admitted.

End UfindLemmas.
  
Section FilteringLemmas.
  
Lemma ufilter_ucons p t c s :
  t \notin (domU s) ->
   ufilter p (ucons t c s) = if p (t,c) then ucons t c (ufilter p s)
                             else ufilter p s.
Proof.
case: s=>//=[|ss Hs]; case:ifP=>//; case:decP=>//= H; last first.
+ by rewrite useqE; case:ifP=>//.
case:decP=>//=H2; rewrite useqE /=; first by case:ifP=>//.
move=> H3; apply:False_ind.
suff: t \notin [seq i.1 | i <- ss & p i] by case/H2.
elim: ss {c H2 Hs H3} H=>//= [[r]]x ss IH /=.
rewrite in_cons negb_or=>/andP=>[[T]] /IH H.
by case: ifP=>//P; rewrite in_cons negb_or T H //.
Qed.

Lemma ufilter_usnoc p s t c :
  t \notin (domU s) ->  
  ufilter p (usnoc s t c) = if p (t,c) then usnoc (ufilter p s) t c
                            else ufilter p s.
Proof.
Admitted.

Lemma ufilter_ucat p r s:
  ufilter p (ucat r s) = ucat (ufilter p r) (ufilter p s).
Proof.
(* should be trivial, or easy at least *)
Admitted.

Lemma ufilter_id p s :
  ufilter p (ufilter p s) = ufilter p s.
Proof. by case: s=>//= ss /= Hs; rewrite useqE filter_id. Qed.

End FilteringLemmas.

Section AMULemmas.
Lemma umany_uall p s: umany p s -> uall p s.
Proof. by case: s=>//=[[|tc s]//]. Qed.

Lemma uall_empty p: uall p emptyU.
Proof. by []. Qed.

Lemma uoneE p s:
  uone p s <-> s = emptyU \/ exists t v, s = ucons t v emptyU /\ p (t,v).
Proof. split=>//.
+ case: s=>//= [[|[t]v ss]]/=; first by left; rewrite useqE //.
 case: ss=>//= H P; right; exists t, v; rewrite useqE P //.
by case=>[->|[t][v][->]P]//.
Qed.

Lemma umany_ucons p t c s:
 t \notin (domU s) -> uall p s -> p (t,c) -> umany p (ucons t c s).
Proof.
case: s=>//[[|tc ss Hs H]/=]; first by rewrite andbT.
by case/andP=> P1 A P2; case: decP=>//= _; rewrite P1 P2 A //.
Qed.

Lemma umany_usnoc p t c s:
  t \notin (domU s) -> uall p s -> p (t,c) -> umany p (usnoc s t c).
Proof.
Admitted.

(* Would this alternative be any better? *)
Lemma umany_ucons_t p t c s:
  t \notin (domU s) -> umany p (ucons t c s) = uall p s && p (t,c).
Proof.
by case: s=>//= [[|tc ss]]// Hs T ; case:decP=>//=H; rewrite ?andbT // andbC.
Qed.

Lemma uall_ucons p t c s:
  t \notin (domU s) -> uall p s -> p (t,c) -> uall p (ucons t c s).
Proof.
by case: s=>//= ss Hs T U P; rewrite /uall; case:decP=>//= _; rewrite P U //.
Qed.

Lemma uall_usnoc p t c s:
  t \notin (domU s) -> uall p s -> p (t,c) -> uall p (usnoc s t c).
Proof.
case: s=>//= ss Hs T U P; rewrite /uall; case:decP=>//= _.
by rewrite all_rcons P U //.
Qed.

Lemma uall_ucat p r s:
 ~~ has (mem (domU r)) (domU s) -> uall p (ucat r s) = uall p r && uall p s.
Proof.
case: r=>// rs Hr; case: s=>//=[| ss Hs]; first by rewrite andbF.
by rewrite /ucat; case:decP=>//= H; first by  rewrite all_cat.
Qed.

Lemma ucat_2_umany p r s :
 ~~ has (mem (domU r)) (domU s) -> umany p r -> umany p s -> umany p (ucat r s).
Proof.
case: r=>//[[|tr rr]]/= Hr;
 case: s=>//[[|ts ss]]// Hs H /andP [PR] R /andP [PS]S //=.
rewrite /umany /ucat; case:decP=>//H1 /=.
by rewrite all_cat /= R PR S PS//.
Qed.                                                    

(* Lemma umany_ucons2 p t c s: *)
(*   (t \notin (domU s)) && uall p s && p (t,c) =  umany p (ucons t c s). *)
(* case: s t=>//; elim=> [|/= tc ss IH ]//= Hs t; first by rewrite andbT. *)
(* case:decP=>//= H; first by rewrite H andTb andbC. *)
(* apply: False_ind; apply: H; rewrite in_cons negb_or. *)
(* (*!! *) *)
(* Abort. *)

Lemma umany_NE p s:
  umany p s ->
  exists t, exists c, exists ss,
      [/\ p (t,c), t \notin (domU ss), uall p ss & s = ucons t c ss].
Proof.
case: s=>//;case=>//=[[t]]c s Hs /andP [P] H2.
have T0: t \notin [seq i.1 | i <- s] by case/andP: Hs.
have H0: uniq [seq i.1 | i <- s] by case/andP: Hs.
exists t; exists c; exists (Def H0).
by rewrite P //=; split=>//; case:decP=>//H; rewrite useqE.
Qed.
End AMULemmas.


Section UpdateLemmas.

Lemma uupd_empty t x: uupd t x (emptyU) = emptyU.
Proof. rewrite useqE //. Qed.

Lemma uupd_ucons t x z c s:
  uupd t x (ucons z c s) = if (t == z) then ucons t x s
                           else ucons z c (uupd t x s).
Proof. 
elim/u_ind: s=>[||r v ss]; first by case:eqP=>//.
+ by case:eqP=>//=[->|P]; rewrite useqE; case:eqP=>// /esym/P //.
case: ss=>//= ss Hs Z;case: eqP=>//[->|P]; rewrite /uupd //=; case:decP=>//=H1.
+ case:decP=>//= H3; case:decP=>//=  H4; rewrite !useqE; case:eqP=>// _.
 by case=>->; case:eqP=>// /esym E; case/norP:H4; case:eqP=>//.
+ case:decP=>//= H2; case:decP=>//= H3; rewrite !useqE //=.
 case:eqP H2=>//_; case:eqP=>//[-> /H1 //|E].
 by case/norP: H3=>_ ;case/H1.
+ case:decP=>//= H2;case:decP=>//= H3; rewrite useqE.
 case:eqP=>[/esym/P//|_]_; case:decP=>//=H4; rewrite useqE; last first.
 - case:decP=>//=; rewrite negb_or H2 andbT //==> T.
  apply:False_ind; apply: H4; rewrite negb_or H1.
  by move: T; case:ifP=>//= _ ->//. 
 case:decP=>// H5; first by case:eqP=>[/esym/P//|E]//.
 case/norP: H4=> R _; apply:False_ind; apply:H5.
 by case:ifP=>//= _;  rewrite negb_or R H2 //.
case: decP=>//= H2 _; case:decP=>//=H3; case:decP=>//= H4.
+ by apply:False_ind; apply:H1; case/norP:H4=>_ ->.
by case:decP=>//= H6; apply:False_ind; apply: H2; case/norP: H6=> H7 ->.
Qed.  
(* This was an awful proof, I might just missed sth *)

(* I'm enuntiating the usual lemmas for completeness, will prove them if needed *)
Lemma uupd_usnoc t x s z c:
  uupd t x (usnoc s z c) = if (t == z) then usnoc s t x
                           else usnoc (uupd t x s) z c.
Proof.
Admitted.

(* I will need the following ones for civ_uupd*)
Lemma uupd_id t c s:  t \notin (domU s) -> uupd t c s = s.
Proof.
elim/u_ind: s=>//[|r v [/=|ss H]  Hs IH]; rewrite useqE // uupd_ucons.
(* TO FINISH *)
Admitted.

Lemma uupd_ucat t x r s:
  uupd t x (ucat r s) = ucat (uupd t x r) (uupd t x s).
Proof.
Admitted.

(* the following is not valid *)
(* Lemma ufilter_upd p t c s: *)
(*   ufilter p (uupd t c s) = if p (t, c) then uupd t c (ufilter p s) *)
(*                            else ufilter p s. *)
(* Proof. *)
(* elim/u_ind:s=>//=; try by case: ifP=>//P; rewrite useqE. *)
(* move=> z r ss T; case:ifP=>// Pt IH; *)
(*  rewrite ufilter_ucons // !uupd_ucons; case:eqP Pt=>[->|E]//Pt; *)
(*   rewrite ufilter_ucons // ?dom_uupd ?T//. *)

(* + case:ifP Pt=>//Pt; case:ifP=>//Pz. rewrite uupd_ucons; case:eqP=>//. *)
(*  by case:ifP Pz=>//; rewrite IH. *)
(* - rewrite !uupd_ucons; case:eqP Pt=>[->|E]//Pt. *)

End UpdateLemmas.

Section PaintingLemmas.

Lemma  repaint_R: forall c (rs: seq (ts * color)),
    [seq i.1 | i <- [seq (tv.1, c) | tv <- rs]] = [seq i.1 | i <- rs].
Proof.  by move=> c; elim=>//= a rl ->. Qed.
  
Lemma dom_repaint c s: domU s = domU (repaint c s).
Proof. by case: s=>//s i /=; rewrite repaint_R. Qed.

Lemma repaint_empty c: repaint c (emptyU) = emptyU.
Proof. by rewrite useqE //. Qed.

Lemma repaint_valid c s: validU s -> validU (repaint c s).
Proof. by case: s=>//. Qed.

Lemma repaint_ucons c t x s:
    repaint c (ucons t x s) = ucons t c (repaint c s).
Proof.  
case:s=>//= ss sH.
case: decP=>//= H; case:decP=>//= J; first (by rewrite useqE); apply: False_ind.
+ by apply: J; rewrite repaint_R H. 
by apply: H; rewrite repaint_R in J.  
Qed.

Lemma repaint_usnoc c t x s:
    repaint c (usnoc s t x) = usnoc (repaint c s) t c.
Proof.  
case:s=>//= ss sH.
case: decP=>//= H; case:decP=>//= J; first by rewrite useqE map_rcons //.
+ by apply: False_ind; apply: J; rewrite repaint_R H. 
by apply: False_ind; apply: H; rewrite repaint_R in J. 
Qed.

(* repaint is and homomorphism *)  
Lemma repaint_ucat c r s:
    repaint c (ucat r s) = ucat (repaint c r) (repaint c s).
Proof.
elim/u_ind: r s=>//[|t x rs T IH] s; first by rewrite repaint_empty !ucat0s.
by rewrite ucat_ucons !repaint_ucons ucat_ucons IH.
Qed.

Lemma repaint_uall c s:
  validU s -> uall (fun tc => tc.2 == c) (repaint c s).
Proof.
by case: s=>//; elim=>//= tc ss IH /andP [_] H /(IH H) ->; rewrite andbT //.  
Qed.

Lemma repaint_repaint c1 c2 s:
    repaint c1 (repaint c2 s) = (repaint c1 s).
Proof.  
elim/u_ind: s=>//[|t c s T IH]; first by rewrite repaint_empty.
by rewrite !repaint_ucons IH.  
Qed.
End PaintingLemmas. 
End ColorHistories.

Notation "s1 '+++' s2" :=
  (ucat s1 s2) (at level 31, right associativity).

Notation "t '-:>' c ':::'  s" :=
  (ucons t c s) (at level 30, right associativity).

(* This notation is clashing with some other, will figure out later *)
(* Notation "'[::: ' t '-:>' c ]'" := *)
(*   (ucons t c emptyU) (at level 30). *)


(* Here we instantiate the colors w/ the three colors proposed for the
Jayanti snapshot concurroid, and define the coloring invariant of the
joint history *)

Structure jayantiT := JayantiT {
  label_of : nat;
  eset_of : encoded_set;
  x_of : ptr; 
  y_of : ptr;
  fx_of : ptr; 
  fy_of : ptr;
  s_of : ptr}.


Section JayantiHistories.
Variable jT : jayantiT.
Notation ts := [ordType of nat].
Notation A := (eset_of jT).
Notation x := (x_of jT).
Notation y := (y_of jT).

Inductive color  :=  red | green | yellow.

Section color_Eq.
Definition eqdc c1 c2  :=
  match c1, c2 with
  | red, red => true
  | green, green => true
  | yellow, yellow => true 
  | _, _ => false
  end.

Lemma eqdcP : Equality.axiom eqdc.
Proof. by do 2 case=>//; constructor=>//. Qed.

Canonical color_eqMixin := EqMixin eqdcP.
Canonical color_eqType := Eval hnf in EqType (color) color_eqMixin.

Lemma eqdcE : eqdc = eq_op.
Proof. by []. Qed.
End color_Eq.



Notation unil := (emptyU color_eqType).

Implicit Type h : hist [encoded_set of ptr * A].
Implicit Type s : useq (color_eqType).

Section ColorPreds. 

Definition green_plus s :=
    umany (fun tc=> tc.2 == green) s. 

Definition yellow_zo s :=
    uone (fun tc=> tc.2 == yellow) s.

Definition red_star s :=
    uall (fun tc=> tc.2 == red) s. 

Lemma green_valid s: green_plus s -> validU s.
Proof. by case:s. Qed.

Lemma red_valid s: red_star s -> validU s.
Proof. by case:s. Qed.

Lemma yellow_valid s: yellow_zo s -> validU s.
Proof. by case:s. Qed.

(* Some reasoning about colored fragments *)
Lemma green_dom t s:
  green_plus s -> t \in domU s -> ufind t s = Some green. 
Proof.
Admitted. 

Lemma red_dom t s:
  red_star s -> t \in domU s -> ufind t s = Some red. 
Admitted.

Lemma yellow_dom t s:
  yellow_zo s -> t \in domU s -> s = t -:>yellow ::: unil. 
Proof.
by case/uoneE=>/=[->//|[t1][v][->]]/eqP/=-> /orP[/eqP->|//]; rewrite useqE//.
Qed.
End ColorPreds.
Notation paint_green s := (repaint green s).

Section ColorInvariant.

(* I'm removing valid from the invariant, as it will be repeted elsewhere *)
Definition color_inv s :=
  exists gs ys rs, [/\ green_plus gs , yellow_zo ys , red_star rs,
                       s  = gs +++ ys +++ rs  &
                         validU (gs +++ ys +++ rs)].

(* Inv s => validU s lemmas *)

Lemma color_inv_valid s: color_inv s -> validU s.
Proof. by case=>gs[ys][rs][G]Y R ->. Qed.




Notation green_red r s :=
  ([/\ validU (r +++ s), green_plus r & red_star s]).

Notation green_yellow r s :=
  ([/\ validU (r +++ s), green_plus r & yellow_zo s]).

Notation yellow_red r s :=
  ([/\ validU (r +++ s), yellow_zo r & red_star s]).


(* Inv construction lemmas:  *)

(* Greens are good*)  
Lemma some_green_inv s :  green_plus s -> color_inv s. 
Proof.
by move=> S; exists s, unil, unil; rewrite !ucats0 /= green_valid S //.
Qed.

(* Green and at most one yellow, too *)
Lemma green_yellow_inv g y:
   green_yellow g y -> color_inv (g +++ y). 
Proof. by case=>//vG G Y; exists g, y, unil; rewrite ucats0 Y G vG //. Qed.

(* Or we can have a red and green and paste it together *)
Lemma green_red_inv g r:
   green_red g r -> color_inv (g +++ r). 
Proof. by case=>//vG G R; exists g, unil, r; rewrite ucat0s R G vG //. Qed.

(* A yellow item can be snoc'd after a green history *)
Lemma green_snocy_inv s t:
   green_plus s -> t \notin domU s -> color_inv (usnoc s t yellow). 
Proof.
move=> G T; rewrite -ucats1; apply: green_yellow_inv.
by rewrite G ucats1; split=>//; apply/valid_usnoc; rewrite T green_valid //.
Qed.


(* Inductive forward reasoning with a well-colored s*)

(*I can add one red on the right *)
Lemma snoc_red_inv s t:
  t \notin (domU s) -> color_inv s -> color_inv (usnoc s t red).  
Proof.
move=> T [gs][ys][rs][G]Y R S vS; rewrite S in vS T *.
exists gs, ys, (usnoc rs t red).
have RS: red_star (usnoc rs t red).
+ rewrite /red_star; rewrite ucatA in vS T; apply: (uall_usnoc)=>//. 
  by case/(notin_dom_ucat vS): T=>_.
rewrite Y G RS  [in y in _=y]ucatA ucatA usnoc_ucat //.
split=>//;rewrite ucatA -usnoc_ucat.
by apply/valid_usnoc; rewrite -ucatA T vS.
Qed.


(* I can add green on the left to a valid invariant*)
Lemma cons_green_inv s t:
  t \notin (domU s) -> color_inv s -> color_inv (t -:> green ::: s).  
Proof.
move=> T [gs][ys][rs][G] Y R S vS.
rewrite S in T vS * ;exists (t -:> green ::: gs), ys, rs.
have GS: green_plus (ucons t green gs).
+ case/(notin_dom_ucat vS): T=> T _ ; rewrite /green_plus /= in G *.
 by apply: (umany_ucons T)=>//; apply:umany_uall. 
by rewrite GS Y R ucat_ucons //; split=>//; apply/valid_ucons.
Qed.


(* Well, that's  just one, I can add umany green on the left *)
Lemma ucat_green_inv l r:
  green_plus l -> color_inv r ->
     validU (l +++ r) -> color_inv (l +++ r).
Proof.
move=> L [gs][ys][rs][G] Y R -> vR; rewrite ucatA=> V.
exists (l +++ gs),ys,rs; rewrite Y R; split=>//.
case/valid_ucat: V=> /valid_ucat [_] _ H _ _.
by apply: ucat_2_umany=>//.
Qed.

(* Or many red on the right *)
Lemma ucat_inv_red l r:
  color_inv l -> red_star r -> 
     validU (l +++ r) -> color_inv (l +++ r).
Proof.
move=> [gs][ys][rs][G] Y R -> vR RR; rewrite -!ucatA=> V.
exists gs,ys, (rs +++ r); rewrite G Y V //.
rewrite /red_star in R RR *; rewrite uall_ucat ?R ?RR //.
by rewrite ucatA in V; case/valid_ucat: V=>_ /valid_ucat=>[[_]]_ ->//.
Qed.

(* But, I could also cons a green to a RS to make it valid*)
Lemma cons_green_rs_inv r s t:
  t \notin (domU (r +++ s)) ->
      yellow_red r s -> color_inv (t -:> green ::: (r +++ s)).  
Proof.
move=> T[vRS]Y R; exists (t -:> green ::: unil), r, s.
by rewrite Y R // ucat1s; split=>//; apply/valid_ucons; rewrite vRS T.
Qed.

(* Or, If I have a GR, I can put one yellow in the middle *)  
Lemma insert_yellow_inv g r t:
   green_red g r ->
     t \notin (domU (g +++ r)) ->
        color_inv (g +++  t -:> yellow ::: r).
Proof.  
case=> V G R /(notin_dom_ucat V) [gT] rT; case/valid_ucat: (V)=> vG vR H.
exists g, (ucons t yellow unil), r; rewrite ucat1s G R /=; split=>//.
have vT: validU ( t -:> yellow ::: r) by apply/valid_ucons; split=>//.
+ by apply/valid_ucat; rewrite vG vT valid_dom_ucons //= negb_or gT H.
Qed.


(* Can I reason backwards with color_inv ? *)


(* Now for something different, I can repaint a valid history green *)
(* This requires some "stating the obvious" lemmas *)

Lemma green_plus_paint_green s:
   green_plus s -> green_plus (paint_green s).
Proof. 
case/umany_NE=>[t][c][ss][/= /eqP ->]T /uall_valid /(repaint_uall green) S ->.
rewrite repaint_ucons; apply: umany_ucons=>//.
by rewrite -(dom_repaint green).                    
Qed.

(* Not sure If i need it, though, as i can get it from the following and more
general lemma: *)

(* Repaint green Lemma: painting it green preserves the coloring invariant *)
Lemma paint_green_cinv s:
     color_inv s -> color_inv (paint_green s).
Proof.  
case=>// [gs][ys][rs][G] Y R -> vS.
have V: validU (paint_green (gs +++ ys +++ rs)) by apply:repaint_valid.
apply: some_green_inv;case:(umany_NE G) {s}=>//=[t][c][ss][/eqP->]T GS E.
rewrite E ucat_ucons repaint_ucons in V vS *.
apply: umany_ucons=>//; first by case/valid_ucons: V=>//.
by apply: repaint_uall; case/valid_ucons: vS.
Qed.

(* Transfer: painting yellow to green *)
Lemma transfer_cinv s t:
  color_inv s -> ufind t s = Some yellow -> color_inv (uupd t green s).
Proof.           
case=>[gs][ys][rs][G]Y R -> V F.
case/valid_ucat: (V) => vG vYR H0.
case/valid_ucat: (vYR) => vY vR H1.
have NG: t \notin domU gs. 
+ case/ufind_ucat_dom: (F) => T.
 - by move: F; rewrite (ufind_ucatW _ T) (green_dom G T); discriminate.
 case:negP=>//HH; apply: False_ind; apply: HH=> HH.
 by case/hasP: H0; exists t.
have NR: t \notin domU rs. 
+ move/ufind_some: (F); rewrite valid_dom_ucat //= mem_cat. 
 case/orP=>// T; first by case/negP: NG.
 move: F; rewrite ufind_ucatS (ufind_ucatW _ T).
 rewrite valid_dom_ucat // mem_cat in T ;case/orP: T=>T.
 case: negP=>//HH; apply:False_ind; apply: HH=>HH.
 - by case/hasP: H1; exists t.
 by rewrite ufind_ucatS (ufind_ucatW _ T) (red_dom R T); discriminate. 
have: t \in domU ys.
+ admit. 
move/(yellow_dom Y)=>->.
rewrite !uupd_ucat (uupd_id _ NR) (uupd_id _ NG)  uupd_ucons.
case:eqP=>// _; rewrite ucat1s -ucat_usnoc.
exists (usnoc gs t green), unil, rs.
have GS: green_plus (usnoc gs t green)
       by apply umany_usnoc=>//; apply: umany_uall=>//.
have VV: validU (usnoc gs t green +++ rs).
+ have VG: validU (usnoc gs t green) by apply/valid_usnoc.  
 apply/valid_ucat. 
 rewrite VG vR has_sym valid_dom_usnoc // has_rcons negb_or NR.
 move: H0; rewrite valid_dom_ucat // has_cat negb_or;case/andP=>_ H0.
 by rewrite has_sym H0 //.
by rewrite ucat0s GS VV //.
Qed.

End ColorInvariant.

Section Projections.
(* I will be given this proof later *)  
Variable NXY : x <> y. 

Definition x_hist h s :=
  ufilter (fun tc => if (find tc.1 h) is Some (xx, v)
                    then x == xx
                    else false) s.  

Definition y_hist h s :=
  ufilter (fun tc => if (find tc.1 h) is Some (yy, v)
                    then y == yy 
                    else false) s.  



Section ProjectionLemmas.

  Lemma paintgreen_xhist h s:
    repaint green (x_hist h s) = x_hist h (repaint green s).
Proof. by case:s=>//= ss Hs; rewrite useqE /= filter_map. Qed.

Lemma paintgreen_yhist h s:
    repaint green (y_hist h s) = y_hist h (repaint green s).
Proof. by case:s=>//= ss Hs; rewrite useqE /= filter_map. Qed.

Lemma snocx_yhist t c h s:
   t \notin domU s -> (exists v, {{ (x,v) in h at t}}) ->
           y_hist h (usnoc s t c) = y_hist h s.
Proof.
move=>/= T [v]/=H. rewrite /y_hist ufilter_usnoc //=.
by case: (find t h) H=>//[[zz b]] /= [->]_; case:eqP=>///esym/NXY.
Qed.

Lemma snocy_xhist t c h s:
   t \notin domU s -> (exists v, {{ (y,v) in h at t}}) ->
           x_hist h (usnoc s t c) = x_hist h s.
Proof.
move=>/= T [v]/=H; rewrite /x_hist ufilter_usnoc //=.
by case: (find t h) H=>//[[zz b]] /= [->]_; case:eqP=>//.
Qed.

Lemma uconsx_yhist t c h s:
   t \notin domU s -> (exists v, {{ (x,v) in h at t}}) ->
           y_hist h (ucons t c s) = y_hist h s.
Proof.
move=>/= T [v]/=H; rewrite /y_hist ufilter_ucons //=.
by case: (find t h) H=>//[[zz b]] /= [->]_; case:eqP=>///esym/NXY.
Qed.

Lemma uconsy_xhist t c h s:
   t \notin domU s -> (exists v, {{(y,v) in h at t}}) ->
           x_hist h (ucons t c s) = x_hist h s.
Proof.
move=>/= T [v]/=H; rewrite /x_hist ufilter_ucons //=.
by case: (find t h) H=>//[[zz b]] /= [->]_; case:eqP=>//.
Qed.
End ProjectionLemmas.


Section ProjectionInvariants.

(* Here we define the invariant that ties the h history with the
 colored history s :

  First, the histories have the same timpestamps in their domain *)
Notation hs_inv h s:=  (dom h =i domU s).     

(* Then, a timestamp cannot be in two projections at one, and there are
  only two options x or y: *)

Notation sx_sy_inv h s := (domU s =i domU (ucat (x_hist h s) (y_hist h s))).

(* And finally, each history projection Hx Hy satisifes the coloring
  invariant. Repacking, we define proj_inv: *)

Definition proj_inv h s:=
  [/\ validU s, hs_inv h s, sx_sy_inv h s ,
      color_inv (x_hist h s) & color_inv (y_hist h s)].


Section HelperLemmas.
 
Lemma inx_x t h s:
  proj_inv h s ->  
    t \in domU (x_hist h s) -> exists v, {{ (x,v) in h at t}}.
Proof.    
case=>/=vS Dh Ds _ _ T.
case/dom_suppU: (T)=>[c]; rewrite supp_ufilter=> /andP [/andP[_]/= F] H.
by case:(find t h) F=>//[[z]]v /eqP ->; exists v. 
Qed.

Lemma iny_y t h s:
  proj_inv h s ->  
    t \in domU (y_hist h s) -> exists v, {{ (y,v) in h at t}}.
Proof.    
case=>/=vS Dh Ds _ _ T.
case/dom_suppU: (T)=>[c]; rewrite supp_ufilter=> /andP [/andP[_]/= F] H.
by case:(find t h) F=>//[[z]]v /eqP ->; exists v. 
Qed.

                        
Lemma inx_notiny t h s:
  proj_inv h s -> t \in domU (x_hist h s) -> t \notin domU (y_hist h s). 
Proof.
case=>[v]_ S _ _ X; case:negP=>// N;apply: False_ind; apply: N=> Y.
have D: (t \in domU s) by move/in_ufilter_in_dom: X.
move: (S t) D=> -> /dom_validU; case/valid_ucat => _ _ /negP H.
apply: False_ind; apply: H ;case:hasP=>// H; apply: False_ind; apply: H.
by exists t.
Qed.

Lemma iny_notinx t h s:
    proj_inv h s -> t \in domU (y_hist h s) -> t \notin domU (x_hist h s). 
Proof.
case=>[v]_ S _ _ Y; case:negP=>// N;apply: False_ind; apply: N=> X.
have D: (t \in domU s) by move/in_ufilter_in_dom: X.
move: (S t) D=> -> /dom_validU/valid_ucat=>[[_ _]]/negP H.
apply: False_ind; apply: H; case:hasP=>// H; apply: False_ind; apply: H.
by exists t.
Qed.

(* Don't know if I need the following, they follow from sx_sy_inv
Lemma filterxyE h s:
    proj_inv h s -> x_hist h (y_hist h s) = unil. 
Proof.
Admitted.

Lemma filteryxE h s:
    proj_inv h s -> y_hist h (x_hist h s) = unil. 
Proof.
Admitted.
*)

(* Reasoning with cons and snoc for the projection invariants? *)
(* I should leave this for later, as I'm not sure if they will be needed *)

(* consing greens is the only safe operation on the left, and im' not sure I need it *)
(* Lemma pinv_ucons h t s z v:  *)
(*    proj_inv (upd t (z,v) h) (t -:> green ::: s) /\ (z = x \/ z = y) <-> *)
(*      [/\ t \notin domU s, proj_inv h s & *)
(*          if (z == x) then color_inv (x_hist (upd t (x,v) h) ( t -:> green ::: s)) *)
(*          else if (z == y) then color_inv (y_hist (upd t (y,v) h) ( t -:> green ::: s)) *)
(*               else False]. *)

Lemma xhist_upd t c h s:
  x_hist h (uupd t c s) = uupd t c (x_hist h s).
Proof.
elim/u_ind: s =>//; first by rewrite useqE.
move=> r v ss R IH.
have X:  forall s, ufilter
     (fun tc : nat * color =>
      match find tc.1 h with
      | Some (xx, _) => x == xx
      | None => false
      end) s = x_hist h s by rewrite /x_hist.
rewrite uupd_ucons /x_hist ufilter_ucons //=.
case: eqP R =>[<-|E]R.
+ have S: t \notin domU (x_hist h ss)
             by move: R;apply/contra/in_ufilter_in_dom.
 case:(dom_find t h)=>[N//|[p]b F H]; rewrite (X ss) ufilter_ucons //=.
 - move: (find_none N)=>/= T; rewrite N (X ss).
  by rewrite (uupd_id _ S).
 move: (find_some F)=>/= T; rewrite F (X ss).
 case:eqP F=>//[<-|N]F; first by rewrite uupd_ucons; case:eqP=>//.
 by rewrite (uupd_id _ S).
case:(dom_find r h)=>[N//|[p]b F H];
   rewrite /= !(X ss) ufilter_ucons ?dom_uupd //=; first by rewrite N //.
by rewrite F; case:eqP=>//_; rewrite (X _) uupd_ucons; case:eqP=>//; rewrite IH.
Qed.

Lemma yhist_upd t c h s:
  y_hist h (uupd t c s) = uupd t c (y_hist h s).
Proof.                             
elim/u_ind: s =>//=; first by rewrite useqE.
move=> r v ss R IH.
have Y:  forall s, ufilter
     (fun tc : nat * color =>
      match find tc.1 h with
      | Some (yy, _) => y == yy
      | None => false
      end) s = y_hist h s by  rewrite /y_hist.
rewrite uupd_ucons /y_hist ufilter_ucons //=.
case: eqP R =>[<-|E]R.
+ have S: t \notin domU (y_hist h ss)
             by move: R;apply/contra/in_ufilter_in_dom.
 case:(dom_find t h)=>[N//|[p]b F H]; rewrite (Y ss) ufilter_ucons //=.
 - move: (find_none N)=>/= T; rewrite N (Y ss).
  by rewrite (uupd_id _ S).
 move: (find_some F)=>/= T; rewrite F (Y ss).
 case:eqP F=>//[<-|N]F; first by rewrite uupd_ucons; case:eqP=>//.
 by rewrite (uupd_id _ S).
case:(dom_find r h)=>[N//|[p]b F H];
   rewrite /= !(Y ss) ufilter_ucons ?dom_uupd //=; first by rewrite N //.
by rewrite F; case:eqP=>//_; rewrite (Y _) uupd_ucons; case:eqP=>//; rewrite IH.
Qed.

End HelperLemmas.

Section PreservationLemmas.

Lemma paintgreen_inv h s:
        proj_inv h s -> proj_inv h (repaint green s).
Proof.
case=> /(repaint_valid green)V H S /paint_green_cinv Cx /paint_green_cinv Cy.
rewrite /proj_inv //= -!paintgreen_xhist -!paintgreen_yhist -dom_repaint. 
by split=>// t; rewrite S (dom_repaint green) repaint_ucat.
Qed.

Lemma transfer_inv h s t:
        proj_inv h s ->  ufind t s = Some yellow -> proj_inv h (uupd t green s).
Proof.
move=> P; case: (P)=> /(valid_uupd t green)V S H Cx Cy F.
rewrite /proj_inv V xhist_upd yhist_upd dom_uupd -uupd_ucat dom_uupd.
move/ufind_some: (F); rewrite H=>T. 
move/dom_validU: (T)=>VV.
move: T; rewrite {1}valid_dom_ucat // mem_cat /=; case/orP=>//T.
+ move:(inx_notiny P T)=>NT. 
 rewrite (uupd_id _ NT) //; split=>//; apply:(transfer_cinv Cx).
 by rewrite ufind_ufilter F.
move:(iny_notinx P T)=>NT. 
rewrite (uupd_id _ NT) //; split=>//; apply:(transfer_cinv Cy).
 by rewrite ufind_ufilter F.
Qed.

(* TO do next: write snoc, rearrange *)

End  PreservationLemmas.
   
End ProjectionInvariants.


End Projections.

(* 
  
Definition hs_start h s := 
  (* There is an initial token *)
  [/\ (exists xv, find 0 h = Some xv /\ 0 \in domU s),
   (* and at least one entry fore each pointer *)  
      (exists t, exists v, {{ (x, v) in h at t}} /\ t \in domU (x_hist h s)) &
      (exists t, exists w, {{ (y, w) in h at t}} /\ t \in domU (y_hist h s)) ].

Actually, I do not need the last part of the invariant, as it follows
from the coloring invariant of both projections: in order to satisfy
the invariant, there should be at least one green entry for each.

As for the first part I could either add it later to the proj_inv or 

*)
End JayantiHistories.


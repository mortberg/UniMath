(* An experiment to see how uahp obstructs computations. Inlines all
definitions needed and removes coercions to make translation to
cubicaltt easier *)

Require Import UniMath.Foundations.Basics.PartD.

(* Propositions *)

Definition hProp := total2 (fun X : UU => isaprop X).

Definition hProppair (X : UU) (isp : isaprop X) : hProp :=
  tpair (fun X : UU => isaprop X) X isp.

Definition ishinh_UU (X : UU) := ∀ P : hProp, ((X -> pr1 P) -> pr1 P).

Lemma isapropishinh (X : UU) : isaprop (ishinh_UU X).
Proof.
apply impred; intro P.
apply impred; intro f.
apply (pr2 P).
Defined.

Definition ishinh (X : UU) : hProp := hProppair (ishinh_UU X) (isapropishinh X).

Definition hinhpr {X : UU} : X -> pr1 (ishinh X) :=
 fun (x : X) (P : hProp) (f : X -> pr1 P) => f x.

Definition hinhuniv {X : UU} {P : hProp} (f : X -> pr1 P)
  (inhX : pr1 (ishinh X)) : pr1 P := inhX P f.

Definition hdisj (P Q : UU) : hProp := ishinh (coprod P Q).

Definition hdisj_in1 {P Q : UU} (X : P) : pr1 (hdisj P Q) := hinhpr (ii1 X).
Definition hdisj_in2 {P Q : UU} : Q -> pr1 (hdisj P Q) := fun X => hinhpr (ii2 X).

Definition eqweqmaphProp {P P' : hProp} (e: @paths hProp P P') : weq (pr1 P) (pr1 P').
Proof.
destruct e.
apply idweq.
Defined.

Axiom uahp : ∀ P P' : hProp, (pr1 P -> pr1 P') -> (pr1 P' -> pr1 P) -> P = P'.

Definition weqtopathshProp {P P' : hProp} (w : weq (pr1 P) (pr1 P')) : P = P' :=
  uahp P P' w (invweq w).

Definition weqpathsweqhProp {P P' : hProp} (w : weq (pr1 P) (pr1 P')) :
  eqweqmaphProp (weqtopathshProp w) = w.
Proof.
apply proofirrelevance.
apply (isapropweqtoprop (pr1 P) (pr1 P') (pr2 P')).
Defined.

Theorem univfromtwoaxiomshProp (P P' : hProp) : isweq (@eqweqmaphProp P P').
Proof.
set (P1 := fun XY : hProp × hProp => pr1 XY = pr2 XY).
set (P2 := fun XY : hProp × hProp => weq (pr1 (pr1 XY)) (pr1 (pr2 XY))).
set (Z1 := total2 P1).
set (Z2 := total2 P2).
set (f := totalfun _ _ (fun XY : hProp × hProp =>
                           @eqweqmaphProp (pr1 XY) (pr2 XY)) : Z1 -> Z2).
set (g := totalfun _ _ (fun XY : hProp × hProp =>
                           @weqtopathshProp (pr1 XY) (pr2 XY)) : Z2 -> Z1).
assert (efg : ∀ z2 : Z2, f (g z2) = z2).
  intros. induction z2 as [ XY w] .
  exact (maponpaths (fun w : weq (pr1 (pr1 XY)) (pr1 (pr2 XY)) => tpair P2 XY w)
           (@weqpathsweqhProp (pr1 XY) (pr2 XY) w)).

set (h := fun a1 : Z1 => (pr1 (pr1 a1))).
assert (egf0 : ∀ a1 : Z1, pr1 (g (f a1)) = pr1 a1).
  intro; apply idpath.
assert (egf1 : ∀ a1 a1' : Z1, pr1 a1' = pr1 a1 -> a1' = a1).
  intros ? ? X .
  set (X' :=  maponpaths (@pr1 _ _ ) X).
  assert (is : isweq h).
    apply (isweqpr1pr1 hProp).
  apply (invmaponpathsweq (weqpair h is) _ _ X').
set (egf := fun a1 => (egf1 _ _ (egf0 a1))).
set (is2 := gradth _ _ egf efg).
apply (isweqtotaltofib P1 P2 (fun XY : hProp × hProp =>
         @eqweqmaphProp (pr1 XY) (pr2 XY)) is2 (dirprodpair P P')).
Defined.

Definition weqeqweqhProp (P P' : hProp) := weqpair _ (univfromtwoaxiomshProp P P') .

Lemma isasethProp : isaset hProp.
Proof.
unfold isaset.
intros x x'.
apply (isofhlevelweqb (S O) (weqeqweqhProp x x')
         (isapropweqtoprop (pr1 x) (pr1 x') (pr2 x'))).
Defined.

(* Sets *)

Definition hsubtypes (X : UU) := X -> hProp .
Definition carrier {X : UU} (A : hsubtypes X) : UU := @total2 X (fun x : X => pr1 (A x)).

Definition hrel (X : UU) := X -> X -> hProp.

Definition iseqclass {X : UU} (R : hrel X) (A : hsubtypes X) :=
     pr1 (ishinh (carrier A))
  × (∀ x1 x2 : X, pr1 (R x1 x2) -> pr1 (A x1) -> pr1 (A x2))
  × (∀ x1 x2 : X, pr1 (A x1) -> pr1 (A x2) -> pr1 (R x1 x2)).

Definition eqax0 {X : UU} {R : hrel X} {A : hsubtypes X} :
  iseqclass R A -> pr1 (ishinh (carrier A)) := fun S => pr1 S.
Definition eqax1 {X : UU} {R : hrel X} {A : hsubtypes X} :
  iseqclass R A -> ∀ x1 x2 : X, pr1 (R x1 x2) -> pr1 (A x1) -> pr1 (A x2) :=
  fun S => pr1 (pr2 S).
Definition eqax2 {X : UU} {R : hrel X} {A : hsubtypes X} :
  iseqclass R A -> ∀ x1 x2 : X, pr1 (A x1) -> pr1 (A x2) -> pr1 (R x1 x2) :=
  fun S => pr2 (pr2 S).

Lemma isapropiseqclass {X : UU} (R : hrel X) (A : hsubtypes X) :
  isaprop (iseqclass R A) .
Proof.
apply isofhleveldirprod.
- apply (isapropishinh (carrier A)).
- apply isofhleveldirprod.
  + repeat (apply impred; intro).
    apply (pr2 (A t0)).
  + repeat (apply impred; intro).
    apply (pr2 (R t t0)).
Defined.

Lemma isasethsubtypes (X : UU): isaset (hsubtypes X).
Proof.
change (isofhlevel 2 (hsubtypes X)).
apply impred; intro.
apply isasethProp.
Defined.

Definition hSet:= total2 (fun X : UU => isaset X) .

Definition isrefl {X : UU} (R : hrel X) := ∀ x : X, pr1 (R x x).
Definition issymm {X : UU} (R : hrel X) := ∀ (x1 x2 : X), pr1 (R x1 x2) -> pr1 (R x2 x1).
Definition istrans {X : UU} (R : hrel X) :=
  ∀ (x1 x2 x3 : X), pr1 (R x1 x2) -> pr1 (R x2 x3) -> pr1 (R x1 x3).

Definition ispreorder {X : UU} (R : hrel X) := istrans R × isrefl R .

Definition iseqrel {X : UU} (R : hrel X) := ispreorder R × issymm R.
Definition eqrel (X : UU) := total2 (fun R : hrel X => iseqrel R).

Definition eqrelrefl {X : UU} (R : eqrel X) : isrefl (pr1 R) :=
  pr2 (pr1 (pr2 R)).
Definition eqrelsymm {X : UU} (R : eqrel X) : issymm (pr1 R) := pr2 (pr2 R).
Definition eqreltrans {X : UU} (R : eqrel X) : istrans (pr1 R) :=
  pr1 (pr1 (pr2 R)).

Definition hSetpair X i := tpair isaset X i : hSet.
(* Definition boolset : hSet := hSetpair bool isasetbool. *)


Definition setquot {X : UU} (R : hrel X) := total2 (fun A => iseqclass R A).
Definition pr1setquot {X : UU} (R : hrel X) : setquot R -> (hsubtypes X) :=
  @pr1 _ (fun A => iseqclass R A).

Lemma isinclpr1setquot {X : UU} (R : hrel X) : isincl (pr1setquot R).
Proof .
apply isinclpr1; intro x0.
apply isapropiseqclass.
Defined.

Definition setquottouu0 {X : UU} (R : hrel X) (a : setquot R) : UU :=
  carrier (pr1 a).

Theorem isasetsetquot {X : UU} (R : hrel X) : isaset (setquot R).
Proof.
apply (isasetsubset (@pr1 _ _) (isasethsubtypes X)).
apply isinclpr1; intro x.
apply isapropiseqclass.
Defined.

(* Definition setquotinset {X : UU} (R : hrel X) : hSet := *)
(*   hSetpair _ (isasetsetquot R). *)

Theorem setquotpr {X : UU} (R : eqrel X) : X -> setquot (pr1 R).
Proof.
intros X0.
set (rax := eqrelrefl R).
set (sax := eqrelsymm R).
set (tax := eqreltrans R).
simple refine (tpair _ _ _).
  exact (fun x : X => (pr1 R) X0 x).
split.
  exact (hinhpr (tpair _ X0 (rax X0))).
split.
  intros x1 x2 X1 X2.
  now apply (tax X0 x1 x2 X2 X1).
intros x1 x2 X1 X2.
now apply (tax x1 X0 x2 (sax X0 x1 X1) X2).
Defined.

Lemma setquotl0 {X : UU} (R : eqrel X) (c : setquot (pr1 R))
  (x : setquottouu0 (pr1 R) c) : setquotpr R (pr1 x) = c.
Proof.
apply subtypeEquality.
  intro a.
  apply isapropiseqclass.
apply funextsec; intro x0.
apply uahp.
- intro r.
  exact (eqax1 (pr2 c) (pr1 x) x0 r (pr2 x)).
- intro r.
  exact (eqax2 (pr2 c) (pr1 x) x0 (pr2 x) r).
Defined.

Theorem setquotunivprop {X : UU} (R : eqrel X) (P : setquot (pr1 R) -> hProp)
  (ps : ∀ x : X, pr1 (P (setquotpr R x))) : ∀ c : setquot (pr1 R), pr1 (P c).
Proof.
intro c.
apply (@hinhuniv (carrier (pr1 c)) (P c)).
- intro x.
  set (e := setquotl0 R c x).
  apply (eqweqmaphProp (maponpaths P e)).
  exact (ps (pr1 x)).
- apply (eqax0 (pr2 c)).
Defined.

Theorem setquotuniv2prop {X : UU} (R : eqrel X) (P : setquot (pr1 R) -> setquot (pr1 R) -> hProp)
  (is : ∀ x x' : X, pr1 (P (setquotpr R x) (setquotpr R x'))) : ∀ c c' : setquot (pr1 R), pr1 (P c c').
Proof.
intros c c'.
  apply (setquotunivprop R (λ c0' : setquot (pr1 R), P c c0')
     (λ x : X,
      setquotunivprop R (λ c0 : setquot (pr1 R), P c0 (setquotpr R x))
        (λ x0 : X, is x0 x) c) c').
Defined.

Lemma iscompsetquotpr {X : UU} (R : eqrel X) (x x' : X) (a : pr1 (pr1 R x x')) :
  setquotpr R x = setquotpr R x'.
Proof.
apply (@subtypeEquality (hsubtypes X) (@iseqclass X (pr1 R))).
- intros b.
  apply isapropiseqclass.
- apply funextsec; intro x0.
  simpl.
  apply uahp.
  * intro r0.
    exact (@eqreltrans X R _ _ _ (eqrelsymm R _ _ a) r0).
  * intro x0'.
    exact (eqreltrans R _ _ _ a x0').
Defined.

Theorem weqpathsinsetquot {X : UU} (R : eqrel X) (x x' : X) :
  weq (pr1 (pr1 R x x')) (setquotpr R x = setquotpr R x').
Proof.
exists (iscompsetquotpr R x x').
apply isweqimplimpl.
- intro e.
  set (e' := maponpaths (pr1setquot (pr1 R)) e).
  set (e'' := maponpaths (fun f => f x') e').
  exact (eqweqmaphProp (pathsinv0 e'') (eqrelrefl R x')).
- exact (pr2 (pr1 R x x')).
- exact (isasetsetquot (pr1 R) (setquotpr R x) (setquotpr R x')).
Defined.

(* Definition isdecprop (P:UU) := (P ⨿ ¬P) × isaprop P. *)
(* Theorem isapropisdeceq (X:UU): isaprop (isdeceq X). *)
(* Proof. intro. apply ( isofhlevelsn 0 ) .  intro is . unfold isdeceq. apply impred . intro x .  apply ( isapropisisolated X x ) .   Defined . *)

Lemma isdecpropweqf {X Y} : X≃Y -> isdecprop X -> isdecprop Y.
Proof.
  intros w i. unfold isdecprop in *. induction i as [xnx i]. split.
  - clear i. induction xnx as [x|nx].
    * apply ii1. now apply w.
    * apply ii2. intro x'. apply nx. now apply (invmap w).
  - apply (isofhlevelweqf 1 (X:=X)).
    { exact w. }
    { exact i. }
Defined.



(* Theorem isapropisisolated ( X : UU ) ( x : X ) : isaprop ( isisolated X x ) . *)
(* Proof. *)
(* apply isofhlevelsn. *)
(* intro is. *)
(* apply impred. *)
(* intro x'. *)
(* apply (isapropdec _ (isaproppathsfromisolated X x is x')). *)
(* Defined. *)


(* Lemma C P Q : isaprop P -> isaprop Q -> (P -> ¬Q) -> isaprop (sum P Q). *)
(* Proof. *)
(*   intros i j n. apply invproofirrelevance. intros a b. *)
(*   induction a as [a|a]. *)
(*   - induction b as [b|b]. *)
(*     + apply maponpaths, i. *)
(*     + induction (n a b). *)
(*   - induction b as [b|b]. *)
(*     + induction (n b a). *)
(*     + apply maponpaths, j. *)
(* Defined. *)


(* Theorem isapropisdeceq (X : UU) (H : isaset X) : isaprop (isdeceq X). *)
(* Proof. *)
(* unfold isdeceq. *)
(* apply impred. *)
(* intros. *)
(* apply impred. *)
(* intros. *)
(* apply C. *)
(* apply H. *)
(* apply isapropneg. *)
(* intros. *)
(* rewrite X0. *)
(* intro XX. *)
(* apply (XX (idpath t0)). *)
(* Defined. *)

Lemma isapropcoprod P Q : isaprop P -> isaprop Q -> (P -> Q -> ∅) -> isaprop (P ⨿ Q).
Proof.
  intros ? ? i j n. apply invproofirrelevance. intros a b. apply inv_equality_by_case.
  induction a as [a|a].
  - induction b as [b|b].
    + apply X.
    + contradicts (i a) b.
  - induction b as [b|b].
    + contradicts (i b) a.
    + apply X0.
Defined.

Theorem isapropdec (X:UU): isaprop X -> isaprop (X ⨿ ¬X).
Proof.
  intros a b c.
apply isapropcoprod.
  - exact a .
  - apply isapropneg.
  - exact (λ x n, n x).
Defined.


Definition isapropisdecprop ( X : UU ) : isaprop ( isdecprop X ).
Proof.
  apply (isofhlevelweqf 1 (weqdirprodcomm _ _)).
  apply isofhleveltotal2.
  - apply isapropisaprop.
  - intro i. now apply isapropdec.
Defined.


Theorem isdeceqsetquot_non_constr {X : UU} (R : eqrel X)
  (is : ∀ x x' : X, isdecprop (pr1 (pr1 R x x'))) : isdeceq (setquot (pr1 R)).
Proof.
apply isdeceqif.
intros x x'.
apply (@setquotuniv2prop X R
       (fun (x0 x'0 : setquot (pr1 R)) => hProppair (isdecprop (paths x0 x'0)) (isapropisdecprop (paths x0 x'0)))).
simpl.
intros x0 x0'.
simpl.
Check (isdecpropweqf).
apply (@isdecpropweqf (pr1 (pr1 R x0 x0')) (setquotpr R x0 = setquotpr R x0') (@weqpathsinsetquot X R x0 x0') (@is x0 x0')).
Defined.

(* Definition  isdeceqsetquot {X : UU} (R : eqrel X) *)
(*   (is : ∀ x x' : X, isdecprop (pr1 (pr1 R x x'))) : isdeceq (setquot (pr1 R)). *)
(* Proof. *)
(* intros x x'. *)
(* destruct (boolchoice (setquotbooleq R is x x')) as [ i | ni ] .  apply ( ii1 ( setquotbooleqtopaths R is x x' i ) ) . apply ii2 .   intro e .  destruct ( falsetonegtrue _ ni ( setquotpathstobooleq R is x x' e ) ) . Defined . *)

Require Import UniMath.Foundations.NumberSystems.NaturalNumbers.

(* hz experiment *)
Lemma nat1 (m0 m1 n0 n1 : nat) (h0 : m0 = n0) (h1 : m1 = n1) : m0 + m1 = n0 + n1.
Proof.
rewrite h0.
rewrite h1.
apply idpath.
Qed.

Definition relnat2 : eqrel (prod nat nat).
simple refine (tpair _ _ _).
- intros x y.
  simple refine (hProppair _ _).
  + exact (paths (fst x + snd y) (snd x + fst y)).
  + apply isasetnat.
- simpl.
  repeat split.
  + intros x y z.
    simpl.
    intros h1 h2.
    apply (@natplusrcan _ _ (fst y + snd y)).
    generalize (nat1 _ _ _ _ h1 h2).
repeat rewrite natplusassoc.
intros.
assert (H1 : snd z + (fst y + snd y) = snd y + (fst y + snd z)).
rewrite <- natplusassoc.
rewrite natpluscomm.
apply nat1.
apply idpath.
rewrite natpluscomm.
apply idpath.
rewrite H1.
rewrite H.
apply nat1.
apply idpath.
rewrite <- natplusassoc.
rewrite natpluscomm.
apply nat1.
apply idpath.
apply idpath.
  + intros x; simpl.
    rewrite natpluscomm.
    apply idpath.
  + intros x y; simpl.
    rewrite natpluscomm.
    intros h.
    rewrite h.
    rewrite natpluscomm.
    apply idpath.
Defined.

Definition hz := setquot (pr1 relnat2).
Definition hzero := setquotpr relnat2 (0,0).
Definition hone := setquotpr relnat2 (1,0).

Lemma isdeceqhz : isdeceq hz.
Proof.
apply isdeceqsetquot_non_constr.
intros x y.
case x as [x1 x2].
case y as [y1 y2].
split.
simpl.
apply (isdeceqnat (x1 + y2) (x2 + y1)).
apply (@isasetnat (x1 + y2) (x2 + y1)).
Defined.

Definition deceqtobool {X : UU} (h : isdeceq X) (x y : X) : bool := match h x y with
  | ii1 _ => true
  | ii2 _ => false
  end.

Definition test : bool := @deceqtobool hz isdeceqhz hzero hone.

(* This is stuck! *)
(* Eval compute in test. *)

(* New stuff below here *)

Definition R : eqrel bool.
Proof.
  simple refine (_,,_).
  { intros x y. exists (x=y). apply isasetbool. }
  split.
  - split.
    + intros x y z. apply pathscomp0.
    + intros x. reflexivity.
  - intros x y. apply pathsinv0.
Defined.

(* Definition T : hSet := setquotinset (pr1 R). *)

Definition bool' : UU := setquot (pr1 R).
Definition true' : bool' := setquotpr R true.
Definition false' : bool' := setquotpr R false.

(* Version of predicate based on hdisj (ie truncated sum) *)

Definition P' (t : bool') : hProp := hdisj (t = true') (t = false').

Lemma K' (t : setquot (pr1 R)) : pr1 (P' t).
Proof.
  apply setquotunivprop. intros x. unfold P'.
  induction x as [x|x].
  - apply hdisj_in1. reflexivity.
  - apply hdisj_in2. reflexivity.
Defined.
Check K'.
Print Assumptions K'.

Goal K' true' = hdisj_in1 (idpath true').
 try reflexivity.                (* Error: Unable to unify "L'" with "K' true'". *)
Abort.

(* Example of computing a boolean using K' by Thierry: *)

(*  One should be able to prove *)
(*  not (Path _ true'  false') *)
Lemma true'neqfalse' : neg (true' = false').
Proof.
intros H.
generalize (maponpaths (fun apa => pr1 (pr1 apa true)) H).
simpl.
intro H2.
apply nopathsfalsetotrue.
rewrite <- H2.
apply idpath.
Defined.

Lemma test1 (x : setquot (pr1 R)) : x = true' -> x = false' -> empty.
Proof.
intro H.
rewrite H.
apply true'neqfalse'.
Defined.

(*  This means that the property P' t is of the form *)
(*  ishinh (A + B) *)
(* with   A -> B -> N0 *)
(*  If A -> B -> N0  we should be able to prove *)
(*  isinh A -> isinh B -> N0 *)
Lemma test2 (x : setquot (pr1 R)) :
  pr1 (ishinh (x = true')) -> pr1 (ishinh (x = false')) -> empty.
Proof.
intros p1 p2.
refine (@hinhuniv (x = true') (hProppair empty isapropempty) _ p1).
intro H1.
refine  (@hinhuniv _ (hProppair _ isapropempty) _ p2).
intro H2.
apply (test1 x H1 H2).
Defined.

(* and then we can prove that *)
(*  isinh A + isinh B *)
(* is a proposition. *)
Lemma test3 (x : setquot (pr1 R)) :
  isaprop (coprod (pr1 (ishinh (x = true'))) (pr1 (ishinh (x = false')))).
Proof.
apply invproofirrelevance.
intros a b.
induction a as [a|a].
- induction b as [b|b].
  + apply maponpaths.
    apply (@isapropishinh (x = true') a b).
  + destruct (test2 x a b).
- induction b as [b|b].
  + destruct (test2 x b a).
  + apply maponpaths, isapropishinh.
Defined.

(*  But we have a function   isinh A + isinh B -> bool *)
Definition f (x : setquot (pr1 R)) :
  coprod (pr1 (ishinh (x = true'))) (pr1 (ishinh (x = false'))) -> bool.
Proof.
intro H; destruct H.
  exact true.
exact false.
Defined.

(*  This means that using K', we can define a function
      foo : setquot bool R.1 -> bool *)
(* and then we can ask about foo false and foo true, *)
Definition bar (x : setquot (pr1 R)) : (x = true') ⨿ (x = false') ->
   pr1 (ishinh (x = true')) ⨿ pr1 (ishinh (x = false')).
Proof.
intro H.
case H; intro p.
  exact (inl (hinhpr p)).
exact (inr (hinhpr p)).
Defined.

Definition foo {x : setquot (pr1 R)} (x' : pr1 (P' x)) : bool :=
  f x (@hinhuniv _ (hProppair _ (test3 x)) (bar x) x').

Print Assumptions foo.
(* Axioms: *)
(* uahp : ∀ P P' : hProp, (pr1 P -> pr1 P') -> (pr1 P' -> pr1 P) -> P = P' *)
(* funextfunax : ∀ (X Y : UU) (f g : X -> Y), (∀ x : X, f x = g x) -> f = g *)

(* Eval compute in foo (K' true'). *)  (* This is stuck *)
Goal foo (K' true') = true.
try reflexivity.
Admitted.





(* Alternative version of the first exercise based on a predicate
   based on sum instead of hdisj *)

Lemma C P Q : isaprop P -> isaprop Q -> (P -> ¬Q) -> isaprop (sum P Q).
Proof.
  intros i j n. apply invproofirrelevance. intros a b.
  induction a as [a|a].
  - induction b as [b|b].
    + apply maponpaths, i.
    + induction (n a b).
  - induction b as [b|b].
    + induction (n b a).
    + apply maponpaths, j.
Defined.

Definition P : setquot (pr1 R) -> hProp.
Proof.
  intros t. exists (sum (t = true') (t = false')). apply C.
  - apply isasetsetquot.
  - apply isasetsetquot.
  - intros p q.
    exact (nopathstruetofalse (invmap (weqpathsinsetquot R true false) (!p @ q))).
Defined.

Lemma K t : pr1 (P t).
Proof.
  apply setquotunivprop. intros x. unfold P; simpl.
  induction x as [x|x].
  - apply ii1. reflexivity.
  - apply ii2. reflexivity.
Defined.

Print Assumptions K.

Goal K true' = ii1 (idpath true').
  try reflexivity.             (* Error: Unable to unify "L" with "K true'". *)
Abort.

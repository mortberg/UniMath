(* an experiment to see how uahp obstructs computations *)

Require Import UniMath.Foundations.Propositions.

Definition hsubtypes (X : UU) :=  X -> hProp .
Definition carrier {X : UU} (A : hsubtypes X) := total2 A.

Definition hrel (X : UU) := X -> X -> hProp.

Definition iseqclass {X : UU} (R : hrel X) (A : hsubtypes X) :=
     ishinh (carrier A)
  × (∀ x1 x2 : X, R x1 x2 -> A x1 -> A x2)
  × (∀ x1 x2 : X, A x1 -> A x2 -> R x1 x2 ).

Definition eqax0 {X : UU} {R : hrel X} {A : hsubtypes X} :
  iseqclass R A -> ishinh (carrier A) := fun S => pr1 S.
Definition eqax1 {X : UU} {R : hrel X} {A : hsubtypes X} :
  iseqclass R A -> ∀ x1 x2 : X, R x1 x2 -> A x1 -> A x2 := fun S => pr1 (pr2 S).
Definition eqax2 {X : UU} {R : hrel X} {A : hsubtypes X} :
  iseqclass R A -> ∀ x1 x2 : X, A x1 -> A x2 -> R x1 x2 :=
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

Definition isrefl {X : UU} (R : hrel X) := ∀ x : X, R x x.
Definition issymm {X : UU} (R : hrel X) := ∀ (x1 x2 : X), R x1 x2 -> R x2 x1.
Definition istrans {X : UU} (R : hrel X) :=
  ∀ (x1 x2 x3 : X), R x1 x2 -> R x2 x3 -> R x1 x3.

Definition ispreorder {X : UU} (R : hrel X) := istrans R × isrefl R .

Definition iseqrel {X : UU} (R : hrel X) := ispreorder R × issymm R.
Definition eqrel (X : UU) := total2 (fun R : hrel X => iseqrel R).

Definition eqrelrefl {X : UU} (R : eqrel X) : isrefl (pr1 R) :=
  pr2 (pr1 (pr2 R)).
Definition eqrelsymm {X : UU} (R : eqrel X) : issymm (pr1 R) := pr2 (pr2 R).
Definition eqreltrans {X : UU} (R : eqrel X) : istrans (pr1 R) :=
  pr1 (pr1 (pr2 R)).

Definition hSetpair X i := tpair isaset X i : hSet.
Definition boolset : hSet := hSetpair bool isasetbool.


Definition setquot {X : UU} (R : hrel X) := total2 (fun A => iseqclass R A).
Definition pr1setquot {X : UU} (R : hrel X) : setquot R -> (hsubtypes X) :=
  @pr1 _ (fun A => iseqclass R A).

Lemma isinclpr1setquot {X : UU} (R : hrel X) : isincl (pr1setquot R).
Proof .
apply isinclpr1; intro x0.
apply isapropiseqclass.
Defined.

Definition setquottouu0 {X : UU} (R : hrel X) (a : setquot R) :=
  carrier (pr1 a).

Theorem isasetsetquot {X : UU} (R : hrel X) : isaset (setquot R).
Proof.
apply (isasetsubset (@pr1 _ _) (isasethsubtypes X)).
apply isinclpr1; intro x.
apply isapropiseqclass.
Defined.

Definition setquotinset {X : UU} (R : hrel X) : hSet :=
  hSetpair _ (isasetsetquot R).

Theorem setquotpr {X : UU} (R : eqrel X) : X -> setquot (pr1 R).
Proof.
intros X0.
set (rax := eqrelrefl R).
set (sax := eqrelsymm R).
set (tax := eqreltrans R).
split with (fun x : X => (pr1 R) X0 x).
split.
  exact (hinhpr (tpair _ X0 (rax X0))).
assert (a1 : ∀ x1 x2 : X, pr1 R x1 x2 -> pr1 R X0 x1 -> pr1 R X0 x2).
  intros x1 x2 X1 X2.
  now apply (tax X0 x1 x2 X2 X1).
split.
  assumption.
intros x1 x2 X1 X2.
now apply (tax x1 X0 x2 (sax X0 x1 X1) X2).
Defined.

Lemma setquotl0 {X : UU} (R : eqrel X) (c : setquot (pr1 R))
  (x : setquottouu0 _ c) : setquotpr R (pr1 x) = c.
Proof.
apply (invmaponpathsincl _ (isinclpr1setquot (pr1 R))).
apply funextsec; intro x0.
destruct c as [A iseq].
destruct x as [x is].
simpl in *.
apply uahp.
- intro r.
  exact (eqax1 iseq _ _ r is).
- intro a.
  exact (eqax2 iseq _ _ is a).
Defined.

Theorem setquotunivprop {X : UU} (R : eqrel X) (P : setquot (pr1 R) -> hProp)
  (ps : ∀ x : X, P (setquotpr R x)) : ∀ c : setquot (pr1 R), P c .
Proof.
intro c.
apply (@hinhuniv (carrier (pr1 c)) (P c)).
- intro x.
  set (e := setquotl0 R c x).
  apply (eqweqmaphProp (maponpaths P e)).
  exact (ps (pr1 x)).
- apply (eqax0 (pr2 c)).
Defined.


(* New stuff below here *)

Definition R : eqrel (pr1 boolset).
Proof.
  refine (_,,_).
  { intros x y. exists (x=y). apply isasetbool. }
  split.
  - split.
    + intros x y z. apply pathscomp0.
    + intros x. reflexivity.
  - intros x y. apply pathsinv0.
Defined.

Definition T := setquotinset (pr1 R).

Definition true' := setquotpr R true.
Definition false' := setquotpr R false.


(* Version of predicate based on hdisj (ie truncated sum) *)

Definition P' (t : pr1 T) : hProp := hdisj (t = true') (t = false').

Lemma K' t : P' t.
Proof.
  apply setquotunivprop. intros x. unfold P'.
  induction x as [x|x].
  - apply hdisj_in1. reflexivity.
  - apply hdisj_in2. reflexivity.
Defined.

Print Assumptions K'.

Goal K' true' = hdisj_in1 (idpath true').
 try reflexivity.                (* Error: Unable to unify "L'" with "K' true'". *)
Abort.



(* Version of predicate based on sum *)

(* preliminary results *)
Lemma iscompsetquotpr {X : UU} (R : eqrel X) (x x' : X) (a : pr1 R x x') :
  setquotpr R x = setquotpr R x'.
Proof.
apply (invmaponpathsincl _ (isinclpr1setquot (pr1 R))); simpl.
apply funextsec; intro x0.
apply uahp.
- intro r0.
  exact (eqreltrans R _ _ _ (eqrelsymm R _ _ a) r0).
- intro x0'.
  exact (eqreltrans R _ _ _ a x0').
Defined.

Theorem weqpathsinsetquot {X : UU} (R : eqrel X) (x x' : X) :
  weq (pr1 R x x') (setquotpr R x = setquotpr R x').
Proof.
split with (iscompsetquotpr R x x').
apply isweqimplimpl.
- intro e.
  set (e' := maponpaths (pr1setquot (pr1 R)) e).
  set (e'' := maponpaths (fun f => f x') e').
  exact (eqweqmaphProp (pathsinv0 e'') (eqrelrefl R x')).
- exact (pr2 (pr1 R x x')).
- exact (isasetsetquot (pr1 R) (setquotpr R x) (setquotpr R x')).
Defined.

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


Definition P : pr1 T -> hProp.
Proof.
  intros t. exists (sum (t = true') (t = false')). apply C.
  - apply (pr2 T).
  - apply (pr2 T).
  - intros p q.
    exact (nopathstruetofalse (invmap (weqpathsinsetquot R true false) (!p @ q))).
Defined.

Lemma K t : P t.
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

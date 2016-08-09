Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Section def_subobject_classifier.

Variable C : precategory.
Variable (T : Terminal C).

Local Notation "1" := T.

Definition isSubobjectClassifier {Ω : C} (t : C⟦1,Ω⟧) : UU :=
  Π {U X : C} (j : Monic _ U X),
    ∃! (Xj : C⟦X,Ω⟧), Σ (sq : j ;; Xj = TerminalArrow U ;; t),
      isPullback Xj t j (TerminalArrow U) sq.

Lemma isaprop_isSubobjectClassifier (Ω : C) (t : C⟦1,Ω⟧) :
  isaprop (isSubobjectClassifier t).
Proof.
repeat (apply impred; intro); apply isapropiscontr.
Qed.

Definition SubobjectClassifier : UU :=
  Σ (Ω : C) (t : C⟦1,Ω⟧), isSubobjectClassifier t.

Definition mk_SubobjectClassifier {Ω : C} (t : C⟦1,Ω⟧)
  (H : isSubobjectClassifier t) : SubobjectClassifier := (Ω,,(t,,H)).

Definition hasSubobjectClassifier : UU := ishinh SubobjectClassifier.

Definition SubobjectClassifierOb (Ω : SubobjectClassifier) : C :=
  pr1 Ω.
Coercion SubobjectClassifierOb : SubobjectClassifier >-> ob.

Definition SubobjectClassifierMor (Ω : SubobjectClassifier) : C⟦1,Ω⟧ :=
  pr1 (pr2 Ω).

Definition SubobjectClassifier_isSubobjectClassifier (Ω : SubobjectClassifier) :
  isSubobjectClassifier (SubobjectClassifierMor Ω) := pr2 (pr2 Ω).

Definition ClassifyingMor (Ω : SubobjectClassifier) {U X : C} (j : Monic _ U X) : C⟦X,Ω⟧ := pr1 (pr1 (SubobjectClassifier_isSubobjectClassifier Ω _ _ j)).

Definition ClassifyingMorCommutes (Ω : SubobjectClassifier) {U X : C} (j : Monic _ U X) :
  j ;; ClassifyingMor Ω j = TerminalArrow U ;; SubobjectClassifierMor Ω
    := pr1 (pr2 (pr1 (SubobjectClassifier_isSubobjectClassifier Ω _ _ j))).

Definition ClassifyingMorSquareIsPullback (Ω : SubobjectClassifier) {U X : C} (j : Monic _ U X) :
  isPullback _ _ _ _ (ClassifyingMorCommutes Ω j)
    := pr2 (pr2 (pr1 (SubobjectClassifier_isSubobjectClassifier Ω _ _ j))).

End def_subobject_classifier.

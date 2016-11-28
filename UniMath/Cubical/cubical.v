Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.opp_precat.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Local Notation "'PSh' C" := [C^op,HSET,has_homsets_HSET] (at level 3).

(** Category of elements of a presheaf *)
Section cat_of_elems_def.

Context {C : precategory} (hsC : has_homsets C) (F : PSh C).

Definition cat_of_elems_ob_mor : precategory_ob_mor.
Proof.
simpl in *.
mkpair.
- apply (Σ (c : C), F c : hSet).
- intros a b.
  apply (Σ (f : C^op⟦pr1 b,pr1 a⟧), # F f (pr2 b) = pr2 a).
Defined.

Definition cat_of_elems : precategory.
Proof.
mkpair.
- apply (tpair _ cat_of_elems_ob_mor).
  split.
  + intros a.
    exists (identity _).
    abstract (now rewrite (functor_id F)).
  + intros a b c f g.
    exists (pr1 g ;; pr1 f).
    abstract (rewrite functor_comp; cbn;
              eapply pathscomp0; [apply maponpaths, (pr2 g)|];
              apply (pr2 f)).
- abstract (repeat split; intros;
            apply subtypeEquality; try (intro; apply setproperty); simpl;
              [ apply id_left | apply id_right | apply assoc]).
Defined.

Lemma has_homsets_cat_of_elems : has_homsets cat_of_elems.
Proof.
intros a b.
apply isaset_total2.
+ now apply has_homsets_opp, hsC.
+ now intros f; apply isasetaprop, setproperty.
Qed.

End cat_of_elems_def.

Local Notation "∫ F" := (cat_of_elems F) (at level 3).

Section cat_of_elems_theory.

Context {C : precategory} (hsC : has_homsets C) (F G : PSh C).

Lemma eq_mor_cat_of_elems (a b : ∫ F) (f g : ∫ F ⟦a,b⟧) :
  pr1 f = pr1 g → f = g.
Proof.
now apply subtypeEquality; intros x; apply setproperty.
Qed.

Definition nat_trans_cat_of_elems (α : nat_trans (pr1 F) (pr1 G)) : functor (∫ F) (∫ G).
Proof.
mkpair.
- mkpair.
  + intros X; apply (pr1 X,, α (pr1 X) (pr2 X)).
+ intros a b f.
exists (pr1 f).
simpl.
generalize (toforallpaths _ _ _ (nat_trans_ax α _ _ (pr1 f)) (pr2 b)); unfold compose.
simpl.
intros HH.
eapply pathscomp0.
eapply pathsinv0.
apply HH.
apply maponpaths.
apply (pr2 f).
-
split.
intros x.
simpl.
apply subtypeEquality; trivial.
intro xx.
apply setproperty.
intros a b c f g.
apply subtypeEquality; trivial.
intro xx.
apply setproperty.
Admitted.

End cat_of_elems_theory.

Section types.

Variables (C : precategory) (hsC : has_homsets C).

Definition TypeIn (Γ : PSh C) : UU := PSh (∫ Γ).

Local Notation "Γ ⊢" := (TypeIn Γ) (at level 3).

Lemma test (Γ Δ : PSh C) (σ : nat_trans (pr1 Δ) (pr1 Γ)) (A : Γ ⊢) : Δ ⊢.
Proof.
Admitted.

End types.

Section cubical.

Variables (C : precategory) (hsC : has_homsets C) (F : functor C C).

Local Notation "'Id'" := (functor_identity C).

Variable (p_F : nat_trans F Id).
Variable (e0 e1 : nat_trans Id F).

Variable (Γ : PSh C).

Definition Γplus : PSh C.
Proof.
mkpair.
- mkpair.
  + intro I.
    apply (Γ (F I)).
  + simpl; intros I J f.
    apply (# Γ (# F f)).
- split.
  + now intros I; simpl; rewrite (functor_id F), (functor_id Γ).
  + intros I J K f g; simpl in *.
    unfold compose; simpl.
    rewrite (functor_comp F).
    apply (functor_comp Γ).
Defined.

Local Notation "'Γ+'" := Γplus.

Definition p : nat_trans Γ Γ+.
mkpair.
- simpl; intro I; apply (# Γ (p_F I)).
- intros I J f; simpl in *; rewrite <- !(functor_comp Γ).
  now apply maponpaths, pathsinv0, (nat_trans_ax p_F).
Defined.

Definition f0 : nat_trans Γ+ Γ.
Proof.
mkpair.
- simpl; intro I; apply (# Γ (e0 I)).
- intros I J f; simpl in *; rewrite <- !(functor_comp Γ).
  now apply maponpaths, pathsinv0, (nat_trans_ax e0).
Defined.

Definition f1 : nat_trans Γ+ Γ.
Proof.
mkpair.
- simpl; intro I; apply (# Γ (e1 I)).
- intros I J f; simpl in *; rewrite <- !(functor_comp Γ).
  now apply maponpaths, pathsinv0, (nat_trans_ax e1).
Defined.

Local Notation "'[0]'" := f0.
Local Notation "'[1]'" := f1.

Arguments nat_trans_comp {_ _ _ _ _} _ _.
Local Notation "α • β" := (nat_trans_comp α β) (at level 50, format "α  •  β", left associativity).

Section version1.
Hypothesis (Hpe0 : p_F • e0 = nat_trans_id F).
Hypothesis (Hpe1 : p_F • e1 = nat_trans_id F).

Lemma pf0 : [0] • p = nat_trans_id Γ+.
Proof.
apply (nat_trans_eq has_homsets_HSET).
simpl; intro I.
assert (H := nat_trans_eq_pointwise Hpe0 I).
simpl in H.
assert (H1 : # Γ (e0 I) ;; # Γ (p_F I) = # Γ (identity (F I))).
rewrite <- H.
apply pathsinv0.
apply (functor_comp Γ).
rewrite (functor_id Γ) in H1.
apply H1.
Qed.

Lemma pf1 : [1] • p = nat_trans_id Γ+.
Proof.
apply (nat_trans_eq has_homsets_HSET).
simpl; intro I.
assert (H := nat_trans_eq_pointwise Hpe1 I).
simpl in H.
assert (H1 : # Γ (e1 I) ;; # Γ (p_F I) = # Γ (identity (F I))).
rewrite <- H.
apply pathsinv0.
apply (functor_comp Γ).
rewrite (functor_id Γ) in H1.
apply H1.
Qed.
End version1.

Section version2.
Hypothesis (Hpe0 : e0 • p_F = nat_trans_id _).
Hypothesis (Hpe1 : e1 • p_F = nat_trans_id _).

Lemma pf0' : p • [0] = nat_trans_id Γ.
Proof.
apply (nat_trans_eq has_homsets_HSET).
simpl; intro I.
assert (H := nat_trans_eq_pointwise Hpe0 I).
simpl in H.
rewrite <- (functor_id Γ).
eapply pathscomp0.
eapply pathsinv0.
eapply (functor_comp Γ).
unfold compose; simpl.
now rewrite H.
Qed.

Lemma pf1' : p • [1] = nat_trans_id Γ.
Proof.
apply (nat_trans_eq has_homsets_HSET).
simpl; intro I.
assert (H := nat_trans_eq_pointwise Hpe1 I).
simpl in H.
rewrite <- (functor_id Γ).
eapply pathscomp0.
eapply pathsinv0.
eapply (functor_comp Γ).
unfold compose; simpl.
now rewrite H.
Qed.

End version2.
End cubical.

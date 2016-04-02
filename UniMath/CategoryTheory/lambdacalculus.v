Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.colimits.colimits.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.colimits.chains.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.EquivalencesExamples.
Require Import UniMath.CategoryTheory.AdjunctionHomTypesWeq.
Require Import UniMath.CategoryTheory.colimits.polynomialfunctors.
Require Import UniMath.CategoryTheory.exponentials.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).


Require Import UniMath.Foundations.NumberSystems.NaturalNumbers.

Section temp.

Variable (C : precategory).

Lemma strong_ind (P : nat -> UU) : (forall n, (forall m, m < n -> P m) -> P n) -> forall n, P n.
Proof.
intros.
induction n.
apply X.
admit.
apply X.
induction m.

admit.
(* intros H0 IH. *)
(* intros n. *)
(* apply (IH n). *)
(* induction m. *)
(* admit. *)
(* apply IH. *)
(* induction n. *)
(* apply H0. *)
(* apply IH. *)
Admitted.
(* apply (IH n _ (natlthnsn n) IHn). *)
(* Defined. *)


Lemma test (c : chain C) : forall j, (forall i, i < j -> C⟦dob c i,dob c j⟧) -> forall i, C⟦dob c i,dob c j⟧.
Proof.
intros j h.
apply strong_ind.

Lemma test (c : chain C) : forall i j, i < j -> C⟦dob c i,dob c j⟧.
Proof.
induction i using strong_ind.
admit.
intros i j hij.
generalize i.
apply strong_ind.
admit.
admit.
Admitted.

End temp.

(* The functor "* : C^2 -> C" is omega cocont *)
Section binprod_functor.

Variables (C : precategory) (PC : Products C) (hsC : has_homsets C).
Variables (hE : has_exponentials PC).


Definition inc1 (cAB : chain (product_precategory C C)) (K : C)
  (ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K) :
  forall i j,
              C ⟦ ProductObject C (PC (pr1 (pr1 cAB i)) (pr2 (dob cAB j))),
                  ProductObject C (PC (pr1 (pr1 cAB (S i))) (pr2 (dob cAB j))) ⟧.
Proof.
intros i j.
apply (ProductOfArrows _ (PC _ _) (PC _ _) (pr1 (dmor cAB (idpath _))) (identity (pr2 (dob cAB j)))).
Defined.

Definition inc2 (cAB : chain (product_precategory C C)) (K : C)
  (ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K) :
  forall i j,
              C ⟦ ProductObject C (PC (pr1 (pr1 cAB i)) (pr2 (dob cAB j))),
                  ProductObject C (PC (pr1 (pr1 cAB i)) (pr2 (dob cAB (S j)))) ⟧.
Proof.
intros i j.
apply (ProductOfArrows _ (PC _ _) (PC _ _) (identity (pr1 (dob cAB _))) (pr2 (dmor cAB (idpath _)))).
Defined.

Definition fun_lt (cAB : chain (product_precategory C C)) (K : C)
  (ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K) :
  forall i j, i < j ->
              C ⟦ ProductObject C (PC (pr1 (pr1 cAB i)) (pr2 (dob cAB j))),
                  ProductObject C (PC (pr1 (pr1 cAB j)) (pr2 (dob cAB j))) ⟧.
Proof.
intros i j hij.
generalize (test _ cAB i j hij).
simpl.
destruct j.
admit.
induction i.
intros.
admit.
intros.
assert (apa : i < S j).
  admit.
generalize (IHi apa).


Check (inc1 cAB K ccK (pred i) (S j)).
simple refine (_ ;; inc1 cAB K ccK (S i) _).
apply IHi.

Focus 1
-


destruct i.
simpl.
admit.

generalize (@dmor _ _ cAB j _ (idpath _)).
simpl.
unfold ProductObject in IHj; simpl in IHj.
simpl.



induction i.
destruct j.
admit.
simpl.
case Hij.



(* Lemma to construct ccAiB_K *)
Lemma temp (cAB : chain (product_precategory C C)) (K : C)
  (ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K)
  : ∀ i : nat, cocone (mapchain (constprod_functor1 PC (pr1 (pr1 cAB i))) (mapchain (pr2_functor C C) cAB)) K.
Proof.
intro i.
simple refine (mk_cocone _ _).
+ simpl; intro j.

unfold product_functor_ob; simpl.







induction i.
assert (f : C⟦ ProductObject C (PC (pr1 (pr1 cAB 0)) (pr2 (dob cAB j))), ProductObject C (PC (pr1 (pr1 cAB j)) (pr2 (dob cAB j))) ⟧).
admit.
apply (f ;; coconeIn ccK j).

induction j.
simpl.
apply (coconeIn ccK 0).
simpl.
unfold product_functor_ob; simpl.
induction j.

set (abi := coconeIn ccK i).
simpl in abi.
set (ab0 := coconeIn ccK 0).
simpl in ab0.

induction i.
- simple refine (mk_cocone _ _).
  simpl; intro i.
unfold product_functor_ob; simpl.
admit.
admit.
- simpl in *.
simple refine (mk_cocone _ _).
+ simpl; intro j.
unfold product_functor_ob; simpl.
set (abi := coconeIn ccK i).
simpl in abi.

Search ProductObject.
set (ai := ProductPr1 _ (PC (pr1 (dob cAB i)) (pr2 (dob cAB i)))).




Lemma omega_cocont_binproduct_functor : omega_cocont (binproduct_functor PC).
Proof.
intros cAB LM ccLM HccLM K ccK; simpl in *.
generalize (isColimCocone_pr2_functor _ _ hsC _ _ _ HccLM).
generalize (isColimCocone_pr1_functor _ _ hsC _ _ _ HccLM).
set (L := pr1 LM); set (M := pr2 LM).
set (cA := mapchain (pr1_functor C C) cAB).
set (cB := mapchain (pr2_functor C C) cAB).
intros HA HB.

(* Form the colimiting cocones of "A_i * B_0 -> A_i * B_1 -> ..." *)
simple refine (let HAiB : forall i, isColimCocone _ _ (mapcocone (constprod_functor1 PC (pr1 (pr1 cAB i)))
                                                      _ (cocone_pr2_functor C C _ LM ccLM)) := _ in _).
{ intro i.
  apply (omega_cocont_constprod_functor1 _ PC hsC hE (pr1 (pr1 cAB i)) _ _ _ HB).
}
fold cB in HAiB; fold M in HAiB; simpl in HAiB.

(* Turn HAiB into a ColimCocone: *)
simple refine (let CCAiB : forall i, ColimCocone (mapdiagram (constprod_functor1 PC (pr1 (pr1 cAB i))) cB) := _ in _).
{ intro i.
mkpair.
mkpair.
apply (((constprod_functor1 PC (pr1 (pr1 cAB i))) M)).
Focus 2.
apply (HAiB i).
}

generalize (omega_cocont_constprod_functor2 _ PC hsC hE M _ _ _ HA); intro HAiM.

(* Turn HAiM into a ColimCocone: *)
(* simple refine (let X : ColimCocone (mapdiagram (constprod_functor2 PC M) cA) := _ in _). *)
(* { *)
(*   mkpair. *)
(*   - mkpair. *)
(*     + apply (ProductObject _ (PC L M)). *)
(*     + apply (mapcocone (constprod_functor2 PC M) cA (cocone_pr1_functor C C cAB LM ccLM)). *)
(*   - apply HAiM. *)
(* } *)

simple refine (let ccAiB_K : forall i, cocone (mapchain (constprod_functor1 PC (pr1 (pr1 cAB i))) cB) K := _ in _).
{ simpl; intro i.

simple refine (mk_cocone _ _).
- simpl; intro n.
  admit.
- admit.
}

simple refine (let ccAiM_K : cocone (mapdiagram (constprod_functor2 PC M) cA) K := _ in _).
{
simple refine (mk_cocone _ _).
- simpl; intro i.
apply (colimArrow (CCAiB i) K (ccAiB_K i)).
- simpl.
intros m n e.
apply (colimArrowUnique (CCAiB m)).
simpl.
intros x.
admit.
}

mkpair.
- mkpair.
  + apply (colimArrow X K Y).
  + intro n.
    generalize (colimArrowCommutes X K Y n).
simpl.
unfold colimIn.
simpl.
unfold product_functor_mor.
unfold ProductOfArrows.
unfold ProductArrow.
simpl.
admit.
-
intro t.
apply subtypeEquality.
+ admit.
+
simpl.
apply (colimArrowUnique X K Y).
admit.
Admitted.

End binprod_functor.

Section rightkanextension.

Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.RightKanExtension.

Variables C D E : precategory.
Variables (K : functor C D).

(* Lemma foo : has_limits D -> GlobalRightKanExtensionExists K. *)

(* has_limits D *)
Lemma cocont_pre_composition_functor (hsD : has_homsets D) (hsE : has_homsets E) :
  is_cocont (pre_composition_functor _ _ E hsD hsE K).
Admitted. (* will be a simple consequence of foo *)

Lemma omega_cocont_pre_composition_functor (hsD : has_homsets D) (hsE : has_homsets E) :
  omega_cocont (pre_composition_functor _ _ E hsD hsE K).
Proof.
intros c L ccL.
apply cocont_pre_composition_functor.
Defined.

End rightkanextension.

Section lambdacalculus.


Definition option_functor : [HSET,HSET,has_homsets_HSET].
Proof.
apply coproduct_functor.
apply CoproductsHSET.
apply (constant_functor _ _ unitHSET).
apply functor_identity.
Defined.

(* TODO: package omega cocont functors *)
Definition LambdaFunctor : functor [HSET,HSET,has_homsets_HSET] [HSET,HSET,has_homsets_HSET].
Proof.
eapply sum_of_functors.
  apply (Coproducts_functor_precat _ _ CoproductsHSET).
  apply (constant_functor [HSET, HSET, has_homsets_HSET] [HSET, HSET, has_homsets_HSET] (functor_identity HSET)).
eapply sum_of_functors.
  apply (Coproducts_functor_precat _ _ CoproductsHSET).
  (* app *)
  eapply functor_composite.
    apply delta_functor.
    apply binproduct_functor.
    apply (Products_functor_precat _ _ ProductsHSET).
(* lam *)
apply (pre_composition_functor _ _ _ _ _ option_functor).
Defined.

(* Bad approach *)
(* Definition Lambda : functor [HSET,HSET,has_homsets_HSET] [HSET,HSET,has_homsets_HSET]. *)
(* Proof. *)
(* eapply functor_composite. *)
(*   apply delta_functor. *)
(* eapply functor_composite. *)
(*   eapply product_of_functors. *)
(*     apply functor_identity. *)
(*     apply delta_functor. *)
(* eapply functor_composite. *)
(*   eapply product_of_functors. *)
(*     apply (constant_functor [HSET, HSET, has_homsets_HSET] [HSET, HSET, has_homsets_HSET] (functor_identity HSET)). *)
(*     eapply product_of_functors. *)
(*       apply delta_functor. *)

Lemma omega_cocont_LambdaFunctor : omega_cocont LambdaFunctor.
Proof.
apply omega_cocont_sum_of_functors.
  apply (Products_functor_precat _ _ ProductsHSET).
  apply functor_category_has_homsets.
  apply functor_category_has_homsets.
  apply omega_cocont_constant_functor.
  apply functor_category_has_homsets.
apply omega_cocont_sum_of_functors.
  apply (Products_functor_precat _ _ ProductsHSET).
  apply functor_category_has_homsets.
  apply functor_category_has_homsets.
  apply omega_cocont_functor_composite.
  apply functor_category_has_homsets.
  apply omega_cocont_delta_functor.
  apply (Products_functor_precat _ _ ProductsHSET).
  apply functor_category_has_homsets.
  apply omega_cocont_binproduct_functor.
  apply functor_category_has_homsets.
apply omega_cocont_pre_composition_functor.
Defined.

End lambdacalculus.
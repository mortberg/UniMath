(**

Definition of multisorted binding signatures.

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.Foundations.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
(* Require Import UniMath.SubstitutionSystems.Notation. *)

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Section preamble.

Context {C D E : precategory} {hsE : has_homsets E}.

Lemma functor_swap : functor C [D,E,hsE] → functor D [C,E,hsE].
Proof.
intros F.
mkpair.
- mkpair.
  + intro d; simpl.
  { mkpair.
    - mkpair.
      + intro c.
        apply (pr1 (F c) d).
        + intros a b f; apply (# F f).
          - abstract (split;
            [ now intro x; simpl; rewrite (functor_id F)
            | now intros a b c f g; simpl; rewrite (functor_comp F)]).
  }
  + intros a b f; simpl.
  { mkpair.
    - intros x; apply (# (pr1 (F x)) f).
    - abstract (intros c d g; simpl; apply pathsinv0, nat_trans_ax).
  }
- abstract (split;
  [ intros d; simpl;
    apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ hsE) |]; simpl;
    apply funextsec; intro c; apply functor_id
  | intros a b c f g; simpl;
    apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ hsE) |]; simpl;
    apply funextsec; intro x; apply functor_comp ]).
Defined.

Lemma functor_cat_swap : functor [C, [D, E, hsE], functor_category_has_homsets _ _ hsE]
                                 [D, [C, E, hsE], functor_category_has_homsets _ _ hsE].
Proof.
mkpair.
- apply (tpair _ functor_swap); simpl.
  intros F G α.
  mkpair.
  + intros d; simpl.
    mkpair.
    * intro c; apply (α c).
    * abstract (intros a b f; apply (nat_trans_eq_pointwise (nat_trans_ax α _ _ f) d)).
  + abstract (intros a b f; simpl;
              apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ hsE) |]; simpl;
              apply funextsec; intro c; apply nat_trans_ax).
- abstract (split;
  [ intro F; simpl; apply subtypeEquality;
      [ intro x; apply isaprop_is_nat_trans, (functor_category_has_homsets _ _ hsE)|]; simpl;
    apply funextsec; intro d;
    now apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ hsE) |]
  | intros F G H α β; simpl in *; apply subtypeEquality;
      [ intro x; apply isaprop_is_nat_trans, (functor_category_has_homsets _ _ hsE)|]; simpl;
    apply funextsec; intro d;
    now apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ hsE) |]]).
Defined.

(* Lemma functor_assoc1 {C D E F : precategory} *)
(*   {hsD : has_homsets D } {hsE : has_homsets E} {hsF : has_homsets F} : *)
(*   functor [[C,D,hsD],E,hsE] F → functor [C,D,hsD] [E,F,hsF]. *)
(* Proof. *)
(* intros H. *)
(* mkpair. *)
(* - mkpair. *)
(*   + intro FCD; simpl. *)
(*   { mkpair. *)
(*     - mkpair. *)
(*       + intro e. *)
(*         set (temp := constant_functor [C, D, hsD] E e : [[C, D, hsD], E, hsE]). *)
(*         apply (H temp). *)
(* + intros a b f; simpl. *)


(*         set (temp := constant_functor [C, D, hsD] E e : [[C, D, hsD], E, hsE]). *)
(* simpl. *)
(*         apply (# H temp). *)

(* generalyze (# *)


(* apply *)
(* generalize (H FCD). *)

(*         apply (pr1 (F c) d). *)
(*         + intros a b f; apply (# F f). *)
(*           - abstract (split; *)
(*             [ now intro x; simpl; rewrite (functor_id F) *)
(*             | now intros a b c f g; simpl; rewrite (functor_comp F)]). *)
(*   } *)
(*   + intros a b f; simpl. *)
(*   { mkpair. *)
(*     - intros x; apply (# (pr1 (F x)) f). *)
(*     - abstract (intros c d g; simpl; apply pathsinv0, nat_trans_ax). *)
(*   } *)
(* - abstract (split; *)
(*   [ intros d; simpl; *)
(*     apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ hsE) |]; simpl; *)
(*     apply funextsec; intro c; apply functor_id *)
(*   | intros a b c f g; simpl; *)
(*     apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ hsE) |]; simpl; *)
(*     apply funextsec; intro x; apply functor_comp ]). *)
(* Defined. *)
(* Admitted. *)

(* Lemma functor_assoc2 {C D E F : precategory} *)
(*   {hsD : has_homsets D } {hsE : has_homsets E} {hsF : has_homsets F} : *)
(*   functor [C,D,hsD] [E,F,hsF] → functor [[C,D,hsD],E,hsE] F. *)
(* Admitted. *)

End preamble.


Section DiscreteCategory.

Variable (A : UU).

Definition DiscPrecat_data : precategory_data.
Proof.
mkpair.
- apply (A,,paths).
- mkpair; [ apply idpath | apply @pathscomp0 ].
Defined.

Definition is_precategory_DiscPrecat_data : is_precategory DiscPrecat_data.
Proof.
split; [split|]; trivial; intros.
+ apply pathscomp0rid.
+ apply path_assoc.
Qed.

Definition DiscPrecat : precategory :=
  (DiscPrecat_data,,is_precategory_DiscPrecat_data).

Lemma has_homsets_DiscPrecat (H : isofhlevel 3 A) : has_homsets DiscPrecat.
Proof.
intros ? ? ? ? ? ?; apply H.
Qed.

End DiscreteCategory.

(** * Definition of multisorted binding signatures *)
Section MBindingSig.

Variable (sort : UU).
Variable (eq : isdeceq sort). (* Can we eliminate this assumption? *)

Let sort_cat : precategory := DiscPrecat sort.
Let sortToHSET : precategory := [sort_cat,HSET,has_homsets_HSET].

Lemma has_homsets_sortToHSET : has_homsets sortToHSET.
Proof.
apply functor_category_has_homsets.
Qed.

Local Definition BinProductsSortToHSETToHSET : BinProducts [sortToHSET,HSET,has_homsets_HSET].
Proof.
apply (BinProducts_functor_precat _ _ BinProductsHSET).
Defined.

Local Definition CoproductsSortToHSET I (hI : isaset I) : Coproducts I sortToHSET.
Proof.
now apply Coproducts_functor_precat, Coproducts_HSET.
Defined.

Local Definition CoproductsSortToHSET2 I (hI : isaset I) :
  Coproducts I [sortToHSET, sortToHSET, has_homsets_sortToHSET].
Proof.
now apply Coproducts_functor_precat, CoproductsSortToHSET.
Defined.

Lemma functor_sort_cat (D : precategory) (f : sort → D) : functor sort_cat D.
Proof.
mkpair.
+ mkpair.
  - apply f.
  - intros s t []; apply identity.
+ abstract (now split; [intro|intros a b c [] []; simpl; rewrite id_left]).
Defined.

Definition mk_sortToHSET (f : sort → HSET) : sortToHSET.
Proof.
apply (functor_sort_cat _ f).
(* mkpair. *)
(* + apply (tpair _ f). *)
(*   intros a b hab; simpl; apply (transportf f hab). *)
(* + abstract (now split; [ intros a; apply idpath | intros a b c [] [] ]). *)
Defined.

(* Coercion sortToHsetToFun (s : sortToHSET) : sort → HSET := pr1 s. *)

Definition MSig : UU :=
  Π (s : sort), Σ (I : UU), I → list (list sort × sort).

Definition indices (M : MSig) : sort → UU := fun s => pr1 (M s).

Definition args (M : MSig) (s : sort) : indices M s → list (list sort × sort) :=
  pr2 (M s).


Local Notation "'1'" := (TerminalHSET).
Local Notation "a ⊕ b" := (BinCoproductObject _ (BinCoproductsHSET a b)) (at level 50).

(* Definition option : sort -> sortToHSET -> sortToHSET. *)
(* Proof. *)
(* intros s f. *)
(* apply mk_sortToHSET; intro t. *)
(* induction (eq s t) as [H|H]. *)
(* - apply (pr1 f t ⊕ 1). (* TODO: Can one add a coercion to make this look like sort -> Set *) *)
(* - apply (pr1 f t). *)
(* Defined. *)

Definition option_functor_data  (s : sort) : functor_data sortToHSET sortToHSET.
Proof.
mkpair.
+ intro f.
  apply mk_sortToHSET; intro t.
  induction (eq s t) as [H|H].
  * apply (pr1 f t ⊕ 1). (* TODO: Can one add a coercion to make this look like sort -> Set *)
  * apply (pr1 f t).
+ intros F G α.
  mkpair.
  * simpl; intro t.
    induction (eq s t) as [p|p]; simpl; clear p.
    { apply (coprodf (α t) (idfun unit)). }
    { apply α. }
  * abstract (intros t1 t2 []; apply idpath).
Defined.

Lemma is_functor_option_functor s : is_functor (option_functor_data s).
Proof.
split.
+ intros F; simpl in *.
  apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ has_homsets_HSET)|]; simpl.
  apply funextsec; intro t.
  induction (eq s t) as [p|p]; trivial; simpl; clear p.
  now apply funextfun; intros [].
+ intros F G H αFG αGH; simpl in *.
  apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ has_homsets_HSET)|]; simpl.
  apply funextsec; intro t.
  induction (eq s t) as [p|p]; trivial; simpl; clear p.
  now apply funextfun; intros [].
Qed.

Definition option_functor (s : sort) : functor sortToHSET sortToHSET :=
  tpair _ _ (is_functor_option_functor s).

Definition option_list (xs : list sort) : functor sortToHSET sortToHSET.
Proof.
use (foldr _ _ xs).
+ intros s F.
  apply (functor_composite (option_functor s) F).
+ apply functor_identity.
Defined.

(** This applies the sortToHSET to s *)
Definition sortToHSETToHSET (s : sort) : functor sortToHSET HSET.
Proof.
mkpair.
+ mkpair.
  - intro f; apply (pr1 f s).
  - simpl; intros a b f H; apply (f s H).
+ abstract (split;
    [ now intros f; apply funextsec
    | now intros f g h fg gh; apply funextsec; intro x ]).
Defined.

Definition endo_fun (X : functor sortToHSET sortToHSET) (a : list sort × sort) :
  functor sortToHSET HSET.
Proof.
set (O := functor_composite (option_list (pr1 a)) X).
apply (functor_composite O (sortToHSETToHSET (pr2 a))).
Defined.

Lemma endo_fun_functor (a : list sort × sort) :
  functor [sortToHSET,sortToHSET,has_homsets_sortToHSET]
          [sortToHSET,HSET,has_homsets_HSET].
Proof.
mkpair.
- mkpair.
  + intro X.
    apply (endo_fun X a).
  + intros F G α.
unfold endo_fun.
set (F1 := functor_composite (option_list (pr1 a)) F : functor sortToHSET sortToHSET).
set (F1' := functor_composite (option_list (pr1 a)) G : functor sortToHSET sortToHSET).
set (F2 := sortToHSETToHSET (pr2 a)).
apply (@hor_comp _ _ _ F1 F1' F2 F2).
admit.
apply nat_trans_id.
- admit.
Admitted.


Definition endo_funs (xs : list (list sort × sort)) (X : functor sortToHSET sortToHSET) :
  functor sortToHSET HSET.
Proof.
set (XS := map (endo_fun X) xs).
(* The output for the empty list *)
set (T := constant_functor sortToHSET HSET emptyHSET).
apply (foldr1 (fun F G => BinProductObject _ (BinProductsSortToHSETToHSET F G)) T XS).
Defined.

Definition endo_funs_functor (xs : list (list sort × sort)) :
  functor [sortToHSET,sortToHSET,has_homsets_sortToHSET]
          [sortToHSET,HSET,has_homsets_HSET].
Admitted.

(* Definition MSigToFunctor_helper *)
(*   (H : functor sortToHSET sortToHSET → sortToHSET → sort → HSET) : *)
(*  functor [sortToHSET, sortToHSET, has_homsets_sortToHSET] *)
(*          [sortToHSET, sortToHSET, has_homsets_sortToHSET]. *)

(* Lemma asdf : has_homsets [sortToHSET,HSET,has_homsets_HSET]. *)
(* Proof. *)
(* apply functor_category_has_homsets. *)
(* Qed. *)

(* Lemma lol (D : precategory) *)
(*   (H : functor sort_cat [D,HSET,has_homsets_HSET]) : *)
(*   functor D sortToHSET. *)
(* Proof. *)
(* mkpair. *)
(* - mkpair. *)
(* + intros f. *)
(*   apply mk_sortToHSET. *)
(*   intro s. *)
(*   apply (pr1 (H s) f). *)
(* + intros F G α. *)
(* mkpair. *)
(* * intros s. *)
(*   apply (# (pr1 (H s)) α). *)
(* * *)
(* intros s t []; clear t. *)
(* eapply pathscomp0. *)
(* apply (id_left (# (pr1 (H s)) α)). *)
(* apply pathsinv0. *)
(* apply (id_right (# (pr1 (H s)) α)). *)
(* - split. *)
(* + intro F. *)
(* apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ has_homsets_HSET)|]. *)
(* apply funextsec; intro s. *)
(* apply (functor_id ( (H s))). *)
(* + *)
(* intros F1 F2 F3 α12 α23. *)
(* apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ has_homsets_HSET)|]. *)
(* apply funextsec; intro s. *)
(* apply (functor_comp (H s)). *)
(* Admitted. (* Defined is very slow... *) *)


(* Definition lol2 *)
(*   (H : functor [[sortToHSET,sortToHSET,has_homsets_sortToHSET],sortToHSET,has_homsets_sortToHSET] *)
(*                sortToHSET) : *)
(*  functor [sortToHSET, sortToHSET, has_homsets_sortToHSET] *)
(*          [sortToHSET, sortToHSET, has_homsets_sortToHSET]. *)
(* Proof. *)
(* use functor_assoc1. *)
(* - apply has_homsets_sortToHSET. *)
(* - assumption. *)
(* Defined. *)

(* Definition MSigToFunctor_helper *)
(*   (* (H : functor sort_cat *) *)
(*   (*              [[sortToHSET,sortToHSET,has_homsets_sortToHSET], *) *)
(*   (*               [sortToHSET,HSET,has_homsets_HSET], *) *)
(*   (*               asdf]) : *) *)
(*  ( H : functor sort_cat *)
(*     [[[sortToHSET, sortToHSET, has_homsets_sortToHSET], sortToHSET, *)
(*      has_homsets_sortToHSET], HSET, has_homsets_HSET]) : *)
(*  functor [sortToHSET, sortToHSET, has_homsets_sortToHSET] *)
(*          [sortToHSET, sortToHSET, has_homsets_sortToHSET]. *)
(* Proof. *)

(* use functor_assoc1. *)
(* - apply has_homsets_sortToHSET. *)
(* - apply functor_swap. *)
(*   apply H. *)
(* Defined. *)
(* Admitted. *)

(* mkpair. *)
(* * mkpair. *)
(* { intro X. *)
(*   apply lol. *)
(*   mkpair. *)
(*   + mkpair. *)
(*   - intro s. *)
(*     apply (pr1 (H s) X). *)
(*   - intros s t []. *)
(*     set (XX :=  ((pr1 (H s)) X)). *)
(*     simpl in XX. *)
(*     apply (@nat_trans_id sortToHSET HSET XX). *)
(* + split. *)
(* - intro x. *)
(* simpl. *)
(* apply idpath. *)
(* - intros x y z [] []. *)

(*  simpl in *. *)
(* apply subtypeEquality; [intro xx; apply (isaprop_is_nat_trans _ _ has_homsets_HSET)|]. *)
(* apply funextsec; intro s. *)
(* apply idpath. *)
(* } *)
(* intros F G α. *)
(* admit. *)
(* * admit. *)
(* Admitted. *)

(* (C -> D) -> (E -> F) = ((C -> D) -> E) -> F *)
(* functor [C,D] [E,F] = functor [[C,D],E] F *)

(* Variables (A : precategory). *)

(* Lemma temp : has_homsets [A,HSET,has_homsets_HSET]. *)
(* Proof. *)
(* apply functor_category_has_homsets. *)
(* Qed. *)

(* Lemma temp2 : has_homsets [sortToHSET,HSET,has_homsets_HSET]. *)
(* Proof. *)
(* apply functor_category_has_homsets. *)
(* Qed. *)

Definition MSigToFunctor_helper (C D E F G : precategory)
  (hsD : has_homsets D) (hsG : has_homsets G)
  (H : functor F [[C,D,hsD],[E,G,hsG],functor_category_has_homsets _ _ hsG]) :
  functor [C,D,hsD] [E,[F,G,hsG],functor_category_has_homsets _ _ hsG] :=
    functor_composite (functor_swap H) functor_cat_swap.

Definition MSigToFunctor (M : MSig) :
  functor [sortToHSET,sortToHSET,has_homsets_sortToHSET]
          [sortToHSET,sortToHSET,has_homsets_sortToHSET].
Proof.
apply MSigToFunctor_helper.
apply functor_sort_cat.
intro s.
use (coproduct_of_functors (indices M s)).
+ admit.
+ intros y.
  apply (endo_funs_functor (args M s y)).
Admitted.

End MBindingSig.

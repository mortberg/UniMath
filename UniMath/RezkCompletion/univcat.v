Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.category_hset.
Require Import RezkCompletion.functors_transformations.
Require Import RezkCompletion.yoneda.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50, left associativity).
Local Notation "f ;; g"  := (compose f g) (at level 50, format "f  ;;  g").
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").

Section univcat.

Variable V : hSet.
Variable El : V -> hSet.

(* Definition of the V-precategory *)

Definition Vcat_mor a b := hset_fun_space (El a) (El b).

Definition Vcat_ob_mor : precategory_ob_mor :=
  tpair (fun ob : UU => ob -> ob -> UU) V Vcat_mor.

Definition Vcat_precategory_data : precategory_data := 
  precategory_data_pair Vcat_ob_mor (fun a (x : El a) => x)
    (fun a b c (f : El a -> El b) (g : El b -> El c) (x : El a) => g (f x)).

Lemma is_precategory_Vcat_precategory_data :
  is_precategory Vcat_precategory_data.
Proof. repeat split. Qed.

Definition Vcat_precategory : precategory := 
  tpair _ _ is_precategory_Vcat_precategory_data.

Notation Vcat := Vcat_precategory.

Lemma has_homsets_Vcat : has_homsets Vcat.
Proof. intros f g; apply isaset_set_fun_space. Qed.

(* V valued presheafs *)

Variable C : precategory.

Definition Vpresheaf := functor C^op Vcat.

Lemma isaset_Vpresheaf : isaset Vpresheaf.
Proof.
unfold Vpresheaf.
apply (isofhleveltotal2 2).
  apply isofhleveltotal2.
    apply impredfun.
    unfold Vcat; simpl; case V; simpl; trivial.
  intro F.
  repeat (apply impred; intros).
  case (El (F t0)); trivial.
intro F.
apply isasetaprop.
apply isaprop_is_functor.
apply has_homsets_Vcat.
Qed.

End univcat.
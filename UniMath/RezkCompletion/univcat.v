Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.category_hset.
Require Import RezkCompletion.functors_transformations.
Require Import RezkCompletion.yoneda.
(* Require Import RezkCompletion.whiskering. *)
Require Import RezkCompletion.slicecat.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50, left associativity).
Local Notation "f ;; g"  := (compose f g) (at level 50, format "f  ;;  g").
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").

(* Define the "V-precategory" and V valued presheafs *)
Section Vcat.

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

End Vcat.

Notation Vcat := Vcat_precategory.

Section functor_op.

Variable C D : precategory.
Variable F : functor C D.

Definition functor_op_data : functor_data C^op D^op :=
  tpair (fun F : C^op -> D^op => forall a b, a --> b -> F a --> F b) F
        (fun (a b : C) (f : b --> a) => functor_on_morphisms F f).

Lemma is_functor_functor_op : is_functor functor_op_data.
Proof. split; intros; [ apply (functor_id F) | apply (functor_comp F) ]. Qed.

Definition functor_op : functor C^op D^op := tpair _ _ is_functor_functor_op.

End functor_op.

(*  -we define a special presheaf U taking U(X) to be the set of V-valued presheaves *)
(* over C/X *)

(*  -we define \tilde{U}(X) to be the sigma type of one F,  V-presheaf over C/X *)
(* and one element  in F(X,1_X) *)

(*  -we prove that p : \tilde{U} -> U is a universe in the category of presheaves *)
Section test.

Variable V : hSet.
Variable El : V -> hSet.

Variable C : precategory.
Variable hsC : has_homsets C.

Local Notation "c / x" := (slice_precat c x hsC).

Lemma has_homsets_opp_precat : has_homsets C^op.
Proof. intros a b; apply hsC. Qed.

Definition U_fun (x : C^op) : HSET := 
  tpair _ (Vpresheaf V El (C / x)) (isaset_Vpresheaf V El _).

Definition U_func (x y : C) (f : y --> x) (F : functor (C / x)^op (Vcat V El)) :
  functor (C / y)^op (Vcat V El) := functor_composite _ _ _ (functor_op _ _ (slicecat_functor C hsC y x f)) F.

Definition U_functor_data : functor_data C^op HSET :=
 tpair (fun F : C^op -> HSET => forall a b, a --> b -> F a --> F b) U_fun
       (fun (a b : C^op) (f : a --> b) (H : Vpresheaf V El (C / a)) => U_func a b f H).

(* Is this true? *)
Lemma is_functor_U_functor : is_functor U_functor_data.
Admitted.

Definition U : functor C^op HSET := tpair _ _ is_functor_U_functor.

End test.
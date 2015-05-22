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

Section functor_op.

Variable C D : precategory.
Hypothesis hsD : has_homsets D.
Variable F : functor C D.

Definition functor_op_data : functor_data C^op D^op :=
  tpair (fun F : C^op -> D^op => forall a b, a --> b -> F a --> F b) F
        (fun (a b : C) (f : b --> a) => functor_on_morphisms F f).

Lemma is_functor_functor_op : is_functor functor_op_data.
Proof. split; intros; [ apply (functor_id F) | apply (functor_comp F) ]. Qed.

Definition functor_op : functor C^op D^op := tpair _ _ is_functor_functor_op.

Lemma has_homsets_op (hsC : has_homsets C) : has_homsets C^op.
Proof. intros a b; apply hsC. Qed.

(* Lemmas for definition of CAT *)
Lemma functor_identity_left : functor_composite C C D (functor_identity C) F = F.
Proof.
apply (functor_eq _ _ hsD); case F; clear F; intros F; case F; trivial.
Qed.

Lemma functor_identity_right : functor_composite C D D F (functor_identity D) = F.
Proof.
apply (functor_eq _ _ hsD); case F; clear F; intros F; case F; trivial.
Qed.

End functor_op.

Section functor_eqs.
  
Variable C : precategory.
Variable hsC : has_homsets C.

Local Notation "c / x" := (slice_precat c x hsC).

Lemma functor_op_identity : functor_op _ _ (functor_identity C) = functor_identity C^op.
Proof.
apply (functor_eq _ _ (has_homsets_op _ hsC)); trivial.
Qed.

End functor_eqs.

(* Define the "V-precategory" and V valued presheafs *)
Section Vcat.

Variable V : hSet.
Variable eps : V -> V -> hProp.

Variable funV : V -> V -> V.
Variable idV : V -> V.
Hypothesis id_funV : forall a, eps (idV a) (funV a a).

Variable compV : V -> V -> V.
Hypothesis comp_funV : forall b a c f g,
                         eps f (funV a b) -> eps g (funV b c) -> eps (compV f g) (funV a c).

(* Should these rules be untyped? *)
Hypothesis id_leftV : forall a f, compV (idV a) f = f.
Hypothesis id_rightV : forall f a, compV f (idV a) = f.
Hypothesis assocV : forall f g h, compV f (compV g h) = compV (compV f g) h.
(* Variable El : V -> hSet. *)

Lemma isaprop_eps (a b : V) : isaprop (eps a b).
Proof. case (eps a b); trivial. Qed.

Lemma isaset_eps (a : V) : isaset (total2 (fun (b : V) => eps b a)).
Proof.
apply (isofhleveltotal2 2).
  case V; trivial.
intro b; apply isasetaprop; apply isaprop_eps.
Qed.

Definition El (a : V) : hSet := tpair _ _ (isaset_eps a).

(* Definition of the V-precategory *)
Definition Vcat_mor a b := El (funV a b).

Definition Vcat_ob_mor : precategory_ob_mor :=
  tpair (fun ob : UU => ob -> ob -> UU) V Vcat_mor.

Definition Vcat_precategory_data : precategory_data :=
   (precategory_data_pair Vcat_ob_mor
      (fun x => tpair _ (idV x) (id_funV x))
      (fun x y z f g => tpair (fun b => eps b (funV x z)) _
                              (comp_funV _ _ _ _ _ (pr2 f) (pr2 g)))).

Lemma is_precategory_Vcat_precategory_data :
  is_precategory Vcat_precategory_data.
Proof.
repeat split; [intros a b f | intros a b f | intros a b c d f g h].
* destruct f.
  apply (total2_paths2_second_isaprop (id_leftV _ _) (isaprop_eps _ _)).
* destruct f.
  apply (total2_paths2_second_isaprop (id_rightV _ _) (isaprop_eps _ _)).
* destruct f; destruct g; destruct h.
  apply (total2_paths2_second_isaprop (assocV _ _ _) (isaprop_eps _ _)).
Qed.

Definition Vcat_precategory : precategory := 
  tpair _ _ is_precategory_Vcat_precategory_data.

Notation Vcat := Vcat_precategory.

Lemma has_homsets_Vcat : has_homsets Vcat.
Proof. intros f g; apply isaset_eps. Qed.

(* V valued presheafs *)

Definition Vpresheaf (C : precategory) := functor C^op Vcat.

Lemma isaset_Vpresheaf (C : precategory) : isaset (Vpresheaf C).
Proof.
unfold Vpresheaf.
apply (isofhleveltotal2 2).
  apply isofhleveltotal2.
    apply impredfun.
    unfold Vcat; simpl; case V; simpl; trivial.
  intro F.
  repeat (apply impred; intros).
  apply isaset_eps.
intro F.
apply isasetaprop.
apply isaprop_is_functor.
apply has_homsets_Vcat.
Qed.

Variable C : precategory.
Variable hsC : has_homsets C.

Local Notation "c / x" := (slice_precat c x hsC).

Definition U_fun (x : C^op) : HSET := 
  tpair _ (Vpresheaf (C / x)) (isaset_Vpresheaf (C / x)).

Definition U_func (x y : C) (f : y --> x) (F : functor (C / x)^op Vcat) :
  functor (C / y)^op Vcat :=
    functor_composite _ _ _ (functor_op _ _ (slicecat_functor C hsC y x f)) F.

Definition U_functor_data : functor_data C^op HSET :=
 tpair (fun F : C^op -> HSET => forall a b, a --> b -> F a --> F b) U_fun
       (fun (a b : C^op) (f : a --> b) (H : Vpresheaf (C / a)) => U_func a b f H).

Lemma is_functor_U_functor : is_functor U_functor_data.
Proof.
split.
intro a.
simpl.
apply funextfun; intro F.
unfold identity; simpl.
unfold U_func; simpl.
(* rewrite slicecat_functor_identity. *)
(* rewrite functor_op_identity. *)
(* simpl. *)
(* rewrite (functor_identity_left (C / a)^op Vcat (has_homsets_Vcat)). *)
(* apply idpath. *)
(* apply has_homsets_slice_precat. *)
admit.
simpl.
intros a b c f g.
simpl.
apply funextfun; intro Fv; simpl.
apply functor_eq.
admit.
simpl.

functor_composite_data
     (functor_op_data (C / c) (C / b) (slicecat_functor C hsC c b g))
     (functor_composite_data (functor_op_data (C / b) (C / a) (slicecat_functor C hsC b a f)) Fv)
Check (

     
        (functor_op_data (C / b) (C / a) (slicecat_functor C hsC b a f)) _).


Check (functor_composite_data
     (functor_op_data (C / c) (C / a) (slicecat_functor C hsC c a (f ;; g)))
     F).


case F.

simpl.

trivial.

Admitted.

Definition U : functor C^op HSET := tpair _ _ is_functor_U_functor.

End Vcat.

Notation Vcat := Vcat_precategory.


(*  -we define a special presheaf U taking U(X) to be the set of V-valued presheaves *)
(* over C/X *)

(*  -we define \tilde{U}(X) to be the sigma type of one F,  V-presheaf over C/X *)
(* and one element  in F(X,1_X) *)

(*  -we prove that p : \tilde{U} -> U is a universe in the category of presheaves *)
(* Section test. *)

(* Variable V : hSet. *)
(* Variable eps : V -> V -> hProp. *)
(* (* Variable El : V -> hSet. *) *)

(* Variable C : precategory. *)
(* Variable hsC : has_homsets C. *)

(* Local Notation "c / x" := (slice_precat c x hsC). *)

(* Lemma has_homsets_opp_precat : has_homsets C^op. *)
(* Proof. intros a b; apply hsC. Qed. *)

(* Definition U_fun (x : C^op) : HSET :=  *)
(*   tpair _ (Vpresheaf V eps (C / x)) (isaset_Vpresheaf V eps _). *)

(* Definition U_func (x y : C) (f : y --> x) (F : functor (C / x)^op (Vcat V El)) : *)
(*   functor (C / y)^op (Vcat V El) := functor_composite _ _ _ (functor_op _ _ (slicecat_functor C hsC y x f)) F. *)

(* Definition U_functor_data : functor_data C^op HSET := *)
(*  tpair (fun F : C^op -> HSET => forall a b, a --> b -> F a --> F b) U_fun *)
(*        (fun (a b : C^op) (f : a --> b) (H : Vpresheaf V El (C / a)) => U_func a b f H). *)

(* (* Is this true? *) *)
(* Lemma is_functor_U_functor : is_functor U_functor_data. *)
(* Admitted. *)

(* Definition U : functor C^op HSET := tpair _ _ is_functor_U_functor. *)

(* End test. *)
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.category_hset.
Require Import RezkCompletion.functors_transformations.
Require Import RezkCompletion.opp_precat.
Require Import RezkCompletion.slicecat.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50, left associativity).
Local Notation "f ;; g"  := (compose f g) (at level 50, format "f  ;;  g").
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").


Set Implicit Arguments.
Unset Strict Implicit.

Section presheaf.

Variable C : UU.
Variable El : C -> UU.

Record preshG : UU := pG {
  A : C -> UU;
  res I J : (El J -> El I) -> A I -> A J;
  resId I (u : A I) : res (fun i => i) u = u;
  resComp I J K (f : El J -> El I) (g : El K -> El J) (u : A I) :
            res (fun k => f (g k)) u = res g (res f u)
}.



End presheaf.

(*
preshG (C:U) (El:C->U) : U =
 (A : C -> U) *
 (res : (I J:C) -> (El J -> El I) -> A I -> A J) *
 (ref : (I:C) (u:A I) -> Id (A I) (res I I (\ (i:El I) -> i) u) u) *
 (I J K:C) (f:El J -> El I) (g:El K -> El J) (u:A I) -> 
         Id (A K) (res I K (\ (k:El K) -> f (g k)) u) (res J K g (res I J f u))

preshL (C:U) (El:C->U) (I:C) : U =
 (A : (J:C) (f:El J -> El I) -> U) *
 (res : (J K:C) (f:El J -> El I) (g:El K -> El J) -> A J f -> A K (\ (k:El K) -> f (g k))) *
 (ref : (J:C) (f:El J -> El I) (u : A J f) -> Id (A J f) (res J J f (\ (j:El J) -> j) u) u) *
 (J K L:C) (f:El J -> El I) (g:El K -> El J)(h:El L -> El K) (u:A J f) ->
 Id (A L (\ (l:El L) -> f (g (h l)))) 
    (res K L (\ (k:El K) -> f (g k)) h (res J K f g u))
    (res J L f (\ (l:El L) -> g (h l)) u)

test  (C:U) (El:C->U) (I J:C)(f:El J -> El I)
 (A : (J:C) (f:El J -> El I) -> U)
 (res : (J K:C) (f:El J -> El I) (g:El K -> El J) -> A J f -> A K (\ (k:El K) -> f (g k)))
 (ref : (J:C) (f:El J -> El I) (u : A J f) -> Id (A J f) (res J J f (\ (j:El J) -> j) u) u)
 (trans : (J K L:C) (f:El J -> El I) (g:El K -> El J)(h:El L -> El K) (u:A J f) ->
  Id (A L (\ (l:El L) -> f (g (h l)))) 
     (res K L (\ (k:El K) -> f (g k)) h (res J K f g u))
     (res J L f (\ (l:El L) -> g (h l)) u)) : preshL C El J =
 (A1,res1,ref1,trans1)
 where
  A1 (K:C) (g:El K -> El J) : U = A K (\ (k:El K) -> f (g k))
  res1 (K L : C) (g:El K -> El J) (h:El L -> El K) (u:A1 K g) : A1 L (\ (l:El L) -> g (h l)) =
    res K L (\ (k:El K) -> f (g k)) h u
  ref1  (K:C) (g:El K -> El J) (u:A1 K g) : Id (A1 K g) (res1 K K g (\ (k:El K) -> k) u) u =
     ref K (\ (k:El K) -> f (g k)) u
  trans1 (J1 K1 L1:C) (f1:El J1 -> El J) (g1:El K1 -> El J1)(h1:El L1 -> El K1) (u:A1 J1 f1) :
    Id (A1 L1 (\ (l:El L1) -> f1 (g1 (h1 l)))) 
       (res1 K1 L1 (\ (k:El K1) -> f1 (g1 k)) h1 (res1 J1 K1 f1 g1 u))
       (res1 J1 L1 f1 (\ (l:El L1) -> g1 (h1 l)) u) = trans J1 K1 L1 (\ (j:El J1) -> f (f1 j)) g1 h1 u

test1 (C:U) (El:C->U) (I J:C)(f:El J -> El I) (X : preshL C El I) : preshL C El J =
 test C El I J f X.1 X.2.1 X.2.2.1 X.2.2.2

test2 (C:U) (El:C->U) (I:C) (X : preshL C El I) : Id (preshL C El I) (test1 C El I I (\ (i:El I) -> i) X) X =
 refl (preshL C El I) X

test3 (C:U) (El:C->U) (I J K:C) (f:El J -> El I) (g : El K -> El J) (X : preshL C El I) : 
    Id (preshL C El K) (test1 C El J K g (test1 C El I J f X)) (test1 C El I K (\ (k:El K) -> f (g k)) X) =
 refl (preshL C El K) (test1 C El I K (\ (k:El K) -> f (g k)) X)

test4 (C:U) (El:C->U) : preshG C El =
 (A,res,ref,trans)
 where
  A : C -> U = preshL C El
  res : (I J:C) -> (El J -> El I) -> A I -> A J = test1 C El
  ref : (I:C) (u:A I) -> Id (A I) (res I I (\ (i:El I) -> i) u) u = test2 C El
  trans :  (I J K:C) (f:El J -> El I) (g:El K -> El J) (u:A I) -> 
            Id (A K) (res I K (\ (k:El K) -> f (g k)) u) (res J K g (res I J f u)) = test3 C El

mor (C:U)(El:C -> U)(Rel : (I:C) -> El I -> El I -> U) (J I :C) : U = 
 (f : El J -> El I) * 
 (y0 y1:El J) -> Rel J y0 y1 -> Rel I (f y0) (f y1)

compos  (C:U)(El:C -> U)(Rel : (I:C) -> El I -> El I -> U) (I J K:C)
        (g : mor C El Rel K J) (f:mor C El Rel J I) : mor C El Rel K I = 
 (h,h1)
 where
  h (z:El K) : El I = f.1 (g.1 z)
  h1 (z0 z1:El K) (rz:Rel K z0 z1) : Rel I (h z0) (h z1) = f.2 (g.1 z0) (g.1 z1) (g.2 z0 z1 rz)

id (C:U)(El:C -> U)(Rel : (I:C) -> El I -> El I -> U) (I:C) : mor C El Rel I I =
 (\ (i:El I) -> i,\ (i0 i1:El I) (h:Rel I i0 i1) -> h)

comIdL (C:U)(El:C -> U)(Rel : (I:C) -> El I -> El I -> U) (I J : C) (f:mor C El Rel J I) :
    Id (mor C El Rel J I) (compos C El Rel I J J (id C El Rel J) f) f =
 refl  (mor C El Rel J I) f

comIdR (C:U)(El:C -> U)(Rel : (I:C) -> El I -> El I -> U) (I J : C) (f:mor C El Rel J I) :
    Id (mor C El Rel J I) (compos C El Rel I I J f (id C El Rel I)) f = 
 refl  (mor C El Rel J I) f

composAssoc (C:U)(El:C -> U)(Rel : (I:C) -> El I -> El I -> U) (I J K L : C) 
        (f:mor C El Rel J I) (g:mor C El Rel K J) (h:mor C El Rel L K) :
 Id (mor C El Rel L I)
    (compos C El Rel I J L (compos C El Rel J K L h g) f)
    (compos C El Rel I K L h (compos C El Rel I J K g f)) =
  refl (mor C El Rel L I) (compos C El Rel I K L h (compos C El Rel I J K g f))
*)
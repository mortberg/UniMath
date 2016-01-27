Require Import UniMath.Foundations.Basics.Preamble.

Section opacify.

Definition pathscomp0 {X : UU} {a b c : X} (e1 : a = b) (e2 : b = c) : a = c.
Proof.
  intros. induction e1. apply e2.
Defined.

Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Definition pathsinv0 {X : UU} {a b : X} (e : a = b) : b = a.
Proof.
  intros. induction e. apply idpath.
Defined.

Notation "! p " := (pathsinv0 p) (at level 50).

Definition hfiber {X Y : UU}  (f : X -> Y) (y : Y) : UU := Σ x:X, f x = y.

Definition hfiberpair {X Y : UU} (f : X -> Y) {y : Y}
  (x : X) (e : f x = y) : hfiber f y :=
    tpair _ x e.

Definition maponpaths {T1 T2 : UU} (f : T1 -> T2) {t1 t2 : T1}
  (e: t1 = t2) : f t1 = f t2.
Proof.
  intros. induction e. apply idpath.
Defined.

Lemma hfibertriangle2 {X Y : UU} (f : X -> Y) {y : Y} (xe1 xe2: hfiber f y)
  (ee: pr1 xe1 = pr1 xe2) (eee: pr2 xe1 = maponpaths f ee @ (pr2 xe2)) :
    xe1 = xe2.
Proof.
  intros.
  induction xe1 as [t e1].
  induction xe2 as [t' e2].
  simpl in *.
  fold (hfiberpair f t e1).
  fold (hfiberpair f t' e2).
  induction ee.
  simpl in eee.
  apply (maponpaths (fun e: f t = y => hfiberpair f t e) eee).
Qed.

Definition homot {X : UU} {P : X -> UU} (f g : ∀ x : X, P x) :=
  ∀ x : X , f x = g x.

Notation "f ~ g" := (homot f g) (at level 70, no associativity).

Definition homothfiber1 {X Y : UU} (f g : X -> Y)
  (h : f ~ g) (y : Y) (xe : hfiber f y) : hfiber g y.
Proof.
  intros. induction xe as [x e].
  apply (hfiberpair g x (!(h x) @ e)).
Defined.

Definition homothfiber2 {X Y : UU} (f g : X -> Y)
  (h : f ~ g) (y : Y) (xe : hfiber g y) : hfiber f y.
Proof.
  intros. induction xe as [x e].
  apply (hfiberpair f x (h x @ e)).
Defined.

Definition homothfiberretr {X Y : UU} (f g : X -> Y)
  (h : f ~ g) (y : Y) (xe : hfiber g y) :
    homothfiber1 f g h y (homothfiber2 f g h y xe) = xe.
Proof.
  intros.
  induction xe as [x e].
  simpl.
  fold (hfiberpair g x e).
  set (xe1 := hfiberpair g x (! h x @ h x @ e)).
  set (xe2 := hfiberpair g x e).
  apply (hfibertriangle2 g xe1 xe2 (idpath _)).
  simpl.

  (* Now, a little lemma: *)
  assert (ee : ∀ a b c : Y, ∀ p : a = b, ∀ q : b = c,
    !p @ (p @ q) = q).
  { intros. induction p. induction q. apply idpath. }

  apply ee.
Qed.

Definition iscontr (T:UU) : UU := Σ cntr:T, ∀ t:T, t=cntr.

Lemma iscontrretract {X Y : UU} (p : X -> Y) (s : Y -> X)
  (eps : ∀ y : Y, p (s y) = y) (is : iscontr X) : iscontr Y.
Proof.
  intros.
  induction is as [x fe].
  split with (p x).
  intro t.
  apply (! (eps t) @ maponpaths p (fe (s t))).
Defined.

Lemma iscontrhfiberl2 {X Y : UU} (f g : X -> Y)
  (h : f ~ g) (y : Y) (is : iscontr (hfiber f y)) : iscontr (hfiber g y).
Proof.
  intros.
  set (a := homothfiber1 f g h y).
  set (b := homothfiber2 f g h y).
  set (eab := homothfiberretr f g h y).
  apply (iscontrretract a b eab is).
Defined.

Definition isweq {X Y : UU} (f : X -> Y) : UU :=
  ∀ y : Y, iscontr (hfiber f y).

Definition idfun (T : UU) := λ t:T, t.

Lemma idisweq (T : UU) : isweq (idfun T).
Proof.
  intros. unfold isweq. intro y.
  unfold iscontr.
  split with (tpair (fun (x : T) => idfun T x = y) y (idpath y)).
  intro t.
  induction t as [x e].
  induction e.
  apply idpath.
Defined.

Definition funcomp {X Y Z : UU} (f : X -> Y) (g : Y -> Z) := λ x, g (f x).

Notation "g ∘ f" := (funcomp f g) (at level 50, left associativity).

Definition hfibersgftog {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
  (xe : hfiber (g ∘ f) z) : hfiber g z :=
    hfiberpair g (f (pr1 xe)) (pr2 xe).

Definition pathssec1 {X Y : UU} (s : X -> Y) (p : Y -> X)
  (eps : ∀ (x : X) , p (s x) = x)
    (x : X) (y : Y) (e : s x = y) : x = p y.
Proof.
  intros.
  apply (pathscomp0 (! eps x)).
  apply (maponpaths p e).
Qed.

Definition constr1 {X : UU} (P : X -> UU) {x x' : X} (e : x = x') :
  Σ (f : P x -> P x'),
  Σ (ee : ∀ p : P x, tpair _ x p = tpair _ x' (f p)),
  ∀ (pp : P x),
    maponpaths pr1 (ee pp) = e.
Proof.
  intros. induction e.
  split with (idfun (P x)).
  split with (fun p : P x => idpath _).
  unfold maponpaths. simpl.
  intro. apply idpath.
Defined.

Definition transportf {X : UU} (P : X -> UU) {x x' : X}
  (e : x = x') : P x -> P x' := pr1 (constr1 P e).

Lemma total2_paths {A : UU} {B : A -> UU} {s s' : Σ x, B x}
    (p : pr1 s = pr1 s')
    (q : transportf B p (pr2 s) = pr2 s') : s = s'.
Proof.
  intros.
  induction s as [a b].
  induction s' as [a' b']; simpl in *.
  induction p.
  induction q.
  apply idpath.
Defined.

Lemma total2_paths2 {A : UU} {B : A -> UU} {a1 : A} {b1 : B a1}
  {a2 : A} {b2 : B a2} (p : a1 = a2)
    (q : transportf B p b1 = b2) : a1,,b1 = a2,,b2.
Proof.
  intros.
  apply (@total2_paths _ _
    (tpair (fun x => B x) a1 b1) (tpair (fun x => B x) a2 b2) p q).
Qed.

Lemma constr2 {X Y : UU} (f : X -> Y) (g : Y -> X)
  (efg: ∀ y : Y, f (g y) = y) (x0 : X) (xe : hfiber g x0) :
    Σ xe' : hfiber (g ∘ f) x0, xe = hfibersgftog f g x0 xe'.
Proof.
  intros.
  destruct xe as [y0 e].
  set (eint := pathssec1 _ _ efg _ _ e).
  set (ee := ! (maponpaths g eint) @ e).
  split with (hfiberpair (g ∘ f) x0 ee).
  unfold hfibersgftog.
  unfold hfiberpair.
  simpl.
  apply (total2_paths2 eint).
  induction eint.
  apply idpath.
Qed.

Lemma iscontrhfiberl1 {X Y : UU} (f : X -> Y) (g : Y -> X)
  (efg: ∀ y : Y, f (g y) = y) (x0 : X)
    (is : iscontr (hfiber (g ∘ f) x0)) : iscontr (hfiber g x0).
Proof.
  intros.
  set (f1 := hfibersgftog f g x0).
  set (g1 := fun (xe : hfiber g x0) => pr1 (constr2 f g efg x0 xe)).
  set (efg1 := fun (xe : hfiber g x0) => ! (pr2 (constr2 f g efg x0 xe))).
  apply (iscontrretract f1 g1 efg1).
  apply is.
Defined.

Theorem gradth {X Y : UU} (f : X -> Y) (g : Y -> X)
  (egf: ∀ x : X, g (f x) = x)
  (efg: ∀ y : Y, f (g y) = y) : isweq f.
Proof.
  intro y.
  apply (iscontrhfiberl1 g f egf y).
  assert (efg' : ∀ y : Y, y = f (g y)).
    abstract (intro y0; apply pathsinv0, (efg y0)).
  apply (iscontrhfiberl2 (idfun _) (f ∘ g) efg' y (idisweq Y y)).
Defined.

Definition weq (X Y : UU) : UU := Σ f:X->Y, isweq f.

Notation "X ≃ Y" := (weq X Y) (at level 80, no associativity) : type_scope.

Definition pr1weq {X Y : UU} := pr1 : X ≃ Y -> (X -> Y).
Coercion pr1weq : weq >-> Funclass.

Definition weqccontrhfiber {X Y : UU} (w : X ≃ Y) (y : Y) : hfiber w y.
Proof.
  intros. apply (pr1 (pr2 w y)).
Defined.

Definition weqccontrhfiber2 {X Y : UU} (w : X ≃ Y) (y : Y) :
  ∀ x : hfiber w y, x = weqccontrhfiber w y.
Proof.
  intros. unfold weqccontrhfiber. apply (pr2 (pr2 w y)).
Qed.

Definition invmap {X Y : UU} (w : weq X Y) : Y -> X :=
  fun (y : Y) => pr1 (weqccontrhfiber w y).

Definition test (A : UU) : isweq (idfun A) := gradth _ (idfun A) (fun x => idpath x) (fun x => idpath x).

Eval compute in test.

Definition testweq (A : UU) : weq A A := tpair _ _ (test A).

Eval compute in testweq nat 0.
Eval compute in invmap (testweq nat) 0.

Definition homotweqinvweq {X Y : UU} (w : X ≃ Y) :
  ∀ y : Y, w (invmap w y) = y.
Proof.
  intros.
  unfold invmap.
  apply (pr2 (weqccontrhfiber w y)).
Qed.

Definition homotinvweqweq0 {X Y : UU} (w : X ≃ Y) :
 ∀ x : X, x = invmap w (w x).
Proof.
  intros.
  unfold invmap.
  set (xe1 := weqccontrhfiber w (w x)).
  set (xe2 := hfiberpair w x (idpath (w x))).
  set (p := weqccontrhfiber2 w (w x) xe2).
  apply (maponpaths pr1 p).
Qed.

Definition homotinvweqweq {X Y : UU} (w : X ≃ Y) :
  ∀ x : X, invmap w (w x) = x :=
    fun (x : X) => ! (homotinvweqweq0 w x).

Corollary isweqinvmap {X Y : UU} (w : weq X Y) : isweq (invmap w).
Proof.
  intros.
  assert (efg : ∀ (y : Y), w (invmap w y) = y).
  apply homotweqinvweq.
  assert (egf : ∀ (x : X), invmap w (w x) = x).
  apply homotinvweqweq.
  apply (gradth _ _ efg egf).
Defined.

Time Eval compute in isweqinvmap.
(* Much faster! *)


Definition PathPair {A : UU} {B : A -> UU} (x y : Σ x, B x) :=
  Σ p : pr1 x = pr1 y, transportf _ p (pr2 x) = pr2 y.

Notation "a ≡ b" := (PathPair a b) (at level 70, no associativity) : type_scope.
(* the three horizontal lines are reminiscent of a path lying above a path in a fibration *)
(* use \equiv in agda input mode *)

Lemma base_paths {A : UU} {B : A -> UU}
  (a b : total2 B) : a = b -> pr1 a = pr1 b.
Proof.
  intros.
  apply maponpaths; assumption.
Defined.

Definition fiber_paths {A : UU} {B : A -> UU} {u v : Σ x, B x}
  (p : u = v) : transportf (fun x => B x) (base_paths _ _ p) (pr2 u) = pr2 v.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma total2_fiber_paths {A : UU} {B : A -> UU} {x y : Σ x, B x}
  (p : x = y) : total2_paths  _ (fiber_paths p) = p.
Proof.
  induction p.
  induction x.
  apply idpath.
Defined.

Lemma base_total2_paths {A : UU} {B : A -> UU} {x y : Σ x, B x}
  {p : pr1 x = pr1 y} (q : transportf _ p (pr2 x) = pr2 y) :
    (base_paths _ _ (total2_paths _ q)) = p.
Proof.
  induction x as [x H].
  induction y as [y K].
  simpl in *.
  induction p.
  induction q.
  apply idpath.
Defined.

Eval compute in base_total2_paths.

Lemma transportf_fiber_total2_paths {A : UU} (B : A -> UU)
  (x y : Σ x, B x)
    (p : pr1 x = pr1 y) (q : transportf _ p (pr2 x) = pr2 y) :
      transportf (fun p' : pr1 x = pr1 y => transportf _ p' (pr2 x) = pr2 y)
      (base_total2_paths q)  (fiber_paths (total2_paths _ q)) = q.
Proof.
  induction x as [x H].
  induction y as [y K].
  simpl in *.
  induction p.
  induction q.
  apply idpath.
Defined.

Eval compute in transportf_fiber_total2_paths.

Theorem total2_paths_equiv {A : UU} (B : A -> UU) (x y : Σ x, B x) :
  x = y  ≃  x ≡ y.
Proof.
  exists (fun (r : x = y) =>
            tpair (fun p : pr1 x = pr1 y => transportf _ p (pr2 x) = pr2 y)
              (base_paths _ _ r) (fiber_paths r)).
  apply (gradth _
    (fun (pq : Σ p : pr1 x = pr1 y, transportf _ p (pr2 x) = pr2 y) =>
       total2_paths (pr1 pq) (pr2 pq))).
  - intro p.
    apply total2_fiber_paths.
  - intros [p q]. simpl in *.
    apply (total2_paths2 (base_total2_paths q)).
    apply transportf_fiber_total2_paths.
Defined.

(* Time Eval compute in total2_paths_equiv. *)

End opacify.

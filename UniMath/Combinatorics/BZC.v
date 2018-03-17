(**** ZF structures satisfy the axioms BZC ****)

   (**  **)

(** Contents **)

(*

Contents of this file:

-Verification of the axioms of BZC (Zermelo set theory with choice, no replacement, and bounded (=no unbounded quanitifers) comprehension) for ZF structures.

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Combinatorics.WellOrderedSets.
Require Import UniMath.Combinatorics.OrderedSets.
Require Import UniMath.MoreFoundations.DecidablePropositions.
Require Import UniMath.MoreFoundations.Propositions.
Require Export UniMath.Combinatorics.ZFstructures.


(** We restrict to types with decidable equalities and translate some lemmas to this
    setting **)

Definition ZFSde : UU := preZFS.
                           (*∑ (x : preZFS), isdeceq x.*)
Definition pr1ZFSde (x : ZFSde) : hSet := pr111 x.
Coercion pr1ZFSde : ZFSde >-> hSet.



Definition isaset_ZFSde : isaset ZFSde.
Proof.
Admitted.

(*
Lemma isdeceq_Branch (T : preZFS) (x : T) : isdeceq (Branch T x).
Proof.
Admitted.
*)


Local Notation "T ↑ x" := (Branch T x)(at level 40).

Local Notation "x ⊏ y" := ((pr121 (pr111 _)) x y)(at level 50).


Definition Root (X : ZFSde) := pr122 (pr11 X).


Definition isapoint {X : ZFSde} (x : X) := ¬ (x = Root X).

Lemma isaprop_isapoint {X : ZFSde} (x : X) : isaprop (isapoint x).
Proof.
  apply impred.
  intros.
  apply isapropempty.
Qed.

Definition ZFSde_elementof (x y : ZFSde) := ∑ (a : y), (isapoint a) × (x = y ↑ a).

Lemma isaprop_ZFSde_elementof (X Y : ZFSde) : isaprop (ZFSde_elementof X Y).
Proof.
  apply invproofirrelevance.
  unfold isProofIrrelevant.
  intros z w.
  unfold ZFSde_elementof in z.
  unfold ZFSde_elementof in w.
  destruct z as [z [ ispp p]].
  destruct w as [w [ ispq q]].
  set (r := (! q) @ p).
  apply total2_paths_equiv in r.
  destruct r as [r ρ].
  Admitted.
  (*
  set (s := (pr2 Y w z r)).
  simpl in ρ.
  set (τ y := @isapropdirprod _ _ (isaprop_isapoint y) (isaset_ZFS X (Y ↑ y))).
  set (P := λ y : Y, (isapoint y × X = Y ↑ y) ,, τ y).
  apply (total2_paths_hProp_equiv P (z,, (ispp,, p)) (w,, (ispq,, q))).
  simpl.
  apply (! s).
Qed.
*)

Local Notation "x ∈ y" := (ZFSde_elementof x y)(at level 30).

(*
Theorem ZFS_univalence (X Y : ZFS) : (X = Y) ≃ (preZFS_iso X Y).
Proof.
  set (P := λ x, λ y, preZFS_univalence x y).
  set (Q := λ (x : preZFS), (hasuniquerepbranch x ,, isaprop_hasuniquerepbranch x)).
  exact (substructure_univalence _ _ P Q X Y).
Qed.*)

Theorem ZFSde_univalence (X Y : ZFSde) : (X = Y) ≃ (preZFS_iso X Y).
Proof.
  set (P := λ x, λ y, preZFS_univalence x y).
  exact (P X Y).
Qed.

(*
Definition ZFS_elementof_hProp (x y : ZFSde) : hProp :=
  (ZFS_elementof x y ,, isaprop_ZFS_elementof x y).

Local Notation "x ∈ y" := (ZFS_elementof_hProp x y)(at level 30).

Lemma LEM_isrigidiffissuperrigid (T : Tree) : LEM -> (isrigid T <-> issuperrigid T).
Proof.
  (*TODO*)
Admitted.

Lemma LEM_hasuniquerepbranch (x : preZFS) : LEM -> hasuniquerepbranch x.
Proof.
  (*TODO*)
Admitted.

Theorem LEM_weqpreZFSZFS : LEM -> preZFS ≃ ZFS.
Proof.
  (*TODO*)
Admitted.
*)

(*** Axiom of Extensionality ***)

Definition RZC_extensionality_statement : UU :=
  ∏ (x y : ZFSde), (∏ z : ZFSde, z ∈ x <-> z ∈ y) <-> x = y.

Lemma isaprop_RZC_extensionality : isaprop RZC_extensionality_statement.
Proof.
  repeat (apply impred ; intros).
  apply isapropdirprod.
  - apply impred. intros. apply isaset_ZFSde.
  - repeat (apply impred ; intros). apply isapropdirprod.
    -- apply impred. intros. apply isaprop_ZFSde_elementof.
    -- apply impred. intros. apply isaprop_ZFSde_elementof.
Qed.

Lemma ZFSisitselements (x : ZFSde) : (∑ (z : ZFSde), z ∈ x) = x.
Proof.
  apply univalence.
Admitted.

(* todo: upstream *)
Definition branch_elem (x : ZFSde) (a : x) (H : isapoint a) : (x ↑ a) ∈ x :=
 (a,,(H,,idpath _)).

Definition elem2elem (Heq : ∏ x : ZFSde, isdeceq x)
  (x y : ZFSde) (f : ∏ z : ZFSde, z ∈ x -> z ∈ y) : x → y.
Proof.
  intros a.
  induction (Heq x a (Root x)) as [_|Ha].
  { exact (Root y). }
  { exact (pr1 (f (x ↑ a) (branch_elem x a Ha))). }
Defined.

Lemma elem2elem_Root (Heq : ∏ x : ZFSde, isdeceq x)
  (x y : ZFSde) (f : ∏ z : ZFSde, z ∈ x -> z ∈ y) :
  elem2elem Heq x y f (Root x) = Root y.
Proof.
  now unfold elem2elem; induction (Heq x (Root x) (Root x)).
Qed.

(* todo: add a projection to avoid the pr1? *)
Lemma elem2elem_nonRoot (Heq : ∏ x : ZFSde, isdeceq x)
      (x y : ZFSde) (f : ∏ z : ZFSde, z ∈ x -> z ∈ y)
      (a : x) (Ha : isapoint a) :
  elem2elem Heq x y f a = pr1 (f (x ↑ a) (branch_elem _ _ Ha)).
Proof.
  unfold elem2elem.
  induction (Heq x a (Root x)) as [H1|H1]; simpl.
  - induction (transportf isapoint H1 Ha (idpath _)).
  - repeat apply maponpaths; apply isapropneg.
Qed.

(* todo: extract this from the structure *)
Lemma hasuniquerepbranch_eq (x : ZFSde) (a b : x) : x ↑ a = x ↑ b → a = b.
Admitted.

Lemma elem2elem_cancel (Heq : ∏ (x : ZFSde), isdeceq x) (x y : ZFSde)
      (f : ∏ z : ZFSde, z ∈ x -> z ∈ y)
      (g : ∏ z : ZFSde, z ∈ y -> z ∈ x) (a : x) :
  elem2elem Heq y x g (elem2elem Heq x y f a) = a.
Proof.
induction (Heq x a (Root x)) as [Hxa|Hxa].
- now rewrite Hxa, !elem2elem_Root.
- set (z := branch_elem _ _ Hxa).
  set (b := elem2elem Heq x y f a).
  assert (p : x ↑ a = y ↑ b).
  { unfold b.
    rewrite (elem2elem_nonRoot Heq x y f a Hxa).
    apply (f (x ↑ a) z). }
  unfold elem2elem.
  induction (Heq _ _ _) as [H1|H1]; simpl.
  + assert (Hb : isapoint b).
    { unfold b.
      rewrite (elem2elem_nonRoot Heq x y f a Hxa).
      apply (f (x ↑ a) z). }
    induction (Hb H1).
  + set (w := branch_elem _ _ H1 : (y ↑ b) ∈ y).
    set (c := pr1 (g (y ↑ b) w)).
    assert (q : y ↑ b = x ↑ c).
    { apply (g (y ↑ b) w). }
    set (pq := p @ q).
    apply (!hasuniquerepbranch_eq _ _ _ pq).
Qed.

Theorem RZC_extensionality (Heq : ∏ (x : ZFSde), isdeceq x) (x y : ZFSde) :
  (∏ z : ZFSde, z ∈ x <-> z ∈ y) <-> x = y.
Proof.
  split.
  - intros H.
    apply (invweq (ZFSde_univalence x y)).
    use tpair.
    + use weq_iso.
      * apply (elem2elem Heq x y (λ z, pr1 (H z))).
      * apply (elem2elem Heq y x (λ z, pr2 (H z))).
      * apply (elem2elem_cancel Heq).
      * apply (elem2elem_cancel Heq).
    + simpl. admit.
  - now intros p; induction p.
Admitted.

(*** Axiom of the Empty Set ***)

(** The [unit] with the obvious ZFS structure will be our empty set **)

Definition RZC_emptyset_statement := ∑ (x : ZFSde), ∏ (y : ZFSde), ¬ (y ∈ x).

Lemma isaprop_RZC_emptyset : isaprop RZC_emptyset_statement.
Proof.
  (*TODO*)
Admitted.

Definition hsingleton : hSet := ( fromUUtoType unit ,, isasetunit).

Definition htrue : hProp := ( fromUUtoType unit ,, isapropunit).

Lemma isTRRG_hsingleton : isTRR (hsingleton) (λ x, λ y, htrue) tt.
Proof.
  split.
  - unfold isrefl. intros. unfold htrue. split.
  - unfold istrans. simpl. split.
    -- intros. apply tt.
    -- unfold isaroot. intros. split.
Qed.

Definition unitTRRG : TRRGraph :=
  (hsingleton  ,, (λ x, λ y, htrue) ,, tt ,, isTRRG_hsingleton).

Lemma isatree_unitTRRG : isatree unitTRRG.
Proof.
  (*TODO*)
Admitted.

Definition unitTree := (unitTRRG ,, isatree_unitTRRG).

Lemma isapreZFS_unitTRRG : ispreZFS unitTree.
Proof.
  (*TODO*)
Admitted.

Definition preemptyset : preZFS := (unitTree ,, isapreZFS_unitTRRG).

(*
Lemma unitZFShasuniquerepbranch : hasuniquerepbranch unitpreZFS.
Proof.
  (*TODO*)
Admitted.
*)
(*
Definition preemptyset : ZFS := (unitpreZFS ,, unitZFShasuniquerepbranch).
*)

Lemma isdeceq_preemptyset : isdeceq preemptyset.
Proof.
  (*TODO*)
Admitted.

Definition emptyset : ZFSde := (preemptyset ,, isdeceq_preemptyset).

Theorem BZC_emptyset : ∑ (x : ZFSde), ∏ (y : ZFSde), ¬ (y ∈ x).
Proof.
  exists emptyset.
  intros y P.
  induction P as [p [q1 q2]].
  unfold isapoint in q1.
  unfold Root in q1.
  simpl in q1.
  clear q2.
  set (c := (pr2 iscontrunit p)).
  apply (q1 c).
Qed.


(*Axiom of Pairing*)

Definition RZC_pair_statement := ∏ (x y : ZFSde), ∑ (z : ZFSde), ∏ (t : ZFSde), t ∈ z <-> ((t = x) ⨿ (t = y)).

Lemma isaprop_RZC_pair : isaprop RZC_pair_statement.
Proof.
  (*TODO*)
Admitted.

Theorem RZC_pair : ∏ (x y : ZFSde), ∑ (z : ZFSde), ∏ (t : ZFSde), t ∈ z <-> ((t = x) ⨿ (t = y)).
Proof.
  (*TODO*)
Admitted.

(*Axiom of Union*)

Definition RZC_union_statement := ∏ (x : ZFSde), ∑ (u : ZFSde), ∏ (z : ZFSde), z ∈ u <-> ( ∑ t : ZFSde, z ∈ t × t ∈ x).

Lemma isaprop_RZC_union : isaprop RZC_union_statement.
Proof.
  (*TODO*)
Admitted.

Theorem RZC_union : ∏ (x : ZFSde), ∑ (u : ZFSde), ∏ (z : ZFSde), z ∈ u <-> ( ∑ t : ZFSde, z ∈ t × t ∈ x).
Proof.
  (*TODO*)
Admitted.


(*Axiom of Powerset*)

Definition ZFSde_subset (x y : ZFSde) := ∏ (z : ZFSde), z ∈ x → z ∈ y.

Local Notation "x ⊆ y" := (ZFSde_subset x y)(at level 90).

Definition RZC_poweset_statement := ∏ (x : ZFSde), ∑ (v : ZFSde), ∏ (t : ZFSde), t ∈ v <-> t ⊆ x.

Lemma isaprop_RZC_powerset : isaprop RZC_pair_statement.
Proof.
  (*TODO*)
Admitted.

Theorem RZC_powerset : ∏ (x : ZFSde), ∑ (v : ZFSde), ∏ (t : ZFSde), t ∈ v <-> t ⊆ x.
Proof.
  (*TODO*)
Admitted.

(*Axiom of Foundation*)

Definition RZC_poweset_statement := ∏ (x : ZFSde), ∑ (v : ZFSde), ∏ (t : ZFSde), t ∈ v <-> t ⊆ x.

Lemma isaprop_RZC_powerset : isaprop RZC_pair_statement.
Proof.
  (*TODO*)
Admitted.

Theorem RZC_powerset : ∏ (x : ZFSde), ∑ (v : ZFSde), ∏ (t : ZFSde), t ∈ v <-> t ⊆ x.
Proof.
  (*TODO*)
Admitted.


(*Axiom of Infinity*)


(*Axiom of Choice*)


(*Axiom of Comprehension*)

Definition ZF_comprehension_statement := ∏ (φ : ZFSde → hProp) (x : ZFSde), ∑ (s : ZFSde), ∏ (t : ZFSde), (s ⊆ x) × (t ∈ s <-> φ t).

(** REMARK: The below lemma requires propositional resizing if ZFSde is to remain in the same universe, which we want it to. So at this point, for this form of the comprehension axiom, propositional resizing will be used essentially. **)

Lemma isaprop_ZF_comprehension_statement : isaprop ZF_comprehension_statement.
Proof.
  (*TODO*)
Admitted.

Theorem ZF_comprehension : ∏ (φ : ZFSde → hProp) (x : ZFSde), ∑ (s : ZFSde), ∏ (t : ZFSde), (s ⊆ x) × (t ∈ s <-> φ t).
Proof.
  (*TODO*)
Admitted.


(*Axiom of Replacement*)

(* Unclear, yet, if this can work. If it does, then we get a lot more consistency strength, and there is no need for separation, which follows as a consequence. On the other hand, with replacement, we get full ZFC, which makes me skeptial that it can work.*)

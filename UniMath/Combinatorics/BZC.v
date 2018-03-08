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

Definition ZFSde : UU := ∑ (x : ZFS), isdeceq x.
Definition pr1ZFSde (x : ZFSde) : ZFS := pr1 x.
Coercion pr1ZFSde : ZFSde >-> ZFS.

Lemma isaset_ZFSde : isaset ZFSde.
Proof.
Admitted.

Theorem ZFS_univalence (X Y : ZFS) : (X = Y) ≃ (preZFS_iso X Y).
Proof.
  set (P := λ x, λ y, preZFS_univalence x y).
  set (Q := λ (x : preZFS), (hasuniquerepbranch x ,, isaprop_hasuniquerepbranch x)).
  exact (substructure_univalence _ _ P Q X Y).
Qed.

Theorem ZFSde_univalence (X Y : ZFSde) : (X = Y) ≃ (preZFS_iso X Y).
Proof.
  set (P := λ x, λ y, ZFS_univalence x y).
  set (Q := λ (x : ZFS), (isdeceq x ,, isapropisdeceq x)).
  exact (substructure_univalence _ _ P Q X Y).
Qed.

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

≅

(*** Axiom of Extensionality ***)

Definition RZC_extensionality_statement :=
  ∏ (x y : ZFSde), (∏ z : ZFSde, z ∈ x <-> z ∈ y) <-> x = y.

Lemma isaprop_RZC_extensionality : isaprop RZC_extensionality_statement.
Proof.
  repeat (apply impred ; intros).
  apply isapropdirprod.
  - apply impred. intros. apply isaset_ZFSde.
  - repeat (apply impred ; intros). apply isapropdirprod.
    -- apply impred. intros. apply isaprop_ZFS_elementof.
    -- apply impred. intros. apply isaprop_ZFS_elementof.
Qed.

Lemma ZFSisitselements (x : ZFSde) : (∑ (z : ZFSde), z ∈ x) = x.
Proof.
  apply univalence.
Admitted.


Theorem RZC_extensionality : ∏ (x y : ZFSde), (∏ z : ZFSde, z ∈ x <-> z ∈ y) <-> x = y.
Proof.
  intros.
  split.
  - intros.  admit.
  - intros p. induction p. intros. split.
    -- repeat (intros P ; apply P).
    -- repeat (intros P ; apply P).
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

Definition unitpreZFS := (unitTree ,, isapreZFS_unitTRRG).

Lemma unitZFShasuniquerepbranch : hasuniquerepbranch unitpreZFS.
Proof.
  (*TODO*)
Admitted.

Definition preemptyset : ZFS := (unitpreZFS ,, unitZFShasuniquerepbranch).

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

Definition RZC_pair_statement := ∏ (x y : ZF_Structures), ∑ (z : ZF_Structures), ∏ (t : ZF_Structures), t ∈ z <-> ((t = x) ⨿ (t = y)).

Lemma isaprop_RZC_pair : isaprop RZC_pair_statement.
Proof.
  (*TODO*)
Admitted.

Theorem RZC_pair : ∏ (x y : ZF_Structures), ∑ (z : ZF_Structures), ∏ (t : ZF_Structures), t ∈ z <-> ((t = x) ⨿ (t = y)).
Proof.
  (*TODO*)
Admitted.

(*Axiom of Union*)

Definition RZC_union_statement := ∏ (x : ZF_Structures), ∑ (u : ZF_Structures), ∏ (z : ZF_Structures), z ∈ u <-> ( ∑ t : ZF_Structures, z ∈ t × t ∈ x).

Lemma isaprop_RZC_union : isaprop RZC_union_statement.
Proof.
  (*TODO*)
Admitted.

Theorem RZC_union : ∏ (x : ZF_Structures), ∑ (u : ZF_Structures), ∏ (z : ZF_Structures), z ∈ u <-> ( ∑ t : ZF_Structures, z ∈ t × t ∈ x).
Proof.
  (*TODO*)
Admitted.


(*Axiom of Powerset*)

Definition ZFS_subset (x y : ZF_Structures) := ∏ (z : ZF_Structures), z ∈ x → z ∈ y.

Local Notation "x ⊆ y" := (ZFS_subset x y)(at level 90).

Definition RZC_poweset_statement := ∏ (x : ZF_Structures), ∑ (v : ZF_Structures), ∏ (t : ZF_Structures), t ∈ v <-> t ⊆ x.

Lemma isaprop_RZC_powerset : isaprop RZC_pair_statement.
Proof.
  (*TODO*)
Admitted.

Theorem RZC_powerset : ∏ (x : ZF_Structures), ∑ (v : ZF_Structures), ∏ (t : ZF_Structures), t ∈ v <-> t ⊆ x.
Proof.
  (*TODO*)
Admitted.

(*Axiom of Foundation*)


(*Axiom of Infinity*)


(*Axiom of Choice*)


(*Axiom of Bounded Separation*)


(*Axiom of Replacement*)

(* Unclear, yet, if this can work. If it does, then we get a lot more consistency strength, and there is no need for separation, which follows as a consequence.*)

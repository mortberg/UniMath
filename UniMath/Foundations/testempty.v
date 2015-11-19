Require Import UniMath.Foundations.NaturalNumbers.

Definition uneq m : hProp := hProppair (m != 0) (isapropneg _).

Definition X := Σ m:natset, uneq m.

Lemma s : isaset X.
Proof.
  apply (isofhleveltotal2 2).
  { apply setproperty. }
  { intro m. apply isofhlevelsnprop. apply propproperty. }
Defined.

Definition f : nat ≃ X.
Proof.
  refine (_,,_).
  { intro m. exists (S m). apply negpathssx0. }
  { intros [m uneq]. refine (_,,_).
    - refine (_,,_).
      + exact (m - 1).
      + apply subtypeEquality.
        * intro n. apply propproperty.
        * simpl. induction m as [|m _].
          { induction (uneq (idpath 0)). }
          { simpl. apply maponpaths, natminuseqn. }
    - intros [n eq]. apply subtypeEquality.
      + intro i. apply s.
      + simpl.
        assert (r := maponpaths pr1 eq); clear eq; simpl in r; clear uneq.
        induction r. simpl. apply pathsinv0, natminuseqn. }
Defined.

Definition x : X := f 2.

Goal invmap f x = 2. reflexivity. Qed.

Goal (homotinvweqweq f 2) = idpath 2.
  try reflexivity. (* reflexivity does not solve this goal as Coq is stuck *)
Abort.

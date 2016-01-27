Require Import UniMath.Foundations.Basics.PartD.

Time Eval compute in fromempty.
Time Eval compute in tounit.
Time Eval compute in termfun.
Time Eval compute in idfun.
Time Eval compute in funcomp.
Time Eval compute in funcomp_assoc.
Time Eval compute in curry.
Time Eval compute in uncurry.
Time Eval compute in uncurry_curry.
Time Eval compute in curry_uncurry.
Time Eval compute in iteration.
Time Eval compute in adjev.
Time Eval compute in adjev2.
Time Eval compute in dirprod.
Time Eval compute in dneganddnegl1.
Time Eval compute in logeq_both_false.
Time Eval compute in pathscomp0rid.
Time Eval compute in path_assoc.
Time Eval compute in dirprodeq.
Time Eval compute in maponpaths.
Time Eval compute in functtransportb.
Time Eval compute in total2_paths. (* relation to subtypeEquality??? *)
Time Eval compute in total2_paths_b.
Time Eval compute in total2_paths2.
Time Eval compute in iscontrretract.
Time Eval compute in idisweq.
Time Eval compute in homotweqinvweqweq.
Time Eval compute in pathsweq4.
Time Eval compute in isweqcontrtounit.
Time Eval compute in homothfiberretr.
Time Eval compute in isweqhomot.
Time Eval compute in gradth.
(* Finished transaction in 0.248 secs (0.218u,0.001s) (successful) *)
Time Eval compute in bijection_to_weq.
(* Finished transaction in 1.094 secs (0.759u,0.001s) (successful) *)
Time Eval compute in isweqinvmap.
(* Finished transaction in 30.941 secs (29.681u,0.045s) (successful) *)
Time Eval compute in wequnittocontr.
(* Finished transaction in 0.333 secs (0.3u,0.s) (successful) *)
Time Eval compute in isweqpathsinv0.
(* Finished transaction in 1.25 secs (0.631u,0.007s) (successful) *)

Time Eval compute in isweqtococonusf.
(* Finished transaction in 5.515 secs (4.732u,0.048s) (successful) *)

(* Do these ever terminate? *)
(* Time Eval compute in isweqmaponpaths. *)
(* Time Eval compute in total2_paths_equiv. *)
(* Time Eval compute in isweqonpathsincl. *)
(* Time Eval compute in subtypeEquality. *)

Definition test (A : UU) : isweq (idfun A) := gradth _ (idfun A) (fun x => idpath x) (fun x => idpath x).

Eval compute in test.
Time Eval compute in test.
Eval compute in idisweq.
Time Eval compute in idisweq.

Definition testweq (A : UU) : weq A A := tpair _ _ (test A).

Eval compute in testweq nat 0.
Eval compute in invmap (testweq nat) 0.

End opacify.

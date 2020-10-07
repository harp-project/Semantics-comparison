Require Export CE_Tests.

Import ListNotations.

Goal
  exists n res eff, | [], 0, small_example, [] | -p> | n , res, eff |.
Proof.
  unfold small_example.
  eexists. eexists. eexists.
  solve_pbos.
Qed.
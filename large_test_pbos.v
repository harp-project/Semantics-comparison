Require Export CE_Tests.

Import ListNotations.

Goal
  exists n res eff, | [], 0, large_example, [] | -p> | n , res, eff |.
Proof.
  unfold large_example.
  eexists. eexists. eexists.
  solve_pbos.
Qed.
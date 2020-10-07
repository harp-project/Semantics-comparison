Require Export CE_Tests.

Import ListNotations.

Goal
  exists n res eff, | [], 0, medium_example, [] | -p> | n , res, eff |.
Proof.
  unfold medium_example.
  eexists. eexists. eexists.
  solve_pbos.
Qed.
From CE Require Export Tests.

Import ListNotations.

Goal
  exists n res eff, | [], 0, small_example, [] | -e> | n , res, eff |.
Proof.
  unfold small_example.
  eexists. eexists. eexists.
  solve.
Qed.
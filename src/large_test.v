From CE Require Export Tests.

Import ListNotations.

Goal
  exists n res eff, | [], 0, large_example, [] | -e> | n , res, eff |.
Proof.
  unfold large_example.
  eexists. eexists. eexists.
  solve.
Qed.
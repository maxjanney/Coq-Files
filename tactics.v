From LF Require Export poly.

(* apply *)
Theorem sill1 : forall n m o p : nat,
  n = m ->
  [n;o] = [n;p] ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1. apply eq2.
Qed.

Theorem silly2 : forall n m o p : nat,
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.
Qed.

Theorem silly2z : forall n m : nat,
  (n,n) = (m,m) ->
  (forall q r : nat, (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.
Qed.

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 2 = true ->
  oddb 3 = true.
Proof.
  intros H1 H2.
  apply H1. apply H2.
Qed.




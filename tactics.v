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

Theorem silly2a : forall n m : nat,
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

Theorem silly3 : forall n : nat,
  true = (n =? 5) ->
  (S (S n)) =? 7 = true.
Proof.
  intros n H.
  symmetry. apply H.
Qed.

Theorem rev_exercise1 : forall l l' : list nat,
  l = rev l' -> l' = rev l.
Proof.
  intros. 
  rewrite H. symmetry. 
  apply rev_involutive.
Qed.

Example trans_eq_example : forall a b c d e f : nat,
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite <- eq2.
  reflexivity.
Qed.

Lemma trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite <- eq2. apply eq1.
Qed.

Example trans_eq_example' : forall a b c d e f : nat,
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.
Qed.

Example trans_eq_example'' : forall a b c d e f : nat,
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d]. apply eq1. apply eq2.
Qed.

Example trans_eq_exercise : forall n m o p : nat,
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  transitivity m. apply eq2. apply eq1.
Qed.

Theorem S_injective : forall n m : nat,
  S n = S m ->
  n = m.
Proof.
  intros n m H0.
  assert (H1: n = pred (S n)). { reflexivity. }
  rewrite -> H1. rewrite -> H0. reflexivity.
Qed.

Theorem S_injective' : forall n m : nat,
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. apply Hnm.
Qed.

Theorem injective_ex1 : forall n m o : nat,
  [n;m] = [o;o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2.
  reflexivity.
Qed.



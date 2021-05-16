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

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j H0 H1.
  injection H0 as H2 H3.
  rewrite H1 in H3. injection H3 as H4.
  rewrite H4. apply H2.
Qed.

Theorem eqb_0_l : forall n : nat,
  0 =? n = true -> n = 0.
Proof.
  destruct n.
  - reflexivity.
  - intros H. discriminate.
Qed.

Theorem discriminate_ex1 : forall n : nat,
  S n = 0 ->
  2 + 2 = 5.
Proof.
  intros. discriminate.
Qed.

Theorem discriminate_ex2 : forall n m : nat,
  false = true ->
  [n] = [m].
Proof.
  intros. discriminate.
Qed.

Example discriminate_ex3 : 
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros. discriminate.
Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Theorem eq_implies_succ_equal : forall n m : nat,
  n = m -> S n = S m.
Proof.
  intros n m. apply f_equal.
Qed.

Theorem eq_implies_succ_equal' : forall n m : nat,
  n = m -> S n = S m.
Proof.
  intros n m H. f_equal. apply H.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
  (S n) =? (S m) = b ->
  n =? m = b.
Proof.
  intros. simpl in H. apply H.
Qed.

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros h eq H.
  symmetry in H. apply eq in H.
  symmetry in H. apply H.
Qed.

Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. intros m eq. destruct m.
      + reflexivity.
      + discriminate.
  - simpl. intros m eq.
    destruct m.
      + discriminate.
      + apply f_equal. apply IHn'. simpl in eq.
        injection eq as goal. apply goal.
Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  induction n.
  - intros. destruct m.
    + reflexivity.
    + discriminate.
  - intros. destruct m.
    + discriminate.
    + apply f_equal. apply IHn. simpl in H.
      apply H.
Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  induction n.
  + intros. destruct m.
    - reflexivity.
    - discriminate.
  + simpl. intros. destruct m.
    - discriminate.
    - simpl in H. 
      rewrite <- plus_n_Sm in H.
      rewrite <- plus_n_Sm in H.
      injection H as H1. f_equal.
      apply IHn. apply H1.
Qed.




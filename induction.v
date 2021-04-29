From LF Require Export basics.

Theorem plus_n_O : forall n : nat,
  n = n + 0.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite <- IHn.
    reflexivity.
Qed.

Theorem minus_n_n : forall n : nat,
  minus n n = 0.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    apply IHn.
Qed.

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  induction n.
  - reflexivity.
  - simpl. apply IHn.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros.
  induction n.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Fixpoint double (n : nat) : nat :=
  match n with
  | O    => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n : nat,
  double n = n + n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. rewrite <- plus_n_Sm. reflexivity.
Qed.




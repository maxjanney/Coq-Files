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

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  induction n.
  - reflexivity.
  - rewrite -> IHn. simpl. rewrite -> negb_involutive. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  assert (H: p + n = n + p).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m.
  - rewrite <- mult_n_O. reflexivity.
  - rewrite <- mult_n_Sm.
    simpl. rewrite -> IHm. 
    rewrite -> plus_comm. reflexivity.
Qed.

Check leb.

Theorem leb_refl : forall n : nat,
  true = (n <=? n).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. apply IHn.
Qed.

Theorem zero_nbeq_S : forall n : nat,
  0 =? (S n) = false.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true ->
  (p + n) <=? (p + m) = true.
Proof.
  intros.
  induction p.
  - simpl. apply H.
  - simpl. apply IHp.
Qed.

Theorem S_nbeq_0 : forall n : nat,
  (S n) =? 0 = false.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_1_l : forall n : nat,
  1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite <- plus_n_O.
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros.
  destruct b.
  - simpl.
    destruct c.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros.
  induction p.
  - rewrite <- mult_n_O. rewrite <- mult_n_O. 
    rewrite <- mult_n_O. reflexivity.
  - rewrite <- mult_n_Sm. rewrite <- mult_n_Sm.
    rewrite <- mult_n_Sm. rewrite -> IHp.
    rewrite -> plus_swap. rewrite <- plus_assoc.
    rewrite -> plus_swap. rewrite -> plus_assoc. 
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. 
    rewrite -> mult_plus_distr_r.
    reflexivity.
Qed.

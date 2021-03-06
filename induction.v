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
  rewrite -> plus_assoc. rewrite -> plus_assoc.
  assert (H: n + m = m + n).
  { apply plus_comm. }
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

Theorem eqb_refl : forall n : nat,
  true = (n =? n).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - apply IHn.
Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> plus_assoc. rewrite -> plus_assoc.
  replace (n + m) with (m + n). reflexivity.
  apply plus_comm.
Qed.

Theorem succ_succ : forall n : nat,
  S n + S n = S (S (n + n)).
Proof.
  induction n.
  - reflexivity.
  - rewrite -> IHn.
    simpl. rewrite <- plus_n_Sm. 
    rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) =  S (bin_to_nat b).
Proof.
  intros.
  induction b.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite -> IHb.
    rewrite <- plus_n_O. rewrite <- plus_n_O.
    rewrite -> succ_succ. reflexivity.
Qed.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | O    => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n : nat,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite -> bin_to_nat_pres_incr.
    rewrite -> IHn. reflexivity.
Qed.

Definition double_bin (b : bin) : bin :=
  match b with
  | Z => Z
  | _ => B0 b
  end.

Fixpoint normalize (b : bin) : bin :=
  match b with
  | Z => Z
  | B0 b' => double_bin (normalize b')
  | B1 b' => incr (double_bin (normalize b'))
  end.

Lemma double_inc : forall b : bin,
  incr (incr (double_bin b)) = double_bin (incr b).
Proof.
  destruct b.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma nat_to_bin_double : forall n : nat,
  nat_to_bin (double n) = double_bin (nat_to_bin n).
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn.
    rewrite -> double_inc. reflexivity.
Qed.

Theorem bin_nat_bin : forall b : bin,
  nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  induction b.
  - reflexivity.
  - simpl. rewrite <- plus_n_O.
    rewrite <- double_plus. rewrite -> nat_to_bin_double.
    rewrite -> IHb. reflexivity.
  - simpl. rewrite <- plus_n_O.
    rewrite <- double_plus. rewrite -> nat_to_bin_double.
    rewrite -> IHb. reflexivity.
Qed.

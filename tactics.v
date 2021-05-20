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

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. 
  generalize dependent n.
  induction m.
  - simpl. intros n eq. destruct n.
    + reflexivity.
    + discriminate.
  - intros n eq. destruct n.
    + discriminate.
    + f_equal. apply IHm.
      injection eq as H. apply H.
Qed.

Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  induction n.
  + intros X l. destruct l.
    - reflexivity.
    - discriminate.
  + intros X l eq. destruct l.
    - discriminate.
    - simpl. apply IHn. 
      injection eq as H. apply H.
Qed.

Definition square (n : nat) : nat :=
  n * n.

Lemma square_mult : forall n m,
  square (n * m) = square n * square m.
Proof.
  intros n m. unfold square. 
  rewrite mult_assoc. rewrite mult_assoc.
  assert (H: n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H. reflexivity.
Qed.

Definition foo (x : nat) := 5.

Fact silly_fact_1 : forall m,
  foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m. reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2' : forall m, 
  bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m. unfold bar.
  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if n=? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall n : nat,
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
  - reflexivity.
  - destruct (n =? 5) eqn:E2.
    + reflexivity.
    + reflexivity.
Qed.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l.
  - intros. simpl in H. injection H as eq1 eq2.
    rewrite <- eq1. rewrite <- eq2. reflexivity.
  - destruct x. simpl. destruct (split l). intros.
    injection H as H1 H2. rewrite <- H1. rewrite <- H2.
    simpl. assert (H3: combine x0 y0 = l). 
           { apply IHl. reflexivity. }
    rewrite H3. reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n=? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd : forall n : nat,
  sillyfun1 n = true ->
  oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heq3. apply eqb_true in Heq3.
  - rewrite Heq3. reflexivity.
  - destruct (n =? 5) eqn:Heq4.
    + apply eqb_true in Heq4. 
      rewrite Heq4. reflexivity.
    + discriminate.
Qed.

Theorem bool_fn_applied_thrice :
  forall (b : bool) (f : bool -> bool),
  f (f (f b)) = f b.
Proof.
  intros b f. destruct b.
  - destruct (f true) eqn:Heq1.
    + rewrite Heq1. apply Heq1.
    + destruct (f false) eqn:Heq2.
      * apply Heq1.
      * apply Heq2.
  - destruct (f false) eqn:Heq1.
    + destruct (f true) eqn:Heq2.
      * apply Heq2.
      * apply Heq1.
    + rewrite Heq1. apply Heq1.
Qed.

Theorem eqb_sym : forall n m : nat,
  (n =? m) = (m =? n).
Proof.
  induction n.
  - destruct m.
    + reflexivity.
    + reflexivity.
  - destruct m.
    + reflexivity.
    + simpl. apply IHn.
Qed.

Lemma obvious : forall n,
  (n =? n) = true.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. apply IHn.
Qed.

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p eq1 eq2.
  apply eqb_true in eq1.
  apply eqb_true in eq2.
  rewrite eq1. rewrite eq2.
  apply obvious.
Qed.

Definition split_combine_statement : Prop :=
  forall (X Y : Type) (l1 : list X) (l2 : list Y),
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l1. induction l1.
  - intros. simpl. destruct l2.
    + reflexivity.
    + discriminate.
  - intros. destruct l2.
    * simpl. inversion H.
    * simpl. rewrite IHl1.
      + reflexivity.
      + injection H as H1.
        apply H1.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool) 
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
  intros. induction l.
  - discriminate.
  - simpl in H. destruct test eqn:Heq1.
    + injection H as H1 H2. rewrite <- H1. apply Heq1.
    + apply IHl in H. apply H.
Qed.

Fixpoint forallb {X} (test: X -> bool) (l: list X): bool :=
  match l with
  | [] => true
  | h :: t => test h && forallb test t
  end.

Fixpoint existsb {X} (test: X -> bool) (l: list X): bool :=
  match l with
  | [] => false
  | h :: t => test h || existsb test t
  end.

Definition existsb' {X} (test: X -> bool) (l: list X): bool :=
  negb (forallb (fun h => negb (test h)) l).

Theorem existsb_existsb' : forall (X: Type) (f: X -> bool) (l: list X),
  existsb f l = existsb' f l.
Proof.
  intros. unfold existsb'. 
  induction l.
  - reflexivity.
  - simpl. destruct f.
    + reflexivity.
    + simpl. rewrite IHl. reflexivity.
Qed.

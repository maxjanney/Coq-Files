Set Warnings "-notation-overridden,-parsing".
From LF Require Export tactics.

Definition injective {X Y} (f: X -> Y): Prop :=
  forall a b: X, f a = f b -> a = b.

Theorem succ_inj : injective S.
Proof.
  intros a b H.
  injection H as H1. apply H1.
Qed.

Example and_example: 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split. reflexivity. reflexivity.
Qed.

Lemma and_intro : forall A B: Prop, 
  A -> B -> A -> A /\ B.
Proof.
  intros. split. 
  - apply H.
  - apply H0.
Qed.

Example and_exercise: forall n m: nat,
  n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H. destruct n.
  - simpl in H. split.
    + reflexivity.
    + apply H.
  - inversion H.
Qed.

Lemma and_example2: forall n m: nat,
  n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm. 
  reflexivity.
Qed.

Lemma and_example3: forall n m: nat, 
  n + m = 0 -> n * m = 0.
Proof.
  intros n m H. 
  apply and_exercise in H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q: Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP _]. apply HP.
Qed.

Lemma proj2 : forall P Q: Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [_ HQ]. apply HQ.
Qed.

Theorem and_commut: forall P Q: Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ]. split.
  apply HQ. apply HP.
Qed.

Theorem and_assoc: forall P Q R: Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Lemma eq_mult_0: forall n m: nat,
  n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. apply mult_0_r.
Qed.

Lemma or_intro_l : forall A B: Prop,
  A -> A \/ B.
Proof.
  intros A B HA.
  left. apply HA.
Qed.

Lemma zero_or_succ: forall n: nat,
  n = 0 \/ n = S (pred n).
Proof.
  destruct n.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Module MyNot.

Definition not (P: Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

End MyNot.

Theorem ex_false_quodlibet: forall P: Prop,
  False -> P.
Proof.
  intros P H.
  destruct H.
Qed.

Fact not_implies_our_not: forall P: Prop,
  ~P -> (forall Q: Prop, P -> Q).
Proof.
  intros. destruct H. apply H0.
Qed.

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one: 0 <> 1.
Proof.
  unfold not. intros. discriminate.
Qed.

Theorem not_false: ~False.
Proof.
  unfold not. intros H. apply H.
Qed.

Theorem contradiction_implies_anything: forall P Q: Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNP].
  unfold not in HNP. destruct HNP.
  apply HP.
Qed.

Theorem double_neg: forall P: Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not.
  intros G. apply G.
  apply H.
Qed.

Theorem contrapositive: forall P Q: Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H. unfold not. intros HNQ HP. 
  apply HNQ. apply H. apply HP.
Qed.

Theorem not_both_true_and_false: forall P: Prop,
  ~(P /\ ~P).
Proof.
  unfold not. intros P [HP HNP].
  destruct HNP. apply HP.
Qed.

Theorem not_true_is_false: forall b: bool,
  b <> true -> b = false.
Proof.
  intros. destruct b.
  - unfold not in H.
    destruct H. reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false': forall b: bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    exfalso. apply H.
    reflexivity.
  - reflexivity.
Qed.

Module MyIff.

Definition iff (P Q: Prop) :=
  (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym: forall P Q: Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [PIQ QIP].
  split.
  - apply QIP.
  - apply PIQ.
Qed.

Lemma not_true_iff_false: forall b: bool,
  b <> true <-> b = false.
Proof.
  intros. split.
  - apply not_true_is_false.
  - intros. rewrite H. unfold not. 
    intros. discriminate H0.
Qed.

Theorem or_distributes_over_and: forall P Q R: Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros. split.
  - intros [HP | [HQ HR]].
    + split.
      * left. apply HP.
      * left. apply HP.
    + split.
      * right. apply HQ.
      * right. apply HR.
  - intros [[HP | HQ] [HP' | HR]].
    + left. apply HP.
    + left. apply HP.
    + left. apply HP'.
    + right. split.
      * apply HQ.
      * apply HR.
Qed.

Lemma mult_eq_0: forall n m,
  n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m. destruct n.
  - intros _. left. reflexivity.
  - destruct m.
    + right. reflexivity.
    + intros H. discriminate.
Qed.

Lemma mult_0: forall n m,
  n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply eq_mult_0.
Qed.

Theorem or_assoc: forall P Q R: Prop,
  P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [HP | [HQ | HR]].
    + left. left. apply HP.
    + left. right. apply HQ.
    + right. apply HR.
  - intros [[HP | HQ] | HR].
    + left. apply HP.
    + right. left. apply HQ.
    + right. right. apply HR.
Qed.

Definition even x := exists n: nat,
  x = double n.

Lemma four_is_even: even 4.
Proof.
  unfold even. exists 2. reflexivity.
Qed.

Theorem exists_example_2: forall n: nat,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm]. 
  exists (2 + m).
  apply Hm.
Qed.

Theorem dist_not_exists: forall (X: Type) (P: X -> Prop),
  (forall x, P x) -> ~(exists x, ~P x).
Proof.
  intros. unfold not. intros [x NP].
  destruct NP. apply H.
Qed.

Theorem dist_exists_or: forall (X: Type) (P Q: X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. unfold iff. split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ.
Qed.

Fixpoint In {X} (x: X) (l: list X): Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1: In 4 [1;2;3;4;5].
Proof.
  simpl.
  right. right. right. left. reflexivity.
Qed.

Example In_example_2: forall n,
  In n [2;4] ->
  exists n', n = 2 * n'.
Proof.
  simpl. intros n [HN2 | [HN4 | []]].
  - exists 1. rewrite <- HN2. reflexivity.
  - exists 2. rewrite <- HN4. reflexivity.
Qed.

Theorem In_map: 
  forall (A B: Type) (f: A -> B) (l: list A) (x: A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x. induction l.
  - simpl. intros H. apply H.
  - simpl. intros [H1 | H2].
    + rewrite H1. left. reflexivity.
    + right. apply IHl. apply H2.
Qed.

Theorem In_map_iff:
  forall (A B: Type) (f: A -> B) (l: list A) (y: B),
  In y (map f l) <->
  exists x, f x = y /\ In x l.
Proof.
  intros. unfold iff. split.
  induction l as [| a xs].
  - intros [].
  - simpl. intros [L | R].
    + exists a. split.
      * apply L.
      * left. reflexivity.
    + apply IHxs in R as [x [L R]].
      exists x. split.
      * apply L.
      * right. apply R.
  - intros [x [L R]]. rewrite <- L.
    apply In_map. apply R.
Qed.

Theorem In_app_iff: forall A l l' (a: A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros. split.
  - induction l.
    + intros. right. apply H.
    + simpl. intros [L | R].
      * left. left. apply L.
      * apply IHl in R as [F | I].
        { left. right. apply F. }
        { right. apply I. }
  - induction l. simpl.
    + intros [[] | R]. apply R.
    + simpl. intros [[F | I] | R].
      * left. apply F.
      * right. apply IHl. left. apply I.
      * right. apply IHl. right. apply R.
Qed.

Fixpoint All {T} (P: T -> Prop) (l: list T): Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.

Theorem All_In: 
  forall T (P: T -> Prop) (l: list T),
  (forall x, In x l -> P x) <->
  All P l.
Proof.
  intros T P l. unfold iff. split.
  + induction l.
    - reflexivity.
    - intros. simpl. split.
      * apply H. simpl. left. reflexivity.
      * apply IHl. intros. apply H. 
        simpl. right. apply H0.
  + induction l.
    - intros _ _ [].
    - intros. simpl in H. simpl in H0.
      * destruct H as [L R]. destruct H0 as [H1 | H2].
        rewrite <- H1. apply L.
        apply IHl. apply R. apply H2.
Qed.

Definition combine_odd_even (Podd Peven: nat -> Prop): nat -> Prop :=
  fun n => if oddb n then Podd n else Peven n.

Theorem combine_odd_even_intro:
  forall (Podd Peven: nat -> Prop) (n: nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros O E n H1 H2. induction n.
  - unfold combine_odd_even. 
    simpl. apply H2. reflexivity.
  - unfold combine_odd_even. destruct (oddb (S n)).
    + apply H1. reflexivity.
    + apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd:
  forall (Podd Peven: nat -> Prop) (n: nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros. unfold combine_odd_even in H.
  rewrite H0 in H. apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven: nat -> Prop) (n: nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros . unfold combine_odd_even in H.
  rewrite H0 in H. apply H.
Qed.








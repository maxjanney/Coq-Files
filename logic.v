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

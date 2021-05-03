From LF Require Export induction.
Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x _ => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair _ y => y
  end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) :=
  match p with
  | (x,_) => x
  end.

Definition snd' (p : natprod) :=
  match p with
  | (_,y) => y
  end.

Definition swap_pair (p : natprod) :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall n m : nat,
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing : forall p : natprod,
  p = (fst p, snd p).
Proof.
  intros. destruct p. 
  reflexivity.
Qed.

Theorem snd_fst_is_swap : forall p : natprod,
  (snd p, fst p) = swap_pair p.
Proof.
  destruct p. reflexivity.
Qed.

End NatList.
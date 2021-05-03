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

Theorem fst_swap_is_snd : forall p : natprod,
  fst (swap_pair p) = snd p.
Proof.
  destruct p. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | [] => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | [] => l2
  | h :: t => h :: app t l2
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | [] => default
  | h :: _ => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | [] => []
  | _ :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | [] => []
  | O :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.

Example test_nonzeros: 
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => 
    if (oddb h)
      then h :: oddmembers t
      else oddmembers t
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (xs : natlist) : nat :=
  length (oddmembers xs).

Fixpoint countoddmembers' (l : natlist) : nat :=
  match l with
  | [] => O
  | h :: t => 
    if (oddb h) 
      then S (countoddmembers' t) 
      else countoddmembers' t
  end.

Example test_countoddmembers1:
  countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

(*
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | [] => l2
  | h :: t => h :: alternate l2 t
  end.
*)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | [] => O
  | h :: t => 
    if (v =? h) then S (count v t) 
                else count v t
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
  app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
  v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool :=
  negb (count v s =? O).

Fixpoint member' (v : nat) (s : bag) : bool :=
  match s with
  | [] => false
  | h :: t => 
    if (h =? v)
      then true
      else member' v t
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

End NatList.
From LF Require Export induction.
Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x _ => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair _ y => y
  end.

Notation "( x , y )" := (pair x y).

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

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

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

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | [] => []
  | O :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => 
    if (oddb h)
      then h :: oddmembers t
      else oddmembers t
  end.

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

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
  end.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | [] => O
  | h :: t => 
    if (v =? h) 
      then S (count v t) 
      else count v t
  end.

Definition sum : bag -> bag -> bag :=
  app.

Definition add (v : nat) (s : bag) : bag :=
  v :: s.

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

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | [] => s
  | h :: t => 
      if (h =? v)
        then t
        else h :: remove_one v t
  end.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
  | [] => s
  | h :: t =>
    if (h =? v)
      then remove_all v t
      else h :: remove_all v t
  end.

Fixpoint subset (s1 s2 : bag) : bool :=
  match s1 with
  | [] => true
  | h :: t => 
    if (member h s2)
      then subset t (remove_one h s2)
      else false
  end.

Lemma eq_reflexive : forall n : nat,
  (n =? n) = true.
Proof.
  induction n.
  - reflexivity.
  - simpl. apply IHn.
Qed.

Theorem add_inc_count : forall (s : bag) (n : nat),
  count n (add n s) = S (count n s).
Proof.
  intros. simpl.
  rewrite -> eq_reflexive. 
  reflexivity.
Qed.

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. simpl. reflexivity. Qed.

Theorem tl_length_pred : forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  destruct l as [| n l'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Fixpoint rev (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => rev t ++ [h]
  end.

Lemma app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite -> IHl1. 
    reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'.
    rewrite plus_comm. apply plus_1_l.
Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite -> IHl.
    reflexivity.
Qed.

Theorem rev_app_distr : forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1.
  - simpl. rewrite -> app_nil_r.
    reflexivity.
  - simpl. rewrite -> IHl1. 
    apply app_assoc.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite -> rev_app_distr.
    simpl. rewrite -> IHl.
    reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  rewrite -> app_assoc. 
  rewrite -> app_assoc. 
  reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1.
  - reflexivity.
  - simpl. rewrite -> IHl1.
    destruct n.
      + reflexivity.
      + reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | [], [] => true
  | _ :: _, [] => false
  | [], _ :: _ => false
  | h1 :: t1, h2 :: t2 =>
    if (h1 =? h2)
      then eqblist t1 t2
      else false
  end.

Theorem eqblist_refl : forall l : natlist,
  eqblist l l = true.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite -> eq_reflexive.
    apply IHl.
Qed.

Theorem count_member_nonzero : forall s : bag,
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s. reflexivity.
Qed.

Lemma leb_n_Sn : forall n : nat,
  n <=? (S n) = true.
Proof.
  induction n.
  - reflexivity.
  - simpl. apply IHn.
Qed.

Theorem remove_does_not_increase_count : forall s : bag,
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  induction s.
  - reflexivity.
  - destruct n.
    + simpl. rewrite -> leb_n_Sn. reflexivity.
    + simpl. apply IHs.
Qed.

Theorem bag_count_theorem : forall l1 l2 : bag,
  length (sum l1 l2) = length l1 + length l2.
Proof.
  intros l1 l2.
  induction l1.
  - reflexivity.
  - simpl. rewrite -> IHl1.
    reflexivity.
Qed.

Theorem rev_injective : forall l1 l2 : natlist,
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- rev_involutive. rewrite <- H.
  rewrite -> rev_involutive. reflexivity.
Qed.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
  match l with
  | [] => None
  | h :: t => 
    if n =? 0
      then Some h
      else nth_error t (pred n)
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n => n
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | [] => None
  | h :: _ => Some h
  end.

Theorem option_elim_hd : forall (l : natlist) (default : nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros.
  destruct l.
  - reflexivity.
  - reflexivity.
Qed.

End NatList.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) : bool :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : forall x, 
  true = eqb_id x x.
Proof.
  destruct x.
  - simpl. rewrite -> NatList.eq_reflexive. 
    reflexivity.
Qed.

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map) (x : id) (value : nat) : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record i v m => 
    if (eqb_id x i)
      then Some v
      else find x m
  end.

Theorem update_eq : forall (d : partial_map) (x : id) (v : nat),
  find x (update d x v) = Some v.
Proof.
  intros.
  simpl. rewrite <- eqb_id_refl. 
  reflexivity.
Qed.

Theorem update_neq : forall (d : partial_map) (x y : id) (o : nat),
  eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros. 
  simpl. rewrite -> H. 
  reflexivity.
Qed.

End PartialMap.
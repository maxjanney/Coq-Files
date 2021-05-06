From LF Require Export lists.

Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint repeat {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S k => cons x (repeat x k)
  end.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ t => S (length t)
  end.

Notation "x :: y" := (cons x y) 
                     (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem app_nil_r : forall (X : Type) (l : list X),
  l ++ [] = l.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite -> IHl.
    reflexivity.
Qed.

Theorem app_assoc : forall (X : Type) (l m n : list X),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite -> IHl.
    reflexivity.
Qed.

Lemma app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite -> IHl1.
    reflexivity.
Qed.

Theorem rev_app_distr : forall (X : Type) (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1.
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1. rewrite -> app_assoc. 
    reflexivity.
Qed.

Theorem rev_involutive : forall (X : Type) (l : list X),
  rev (rev l) = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. 
    rewrite -> IHl. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, _) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (_, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) 
            : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: combine tx ty
  end.

Fixpoint split {X Y : Type} (l : list (X * Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x,y) :: t => 
    (x :: fst (split t), y :: snd (split t))
  end.

Module OptionPlayground.

Inductive option (X : Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) 
                   : option X :=
  match l with
  | [] => None
  | h :: t =>
    if n =? 0
      then Some h
      else nth_error t (pred n)
  end.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | h :: _ => Some h
  end.

Fixpoint filter {X : Type} (test : X -> bool) (l : list X) 
                : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h
      then h :: filter test t
      else filter test t
  end.

Definition countoddmembers' (l : list nat) : nat :=
  length (filter oddb l).

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun h => evenb h && negb (h <=? 7)) l.

Definition partition {X : Type} 
                     (test : X -> bool) 
                     (l : list X) 
                     : list X * list X :=
  (filter test l, filter (fun h => negb (test h)) l).

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => f h :: map f t
  end.

Lemma map_app : forall (X Y : Type) (x : X) (f : X -> Y) (l : list X),
  map f (l ++ [x]) = map f l ++ [f x].
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite -> IHl.
    reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite <- IHl.
    rewrite -> map_app. reflexivity.
Qed.

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) 
                  : list Y :=
  match l with
  | [] => []
  | h :: t =>
    f h ++ flat_map f t
  end.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) 
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) 
              : Y :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)
  end.

Module Exercises.

Definition fold_len {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Theorem fold_len_correct : forall (X : Type) (l : list X),
  fold_len l = length l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite <- IHl.
    reflexivity.
Qed.

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x y => f x :: y) l [].

Theorem fold_map_correct : forall (X Y : Type) (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite <- IHl.
    reflexivity.
Qed.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros. reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : X*Y -> Z) (p : X*Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros. destruct p.
  - reflexivity.
Qed.

Module Church.

Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition three : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f (f x)).

Definition succ (n : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Definition plus (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => m X f (n X f x).

Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => m X (n X f) x.

Definition exp (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => (m (X -> X) (n X) f) x.

End Church.
End Exercises.
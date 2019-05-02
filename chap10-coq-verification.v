Require Import List Arith Bool.
Import ListNotations.

Fixpoint fact (n : nat ) :=
  match n with
  | 0 => 1
  | S k => n * (fact k)
  end.

Inductive factorial_of : nat -> nat -> Prop :=
| factorial_of_zero : factorial_of 0 1
| factorial_of_succ : forall (a b : nat),
    factorial_of a b -> factorial_of (S a) ((S a) * b).
(* inductively defining a prop*)

Theorem fact_correct : forall (n : nat),
    factorial_of n (fact n).
Proof.
  intros n.
  induction n as [ | k IH].
  - simpl. apply factorial_of_zero.
  - simpl. apply factorial_of_succ.
    assumption.
Qed.

Fixpoint fact_tr_acc (n : nat) (acc : nat) :=
  match n with
  | 0 => acc
  | S k => fact_tr_acc k (n * acc)
  end.
Definition fact_tr (n : nat) :=
  fact_tr_acc n 1.

Lemma fact_tr_acc_mult : forall (n m : nat),
    fact_tr_acc n m = m * fact_tr_acc n 1.
Proof.
  intros n.
  induction n as [ | k IH].
  - intros p. simpl. ring.
  - intros p.
    replace (fact_tr_acc (S k) p) with (fact_tr_acc k ((S k) * p))
    .
    -- rewrite IH. simpl. rewrite mult_1_r. rewrite IH with (m := S k). ring.
    -- simpl. trivial.
Qed.

       Theorem fact_tr_correct : forall (n : nat),
    factorial_of n (fact_tr n).
Proof.
  intros n. unfold fact_tr.
  induction n as [ | k IH].
  - simpl. apply factorial_of_zero.
  - simpl. rewrite mult_1_r.
    destruct k as [ | m].
    -- simpl. rewrite <- mult_1_r.
       apply factorial_of_succ. apply factorial_of_zero.
    -- rewrite fact_tr_acc_mult.
       apply factorial_of_succ.
       assumption.
Qed.

Lemma fact_helper : forall (n acc : nat),
    fact_tr_acc n acc = (fact n) * acc.
Proof.
  intros n.
  induction n as [| k IH];
    intros acc.
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

Theorem fact_tr_is_fact : forall n : nat,
    fact_tr n = fact n.
Proof.
  intros n. unfold fact_tr. rewrite fact_helper. ring.
Qed.

Require Import Extraction.
Extraction Language OCaml.
Extract Inductive nat =>
int ["0" "succ"] "(fun f0 fs -> if n = 0 then f0 () else fs (n - 1))".
Extraction "chap10-fact.ml" fact_tr.


Module MyStack.
 Definition stack (A:Type) := list A.

Definition empty {A:Type} : stack A := nil.

Definition is_empty {A:Type} (s : stack A) : bool :=
  match s with
  | nil => true
  | _::_ => false
  end.

Definition push {A:Type} (x : A) (s : stack A) : stack A :=
  x::s.

Definition peek {A:Type} (s : stack A) : option A :=
  match s with
  | nil => None
  | x::_ => Some x
  end.

Definition pop {A:Type} (s : stack A) : option (stack A) :=
  match s with
  | nil => None
  | _::xs => Some xs
  end.

Definition size {A:Type} (s : stack A) : nat :=
  length s.

Theorem empty_is_empty : forall (A:Type),
  @is_empty A empty = true.
Proof. trivial. Qed.

Theorem push_not_empty : forall (A:Type) (x:A) (s : stack A),
  is_empty (push x s) = false.
Proof. trivial. Qed.

Theorem peek_empty : forall (A:Type),
  @peek A empty = None.
Proof. trivial. Qed.

Theorem peek_push : forall (A:Type) (x:A) (s : stack A),
  peek (push x s) = Some x.
Proof. trivial. Qed.

Theorem pop_empty : forall (A:Type),
  @pop A empty = None.
Proof. trivial. Qed.

Theorem pop_push : forall (A:Type) (x:A) (s : stack A),
  pop (push x s) = Some s.
Proof. trivial. Qed.

Theorem size_empty : forall (A:Type),
  @size A empty = 0.
Proof. trivial. Qed.

Theorem size_push : forall (A:Type) (x:A) (s : stack A),
  size(push x s) = 1 + size s.
Proof. trivial. Qed.

End MyStack.

Extract Inductive bool => "bool" [ "true" "false"].
Extract Inductive option => "option" ["Some" "None"].
Extract Inductive list => "list" ["[]" "(::)"].
Extract Inlined Constant length => "List.length".

Extraction "chap10-mystack.ml" MyStack.

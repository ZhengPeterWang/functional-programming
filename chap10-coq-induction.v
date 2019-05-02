(* Induction in Coq *)
Require Import List.
Import ListNotations.

Fixpoint append {A:Type} (lst1 : list A) (lst2 : list A) :=
  match lst1 with
  | nil => lst2
  | h::t => h::(append t lst2)
  end.

Fixpoint append'	(A:Type) (lst1 : list A) (lst2 : list A) :=
  match lst1 with
  | nil => lst2
  | h::t => h::(append' A t lst2)
  end.
Print append.
Print append'.

Theorem nil_app : forall (A:Type) (lst : list A),
    [] ++ lst = lst.
Proof.
  intros A lst.
  simpl.
  trivial.
Qed.

Theorem app_nil : forall (A: Type) (lst : list A),
    lst ++ [] = lst.
Proof.
  intros A lst.
  induction lst as [ | h t IH].
  - simpl. trivial.
  - simpl. rewrite -> IH. trivial.
Qed.


Theorem app_assoc : forall (A : Type) (l1 l2 l3 : list A),
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  intros A l1 l2 l3.
  induction l1 as [ | j t IH].
  - trivial.
  - simpl. rewrite -> IH. trivial.
Qed.

Print nat.
Compute S O.
Compute S (S O).
Compute S (S (S O)).

Fixpoint my_add (a b : nat) : nat :=
  match a with
  | 0 => b
  | S c => S (my_add c b)
  end.

Fail Fixpoint sum_to (n : nat) : nat :=
  if n = 0 then 0 else n + sum_to (n - 1).

Require Import Arith.
Locate "=?".
Check Nat.eqb.

Fail Fixpoint sum_to (n : nat) : nat :=
  if n =? 0 then 0 else n + sum_to (n - 1).

Fixpoint sum_to (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => n + sum_to k
  end.

Lemma sum_helper : forall n : nat,
    2 * sum_to (S n) = 2 * (S n) + 2 * sum_to n.
Proof.
  intros n. simpl.ring.
Qed.

Theorem sum_sq_no_div : forall n : nat,
    2 * sum_to n = n * (n + 1).
Proof.
  intros n.
  induction n as [ | k IH].
  - trivial.
  - rewrite -> sum_helper.
    rewrite -> IH.
    ring.
Qed.

Lemma div_helper : forall a b c : nat,
    c <> 0 -> c * a = b -> a = b / c.
Proof.
  intros a b c neq eq.
  rewrite <- eq.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul.
  trivial.
  assumption.
Qed.

Search ( _ * _ / _).
Search (_ * _ = _ * _).

Theorem sum_sq : forall n : nat,
    sum_to n = n * (n + 1) / 2.
Proof.
  intros n.
  apply div_helper.
  - discriminate.
  - rewrite sum_sq_no_div.
    trivial.
Qed.

Theorem plus_comm : forall a b,
    a + b = b + a.
Proof.
  intros a b. ring.
Qed.

Theorem foil : forall a b c d,
    (a + b) * (c + d) = a * c + b * c + a * d + b * d.
Proof.
  intros a b c d.
  ring.
Qed.

Print foil.

Compute 0 - 1.
Require Import ZArith.
Open Scope Z_scope.
Compute 0 - 1.
Theorem sub_add_1 : forall a : Z, a - 1 + 1 = a.
Proof.
  intros a. ring.
Qed.
Close Scope Z_scope.
Compute 0 - 1.

Require Import Field.
Require Import Qcanon.
Open Scope Qc_scope.

Theorem frac_qc : forall x y z : Qc, z <> 0 -> (x + y) / z = x / z + y / z.
Proof.
  intros x y z z_not_0.
  field. assumption.
Qed.
Close Scope Qc_scope.

Module RealExample.
  Require Import Reals.
  Open Scope R_scope.
  Theorem frac_r : forall x y z,  z <> 0 -> (x + y) / z = x / z  + y / z.
  Proof.
    intros x y z z_not_0.
    field.
    assumption.
  Qed.
  Close Scope R_scope.
  
End RealExample.

Print app_nil.
Check list_ind. 
Print list_ind.
 
Fixpoint my_list_rect (A : Type) (P : list A -> Prop) (baseCase : P nil) (inductiveCase : forall (h : A) (t : list A), P t -> P (h::t)) (lst : list A) : P lst
  :=
    match lst with
    | nil => baseCase
    | h::t =>
      inductiveCase h t
                    (my_list_rect A P baseCase inductiveCase t)
    end.

Fixpoint my_fold_right
         {A B : Type}
         (init : B)
         (f : A -> B -> B)
         (lst : list A)
  :=
    match lst with
    | nil => init
    | h::t => f h (my_fold_right init f t)
    end.
Print list_rect.

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Print mylist_ind.
Print mylist_rect.

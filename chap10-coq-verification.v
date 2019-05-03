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

Module Compiler.
  Inductive expr : Type :=
  | Const : nat -> expr
  | Plus : expr -> expr -> expr.

  Fixpoint eval_expr (e : expr) : nat :=
    match e with
    | Const i => i
    | Plus e1 e2 => (eval_expr e1) + (eval_expr e2)
    end.

  Example source_test_1 : eval_expr (Const 42) = 42.
  Proof. trivial. Qed.

  Example source_test_2 : eval_expr (Plus (Const 42) (Const 2)) = 44.
  Proof. trivial. Qed.

  Inductive instr : Type :=
  | PUSH : nat -> instr
  | ADD : instr.

  Definition prog := list instr.

  Definition stack := list nat.

  Fixpoint eval_prog (p : prog) (s : stack) : option stack :=
    match p,s with
    | PUSH n :: p', s => eval_prog p' (n::s)
    | ADD :: p', x::y::s' => eval_prog p' (x + y :: s')
    | nil, s => Some s
    | _, _ => None
    end.

  Example target_test_1 : eval_prog [PUSH 42] [] = Some [42].
  Proof. trivial. Qed.

  Example target_test_2 : eval_prog [PUSH 2; PUSH 2; ADD] [] = Some [4].
  Proof. trivial. Qed.

  Fixpoint compile (e : expr) : prog :=
    match e with
    | Const n => [PUSH n]
    | Plus e1 e2 => compile e2 ++ compile e1 ++ [ADD]
    end.

  Example compile_test_1 : compile (Const 42) = [PUSH 42].
  Proof. trivial. Qed.

  Example compile_test_2 : compile (Plus (Const 2) (Const 3))
  = [PUSH 3; PUSH 2; ADD].
  Proof. trivial. Qed.

  
Example post_test_1 :
  eval_prog (compile (Const 42)) [] = Some [eval_expr (Const 42)].
Proof. trivial. Qed.

Example post_test_2 :
  eval_prog (compile (Plus (Const 2) (Const 3))) []
  = Some [eval_expr (Plus (Const 2) (Const 3))].
Proof. trivial. Qed.

Lemma app_assoc_4 : forall (A:Type) (l1 l2 l3 l4 : list A),
    l1 ++ (l2 ++ l3 ++ l4) = (l1 ++ l2 ++ l3) ++ l4.
Proof.
  intros A l1 l2 l3 l4.
  replace (l2 ++ l3 ++ l4) with ((l2 ++ l3) ++ l4);
  rewrite app_assoc; trivial.  
Qed.

Lemma compile_helper : forall (e: expr) (s:stack) (p:prog),
    eval_prog (compile e ++ p) s = eval_prog p (eval_expr e::s).
Proof.
  intros e.
  induction e as [n | e1 IH1 e2 IH2]; simpl.
  - trivial.
  - intros s p. rewrite <- app_assoc_4.
    rewrite IH2. rewrite IH1. simpl. trivial.
Qed.

Theorem compile_correct: forall (e : expr),
    eval_prog (compile e) [] = Some [eval_expr e].
Proof.
  intros e.
  induction e as [n | e1 IH1 e2 IH2]; simpl.
  - trivial.
  - repeat rewrite compile_helper. simpl. trivial.
Qed.
End Compiler.
Extract Inlined Constant Init.Nat.add => "( + )".
Extract Inlined Constant app => "( @ )".
Extraction "chap10-compiler.ml" Compiler.eval_expr 
           Compiler.eval_prog Compiler.compile.

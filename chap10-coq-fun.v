Let x := 42.
Inductive day: Type :=
| sun : day
| mon : day
| tue : day
| wed : day
| thu : day
| fri : day
| sat : day.
Let next_day d :=
match d with 
| sun => mon
| mon => tue
| tue => wed
| wed => thu
| thu => fri
| fri => sat 
| sat => sun
end.
Definition prev_day d :=
  match d with
  | sun => sat
  | mon => sun
  | tue => mon
  | wed => tue
  | thu => wed
  | fri => thu
  | sat => fri
  end.
Theorem wed_aft_tue : next_day tue = wed.
Proof. 
  auto. 
Qed. 
Theorem wed_after_tue' : next_day tue = wed.
Proof.
  simpl. trivial.
Qed.
Print wed_aft_tue.
Print wed_after_tue'.
Theorem day_never_repeats : forall d : day, next_day d <> d.
Proof. 
  intros d. destruct d.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.

Qed.
Print day_never_repeats. 
Theorem day_never_repeats': forall d: day, next_day d <> d.
Proof. 
intros d. destruct d. 
all: discriminate. 
Qed. 
Print day_never_repeats'.
Theorem mon_precedes_tue: forall d : day,
next_day d = tue -> d = mon.
Proof. 
  intros d next_day_is_tue. 
  destruct d. 
  all: discriminate || trivial. 
Qed.  
Print mon_precedes_tue. 

Theorem forty_two: 41 + 1 = 42. 
Proof. 
  reflexivity. 
Qed. 
Print forty_two. 

Require Import List. 
Import ListNotations. 

Module MyList. 
Inductive list (A: Type) : Type := 
| nil : list A 
| cons : A -> list A -> list A. 
End MyList. 
Check list. 

Definition is_empty (A: Type) (lst: list A):=
match lst with 
| nil => true
| cons _ _ => false
end. 

Definition is_empty_sugar (A: Type) (lst : list A):=
match lst with 
| [] => true
| _::_ => false
end.

Compute is_empty nat [1].
Compute is_empty nat []. 

Definition is_empty' {A: Type} (lst: list A) :=
match lst with 
| [] => true
| _::_ => false
end. 
Compute is_empty' [1].
Compute @is_empty' nat [1]. 

Module MyLength. 
Fixpoint length {A: Type} (lst: list A):=
match lst with 
| nil => 0
| _::t => 1 + length t
end.
Compute length [1;2].
End MyLength. 

Module MyOption. 
Inductive option (A:Type) : Type :=
| Some : A -> option A
| None : option A. 
End MyOption. 

Definition hd_opt {A: Type} (lst: list A) : option A :=
match lst with 
| nil => None 
| x :: _ => Some x 
end. 
Compute hd_opt [1]. 
Compute @hd_opt nat []. 

Theorem length0_implies_hdopt_is_none : 
forall A : Type, forall lst : list A, 
length lst = 0 -> hd_opt lst = None. 
Proof. 
  intros A lst length_lst_is_0. 
  destruct lst. 
    trivial. 
    discriminate. 
Qed. 

Definition mult2 x := x * 2. 
Print mult2. 
Compute mult2 0.
Compute mult2 3110.

Definition xor (a b: bool) : bool := 
match a, b with 
| true, false => false
| _, _ => true
end.
Print xor. 

Compute xor true true.

Definition is_none (A: Type) (a: option A) := 
match a with 
| None => true
| _ => false
end. 

Print is_none. 

Check map.
Print map.
Definition double_all (a: list nat) := 
map mult2 a . 
Compute double_all [0;2;10].  

Fixpoint sum (a: list nat ) := 
  match a with 
  | [] => 0
  | h::t => h + sum t 
  end. 
Compute sum [1;2].
Check fold_left. 
Definition plus a b := a + b. 
Definition sum_2 (a: list nat) := 
fold_left plus a 0. 

Theorem thu_aft_wed : forall d : day, 
next_day wed = thu. 
Proof. 
  intros d. 
  destruct d; discriminate || trivial.
Qed.

Theorem wed_bef_thu : forall d : day, 
next_day d = thu -> d = wed. 
Proof. 
  intros d next_day_is_thu.
  destruct d; discriminate || trivial. 
Qed.

Definition tl_opt {A: Type} (lst : list A) : option (list A) := 
match lst with
| [] => None 
| h::t => Some t
end. 

Theorem incl_is_2: forall n, n = 1 -> (fun x => x + 1) n = 2. 
Proof. 
  intros n n_is_1. rewrite n_is_1. trivial. 
Qed.

Theorem nil_implies_tlopt_none :
  forall A: Type, forall lst : list A, 
  lst = nil -> tl_opt lst = None. 
Proof. 
  intros A l l_is_nil. 
  rewrite l_is_nil. 
  simpl. trivial.
Qed. 

Theorem cons_implies_tlopt_some :
  forall {A: Type} (h: A) (t: list A) (lst: list A), 
  lst = h::t -> tl_opt lst = Some t. 
Proof.
  intros A h t lst lst_is_cons.
  rewrite lst_is_cons.
  unfold tl_opt.trivial.
Qed.

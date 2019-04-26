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
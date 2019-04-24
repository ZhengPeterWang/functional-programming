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
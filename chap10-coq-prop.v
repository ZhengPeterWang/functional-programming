Check list.

Definition natlist : Type := list nat.
Check natlist.
Theorem obvious_fact : 1 + 1 = 2.
Proof. trivial. Qed.
Check obvious_fact.
Print obvious_fact. 

Check nat.
Check Set.
Check 43.
Check fun x : nat => x + 1.

Check 1 + 1 = 2.
Check Prop.
Locate "=".
Check @eq.

Check and. Check or. Check not.

Theorem p_implies_p: forall P:Prop, P -> P.
Proof.
  intros P. intros P_assumed. assumption.
Qed.
Check p_implies_p.
Print p_implies_p.

Definition p_implies_p_direct : forall P: Prop, P -> P :=
  fun p ev_p => ev_p.

Theorem syllogism : forall P Q: Prop,
    (P -> Q) -> P -> Q.
Proof.
  intros P Q evPimpQ evP.
  apply evPimpQ.
  assumption.
Qed.
Print syllogism.

Theorem imp_trans : forall P Q R : Prop,
    (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R evPimpQ evQimpR.
  intros evP.
  apply evQimpR.
  apply evPimpQ.
  assumption.
Qed.
Print imp_trans.

Theorem and_fst : forall P Q, P /\ Q -> P.
Proof.
  intros P Q PandQ.
  destruct PandQ.
  assumption.
Qed.
Print and_fst.
Locate "/\".
Print and.

Theorem and_snd : forall P Q:Prop,
    P/\Q ->Q.
Proof.
  intros P Q PandQ.
  destruct PandQ as [P_holds Q_holds].
  assumption.
Qed.
Print and_snd.

Theorem and_ex : 42 = 42 /\ 43 = 43.
Proof.
  split;
  trivial.
Qed.
Print and_ex.

Theorem and_comm: forall P Q, P /\ Q -> Q /\ P.
Proof.
  intros P Q PandQ.
  destruct PandQ as [P_holds Q_holds].
  split; assumption.
Qed.
Print and_comm.

Theorem and_to_imp: forall P Q R: Prop,
    (P /\ Q -> R) -> (P -> (Q -> R)).
Proof.
  intros P Q R evPandQimpR evP evQ.
  apply evPandQimpR.
  split.
  all: assumption.
Qed.
Print and_to_imp.

Theorem or_left : forall (P Q : Prop),
    P -> P \/ Q.
Proof.
  intros P Q P_holds.
  left.
  assumption.
Qed.
Print or_left.
Locate "\/".
Print or_introl.

Theorem or_right : forall P Q : Prop, Q -> P \/Q.
Proof.
  intros P Q Q_holds.
  right.
  assumption.
Qed.
Print or_right.

Theorem or_thm : 3110 = 3110 \/ 2110 = 3110.
Proof.
  left. trivial.
Qed.
Print or_thm.

Theorem or_comm : forall P Q, P \/ Q -> Q \/ P.
Proof.
  intros P Q PorQ.
  destruct PorQ.
  - right. assumption.
  - left. assumption.
Qed.
Print or_comm.

Theorem or_distr_and : forall P Q R,
    P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R PorQR.
  destruct PorQR as [P_holds | QR_holds].
  - split; left; assumption.
  - destruct QR_holds as [Q_holds R_holds].
    split; right; assumption.
Qed.
Print or_distr_and.

Print False.
Theorem explosion : forall P: Prop, False -> P.
Proof.
  intros P false_holds.
  contradiction.
Qed.
Print explosion.

Definition explosion' : forall (P: Prop), False -> P :=
  fun (P : Prop) (f: False) =>
    match f with end.

Theorem p_imp_or_false : forall P: Prop, P -> P \/ False.
Proof.
  intros P P_holds. left. assumption.
Qed.
Theorem p_imp_p_and_true: forall P:Prop, P -> P /\ True.
Proof.
  intros P P_holds. split. assumption. exact I.
Qed.
Print True.
Print p_imp_p_and_true.

Locate "~".
Print not.
Theorem notFalse : ~False -> True.
Proof.
  unfold not.
  intros.
  exact I.
Qed.
Print notFalse.
Theorem notTrue : ~True -> False.
Proof.
  unfold not.
  intros t_imp_f.
  apply t_imp_f.
  exact I.
Qed.
Print notTrue.

Theorem contra_implies_anything : forall P Q, P/\~P -> Q.
Proof.
  unfold not.
  intros P Q PandnotP.
  destruct PandnotP as [P_holds notP_holds].
  contradiction.
Qed.
Print contra_implies_anything.

Theorem deMorgan : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros P Q PorQ_imp_false.
  split.
  - intros P_holds. apply PorQ_imp_false. left. assumption.
  - intros Q_holds. apply PorQ_imp_false. right. assumption.
Qed.
Print deMorgan.

Theorem deMorgan2 : forall P Q : Prop, ~(P /\ Q) -> ~P \/ ~Q.
Proof. 
  unfold not.
  intros P Q PQ_imp_false.
  left.
  intros P_holds. apply PQ_imp_false. split. assumption.
Abort.

Theorem p_imp_nnp: forall P : Prop, P -> ~~P.
Proof.
  unfold not.
  intros P evP evPimpFalse.
  apply evPimpFalse.
  assumption.
Qed.

Theorem syllogism' : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  intros P Q evP evPimpQ.
  apply evPimpQ.
  assumption.
Qed.
Theorem p_imp_nnp': forall P : Prop, P -> ~~P.
Proof. 
  unfold not.
  intros P.
  apply syllogism'.
Qed.
Print p_imp_nnp'.

Module ClassicalReasoning.
  Require Import Coq.Logic.Classical.
  Print classic.
  Print NNPP.
End ClassicalReasoning.


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

Locate "=".
Print eq.
Definition eq42 := @eq nat 42.
Check eq42.
Check (eq42 42).
Check (eq42 43).
Check @eq_refl nat 42.

Theorem direct_eq: 42 = 42.
Proof.
  exact (eq_refl 42).
Qed.
Locate "->".

Theorem deMorgan' : forall P Q: Prop,
    ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  tauto.
Qed.
Print deMorgan'.

Definition x := 2.
Definition y: Set := nat.
Definition z : 0 * 1 = 0 := eq_refl.
Print z.
Definition w : Type := list nat.

Theorem impl : forall P Q : Prop,
    P -> (Q -> P).
Proof.
  intros P Q wP wQ.
  assumption.
Qed.

Theorem imp2 : forall P Q R : Prop,
    (P -> (Q -> R)) -> (Q -> (P -> R)).
Proof.
  intros P Q R PtoQtoR eQ eP.
  apply PtoQtoR.
  assumption.
  assumption.
Qed.
Print imp2.

Theorem imp3 : forall P Q R : Prop,
    ((P -> Q) -> (P -> R)) -> (P -> (Q -> R)).
Proof.
  intros P Q R PtoQtoPtoR eP eQ.
  apply PtoQtoPtoR.
  intros eeP.
  assumption.
  assumption.
Qed.
Print imp3.


Theorem conj1 : forall P Q : Prop,
    P -> (Q -> (P /\ Q)).
Proof.
  intros P Q eP eQ.
  split.
  assumption.
  assumption.
Qed.

Theorem conj2 : forall P Q R : Prop,
    (P -> (Q -> R)) -> ((P /\ Q ) -> R).
Proof.
  intros P Q R PtoQtoR PandQ.
  apply PtoQtoR.
  destruct PandQ as [eP eQ].
  assumption.
  destruct PandQ as [eP eQ].
  assumption.
Qed.
Print conj2.

Theorem conj3 : forall P Q R : Prop,
    (P /\ (Q /\ R)) -> ((P /\ Q) /\ R).
Proof.
  intros P Q R PandQandR.
  destruct PandQandR as [eP QandR].
  destruct QandR as [eQ eR].
  split.
  - split; assumption.
  - assumption.
Qed.
Print conj3.

Definition direct_conj3 (P Q R : Prop) (evP_QR : P /\ Q /\ R)
  : (P /\ Q) /\ R
  :=
    match evP_QR with
    | conj evP evQR =>
      match evQR with
      | conj evQ evR => conj (conj evP evQ) evR
      end
    end.
Print direct_conj3.

Definition direct_conj3' (P Q R : Prop) (evP_QR : P /\ Q /\ R)
  : (P /\ Q) /\ R
  :=
    match evP_QR with
    | conj evP (conj evQ evR) => conj (conj evP evQ) evR
    end.
Print direct_conj3'.

Theorem disj1 : forall P : Prop,
    P -> P \/ P.
Proof.
  intros P eP.
  left.
  assumption.
Qed.

Theorem disj2 : forall P : Prop,
    P \/ P -> P.
Proof.
  intros P PorP.
  destruct PorP.
  assumption.
  assumption.
Qed.

Theorem disj3 : forall P Q R : Prop,
    (P -> R) -> (Q -> R) -> (P \/ Q -> R).
Proof.
  intros P Q R PtoR QtoR PorQ.
  destruct PorQ.
  - apply PtoR. assumption.
  - apply QtoR. assumption.
Qed.

Theorem and_distr_or : forall P Q R,
    P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
  intros P Q R PandQorR.
  destruct PandQorR as [eP QorR].
  destruct QorR as [eQ | eR].
  - left. split; assumption.
  - right. split; assumption.
Qed.
Print and_distr_or.

Theorem tf1 : True \/ False.
Proof.
  left.
  exact I.
Qed.

Locate "<->".
Print iff.

Theorem tf2: forall P : Prop,
    P <-> (True <-> P).
Proof.
  unfold iff.
  intros P.
  split.
  - intros eP.
    split.
    + intros t.
      assumption.
    + intros eeP.
      exact I.
  - intros ttPaPtt.
    destruct ttPaPtt as [l r].
    apply l.
    exact I.
Qed.
Print tf2.

Theorem neg1 : forall P : Prop,
    P /\ ~P -> False.
Proof.
  intros P PorNotP.
  destruct PorNotP.
  contradiction.
Qed.
Print neg1.

Theorem neg2 : forall P Q : Prop,
    (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not.
  intros P Q PtoQ nQ.
  intros eP.
  apply nQ.
  apply PtoQ.
  assumption.
Qed.
Print neg2.

Theorem neg3: forall P Q : Prop,
    ~P \/ ~Q -> ~(P /\ Q).
Proof.
  unfold not.
  intros P Q nPornQ.
  intros PandQ.
  destruct nPornQ as [nP | nQ].
  - apply nP. destruct PandQ. assumption.
  - apply nQ. destruct PandQ. assumption.
Qed.
Print neg3.

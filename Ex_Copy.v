Require Import CSSsVerification.
Require Import Aid.
Import ListNotations.

Definition b : id := Id "b".
Definition b2 : id := Id "b2".
Definition len  : id := Id "len".

Definition Create :=
  CBalloc b (ANum 1011);;
  CBappend (BKId b) (ANum 1012);;
  CFcreate f1 (BKId b).

Lemma OptEqVal : forall (n1 n2:nat),
  Some n1 = Some n2 -> n1 = n2.
Proof.
  intros.
  inversion H. auto.
Qed.

Lemma ValEqOpt : forall (n1 n2:nat),
  n1 = n2 -> Some n1 = Some n2.
Proof.
  intros. auto.
Qed.

Lemma Inlist : forall n l,
  in_list [v2o n] l = true -> n = o2v l.
Proof.
  intros. unfold v2o, o2v.
  inversion H.
  destruct l.
  - destruct (n =? n0) eqn: H'.
    apply beq_true in H'; auto.
    discriminate.
  - discriminate.
Qed.

Theorem hV_update_neq :forall hV x1 x2 v,
   x1 <> x2
->(x2 !hv-> v ; hV) x1 = hV x1.
Proof.
  intros.
  unfold hV_update.
  apply beq_neq in H.
  rewrite beq_comm in H.
  rewrite H.
  reflexivity.
Qed.

Fact Create_Correct :
forall (bl l1 l2:nat),
l1 <> l2 ->
empty_st =[
  Create
]=> St ((emp_sV,
b !sb-> bl; emp_sB,
f1 !sf-> [bl]; emp_sF,
l2 !hv-> 1012; l1 !hv-> 1011; emp_heapV,
bl !hb-> [v2o l1; v2o l2]; emp_heapB)).
Proof.
  intros bl l1 l2 H0.
  eapply E_Seq.
  - eapply E_Ballocate with (loc := l1) ;
    reflexivity.
  - eapply E_Seq.
    eapply E_Bappend with (bloc := bl) (loc := l2).
    reflexivity. rewrite hB_update_eq. reflexivity.
    intros. 
    apply Inlist in H. exists (Some 1011).
    rewrite H. rewrite hV_update_eq. reflexivity.
    reflexivity. rewrite hV_update_neq. auto. auto.
  + simpl. rewrite hB_update_shadow.
    eapply E_Fcreate. simpl.
    rewrite sB_update_eq. reflexivity.
Qed.

(*  emp_sV,
  (b !sb-> n1; emp_sB),
  (f1 !sf-> [n1]; emp_sF),
  (n1 !hb-> [n2;n3]; emp_heapB),
  (n2 !hv-> n4; n3 !hv-> n4; emp_heapV)
).*)


Definition Copy :=
  i ::= (ANum 1);;
  CBlength len (BKAddr f1 (ANum 1));;
  CBnew b2;;
  WHILE (BLe (AId i) (AId len)) DO
    CBlookup bc (BKAddr f1 (ANum 1)) (AId i);;
    CBappend (BKId b2) (AId bc);;
    i ::= (APlus (AId i) (ANum 1))
  END.

Definition no4_eq (n1 n2 n3 n4 : nat) :=
   n2 <> n1 /\ n1 <> n3 /\ n1 <> n4 
/\ n2 <> n3 /\ n2 <> n4 /\ n3 <> n4
.


Lemma oneqv : forall (l : option nat) n,
  n <> 0 ->
  (o2v l =? n) = beq_op_nat (v2o n) l.
Proof.
  intros.
  destruct l; simpl.
  - rewrite beq_comm. auto.
  - destruct n. destruct H. auto.
    auto.
Qed.

Lemma InHb : forall (l : option nat) n1 n2,
in_list [v2o n1; v2o n2] l = true ->
n1 <> 0 -> n2 <> 0 -> 
o2v l = n1 \/ o2v l = n2.
Proof.
    intros.
    destruct ((o2v l) =? n1) eqn : L1.
    apply beq_eq in L1.
    rewrite L1.
    left. auto.
    destruct ((o2v l) =? n2) eqn : L2.
    apply beq_eq in L2.
    rewrite L2.
    right. auto. rewrite oneqv in L1.
    rewrite oneqv in L2.
    unfold in_list in H.
    rewrite L1 in H. rewrite L2 in H.
    discriminate. auto. auto.
Qed.

Lemma SafeinHb1 : forall (l : option nat) n1 n2 n3 n4,
in_list [v2o n1; v2o n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n1 <> n2 ->
exists k , (n2 !hv-> n3; n1 !hv-> n4; emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHb in H.
  destruct H; rewrite H.
  exists (Some n4).
  rewrite hV_update_neq. rewrite hV_update_eq. reflexivity.
  auto.
  exists (Some n3).
  rewrite hV_update_eq. reflexivity.
  auto. auto.
Qed.

Lemma SafeinHb2 : forall (l : option nat) n1 n2 n3 n4 n5 n6,
in_list [v2o n1; v2o n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n1 <> n2 ->
n3 <> n1 -> n3 <> n2 ->
exists k , (n3 !hv-> n6; n2 !hv-> n5; n1 !hv-> n4; emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHb in H.
  destruct H; rewrite H.
  exists (Some n4).
  rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto.
  exists (Some n5).
  rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity. auto. auto. auto.
Qed.

Fact Copy_Correct :
forall (l1 l2 l3 l4 bl bl2:nat),
bl <> bl2 ->
no4_eq l1 l2 l3 l4 ->
l1 <> 0 -> l2 <> 0 -> l3 <> 0 -> l4 <> 0 ->
(emp_sV,
b !sb-> bl; emp_sB,
f1 !sf-> [bl]; emp_sF,
l2 !hv-> 1012; l1 !hv-> 1011; emp_heapV,
bl !hb-> [v2o l1; v2o l2]; emp_heapB) 
=[
    Copy 
]=> St (
(i !sv-> 3; bc !sv-> 1012; len !sv-> 2; emp_sV,
b2 !sb-> bl2; b !sb-> bl; emp_sB,
f1 !sf-> [bl]; emp_sF,
l4 !hv-> 1012; l3 !hv-> 1011; l2 !hv-> 1012; l1 !hv-> 1011; emp_heapV,
bl2 !hb-> [v2o l3; v2o l4]; bl !hb-> [v2o l1; v2o l2]; emp_heapB)
    ).
Proof.
  unfold no4_eq.
  intros l1 l2 l3 l4 bl bl2 H0
  [H1[H2[H3[H4[H5 H6]]]]].
  intros P1 P2 P3 P4.
  eapply E_Seq. eapply E_Ass. auto.
  eapply E_Seq. eapply E_Bsize.
  reflexivity. rewrite hB_update_eq.
  reflexivity. intros. apply SafeinHb1.
  auto. auto. auto. auto.
  reflexivity.

  eapply E_Seq.
  eapply E_Bnew with (bloc := bl2).
  rewrite hB_update_neq; auto.
  eapply E_WhileLoop.
  - auto. 
  - eapply E_Seq. simpl.

    eapply E_Blookup; simpl; auto.
    rewrite hB_update_neq.
    rewrite hB_update_eq. auto.
    apply neq_comm. auto. auto. auto.
    intros. apply SafeinHb1.
    auto. auto. auto. auto.
    reflexivity.
    rewrite hV_update_neq.
    rewrite hV_update_eq.
    reflexivity. auto.

    
    eapply E_Seq.
    eapply E_Bappend with  (loc := l3).
    reflexivity.
    rewrite sB_update_eq, hB_update_eq.
    auto. intros.
    inversion H.
    simpl. rewrite sV_update_eq. reflexivity.
    rewrite hV_update_neq. 
    rewrite hV_update_neq. auto. auto. auto.
    apply E_Ass. reflexivity.
  - simpl.
    rewrite sB_update_eq.
    rewrite hB_update_shadow.

    eapply E_WhileLoop.
  + auto.
  + eapply E_Seq. simpl.

    eapply E_Blookup; simpl; auto.
    rewrite hB_update_neq.
    rewrite hB_update_eq. reflexivity.
    apply neq_comm. auto.
    intros. apply SafeinHb2.
    auto. auto. auto. auto. auto. auto.
    reflexivity.
    rewrite hV_update_neq.
    rewrite hV_update_eq. reflexivity.
    auto.

    eapply E_Seq.
    eapply E_Bappend with (loc := l4).
    reflexivity.
    rewrite sB_update_eq,hB_update_eq.
    reflexivity.
    intros. apply Inlist in H.
    exists (Some 1011). rewrite H.
    rewrite hV_update_eq. reflexivity.
    reflexivity.
    rewrite hV_update_neq.
    rewrite hV_update_neq.
    rewrite hV_update_neq.
    reflexivity. auto.
    auto. auto.

    apply E_Ass.
    reflexivity.

  + simpl.
    rewrite sV_update_eq, sB_update_eq, hB_update_shadow.
    rewrite sV_update_shadow_2.
    rewrite sV_update_shadow.
    rewrite sV_update_shadow_3.
    eapply E_WhileEnd.
    reflexivity.
Qed. 






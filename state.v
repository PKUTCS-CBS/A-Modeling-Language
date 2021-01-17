Require Import util Aid.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

(*定义五元组来表示系统状态*)

(*Sv, Sb, Sf*)
Definition storeV := id -> nat.
Definition storeB := id -> nat.
Definition storeF := id -> list nat.

(*Hv,Hb因为可能对应不到值,所以用可选类型*)
Definition heapV := nat -> option nat.
Definition heapB := nat -> option (list (option nat)).

(*定义空堆*)
Definition emp_heapV : heapV :=
  fun (n: nat) => None.

Definition emp_heapB : heapB :=
  fun (n: nat) => None.

(*定义命题 : 在堆的定义域中*)
Definition in_domV (loc: nat) (hv: heapV) : Prop :=
  exists n, hv loc = Some n.

Definition in_domB (bloc: nat) (hb: heapB) : Prop :=
  exists l, hb bloc = Some l.

(*定义命题 : 不在堆的定义域中*)
Definition not_in_domV (loc: nat) (hv: heapV) : Prop :=
  hv loc = None.

Definition not_in_domB (bloc: nat) (hb: heapB) : Prop :=
  hb bloc = None.

(*在定义域的(Some n) + 不在定义域的(None) 为全集*)
Theorem in_not_in_dec_V :
  forall l h, {in_domV l h} + {not_in_domV l h}.
Proof.
  intros l h.
  unfold in_domV, not_in_domV.
  destruct (h l).
  - left. exists n. auto.
  - right. auto.
Qed.

Theorem in_not_in_dec_B :
  forall l h, {in_domB l h} + {not_in_domB l h}.
Proof.
  intros l h.
  unfold in_domB, not_in_domB.
  destruct (h l).
  - left. exists l0. auto.
  - right. auto.
Qed.

(*定义命题:两堆不相交*)
Definition disjointV (h1 h2: heapV) : Prop :=
  forall l, not_in_domV l h1 \/ not_in_domV l h2.

Definition disjointB (h1 h2: heapB) : Prop :=
  forall l, not_in_domB l h1 \/ not_in_domB l h2.

(*heap1 析取 heap2*)
Definition h_unionV (h1 h2: heapV) : heapV :=
  fun l =>
    if (in_not_in_dec_V l h1) then h1 l else h2 l.

Definition h_unionB (h1 h2: heapB) : heapB :=
  fun l =>
    if (in_not_in_dec_B l h1) then h1 l else h2 l.


(* h1 is a subset of h2 *)
Definition h_subsetV (h1 h2: heapV) : Prop :=
  forall loc n, h1 loc = Some n -> h2 loc = Some n.

Definition h_subsetB (h1 h2: heapB) : Prop :=
  forall bloc l, h1 bloc = Some l -> h2 bloc = Some l.


(* store update *)
Definition sV_update (s: storeV) (x: id) (n: nat) : storeV :=
  fun x' => if beq_id x x' then n else s x'.

Definition sB_update (s: storeB) (x: id) (n: nat) : storeB :=
  fun x' => if beq_id x x' then n else s x'.

Definition sF_update (s: storeF) (x: id) (nli: list nat) : storeF :=
  fun x' => if beq_id x x' then nli else s x'.

Notation "x '!sv->' v ';' m" := (sV_update m x v)
            (at level 100, v at next level, right associativity).

Notation "x '!sb->' v ';' m" := (sB_update m x v)
            (at level 100, v at next level, right associativity).

Notation "x '!sf->' v ';' m" := (sF_update m x v)
            (at level 100, v at next level, right associativity).

(* heap update *)
Definition hV_update (h: heapV) (loc: nat) (n: nat) : heapV :=
  fun loc' => if beq_nat loc loc' then Some n else h loc'.

Definition hB_update (h: heapB) (bloc: nat) (l: list (option nat)) : heapB :=
  fun bloc' => if beq_nat bloc bloc' then Some l else h bloc'.

Notation "x '!hv->' v ';' m" := (hV_update m x v)
            (at level 100, v at next level, right associativity).

Notation "x '!hb->' v ';' m" := (hB_update m x v)
            (at level 100, v at next level, right associativity).


(* heap remove *)
Definition hV_remove (h:heapV) (l:nat) : heapV :=
fun x => if beq_nat x l then None else h x.

Definition hB_remove (h:heapB) (l:nat) : heapB :=
fun x => if beq_nat x l then None else h x.

(****Some Lemma****)
Lemma sV_update_eq : forall storeV x v,
   (x !sv-> v ; storeV) x = v.
Proof.
  intros.
  unfold sV_update.
  rewrite beq_id_refl.
  reflexivity.
Qed.

Lemma sB_update_eq : forall storeB x v,
   (x !sb-> v ; storeB) x = v.
Proof.
  intros.
  unfold sB_update.
  rewrite beq_id_refl.
  reflexivity.
Qed.

Theorem sB_update_neq :forall sB x1 x2 v,
   x1 <> x2
->(x2 !sb-> v ; sB) x1 = sB x1.
Proof.
  intros.
  unfold sB_update.
  apply beq_neq_id in H.
  rewrite beq_comm_id in H.
  rewrite H.
  reflexivity.
Qed.

Lemma sF_update_eq : forall storeF x v,
   (x !sf-> v ; storeF) x = v.
Proof.
  intros.
  unfold sF_update.
  rewrite beq_id_refl.
  reflexivity.
Qed.

Theorem sF_update_neq :forall sF x1 x2 v,
   x1 <> x2
->(x2 !sf-> v ; sF) x1 = sF x1.
Proof.
  intros.
  unfold sF_update.
  apply beq_neq_id in H.
  rewrite beq_comm_id in H.
  rewrite H.
  reflexivity.
Qed.

Lemma hV_update_eq : forall heapV x v,
   (x !hv-> v ; heapV) x = Some v.
Proof.
  intros.
  unfold hV_update.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Lemma hB_update_eq : forall heapB x v,
   (x !hb-> v ; heapB) x = Some v.
Proof.
  intros.
  unfold hB_update.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem hB_update_neq :forall hB x1 x2 v,
   x1 <> x2
->(x2 !hb-> v ; hB) x1 = hB x1.
Proof.
  intros.
  unfold hB_update.
  apply beq_neq in H.
  rewrite beq_comm in H.
  rewrite H.
  reflexivity.
Qed.

Lemma sV_update_shadow : forall storeV x v1 v2,
  (x !sv-> v2 ; x !sv-> v1 ; storeV) = (x !sv-> v2; storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sB_update_shadow : forall storeB x v1 v2,
  (x !sb-> v2 ; x !sb-> v1 ; storeB) = (x !sb-> v2; storeB).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sB_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sB_update_shadow_3 : forall storeB x y v1 v2 v3,
  (x !sb-> v2 ; y !sb-> v1 ; x !sb-> v3 ;storeB) 
= (x !sb-> v2; y !sb-> v1; storeB).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sB_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_2 : forall storeV x y v1 v2 v3,
  (x !sv-> v2 ; y !sv-> v1 ; x !sv-> v3 ;storeV) 
= (x !sv-> v2; y !sv-> v1; storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_3 : forall storeV x y z v1 v2 v3 v4,
  (x !sv-> v2 ; y !sv-> v1 ; z !sv-> v4 ; x !sv-> v3 ;storeV) 
= (x !sv-> v2; y !sv-> v1 ; z !sv-> v4 ; storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sF_update_shadow : forall storeF x v1 v2,
  (x !sf-> v2 ; x !sf-> v1 ; storeF) = (x !sf-> v2; storeF).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sF_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sF_update_shadow_3 : forall storeF x y v1 v2 v3,
  (x !sf-> v2 ; y !sf-> v1 ; x !sf-> v3 ;storeF) 
= (x !sf-> v2; y !sf-> v1; storeF).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sF_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hV_update_shadow : forall heapV x v1 v2,
  (x !hv-> v2 ; x !hv-> v1 ; heapV) = (x !hv-> v2; heapV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hV_update.
  destruct (beq_nat x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hB_update_shadow : forall heapB x v1 v2,
  (x !hb-> v2 ; x !hb-> v1 ; heapB) = (x !hb-> v2; heapB).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hB_update.
  destruct (beq_nat x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hB_remove_neq : forall hB x1 x2 v,
   x1 <> x2
-> hB_remove (x2 !hb-> v;hB) x1 
   = (x2 !hb-> v; hB_remove hB x1).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hB_remove.
  destruct (beq_nat x x1) eqn:H1.
  + rewrite beq_eq in H1.
    rewrite H1,hB_update_neq.
    rewrite <- beq_refl.
    trivial. trivial.
  + destruct (beq_nat x x2) eqn:H2.
    - rewrite beq_eq in H2. subst.
      repeat rewrite hB_update_eq. trivial.
    - rewrite beq_neq in H2.
      repeat rewrite hB_update_neq; trivial.
      rewrite H1.
      trivial.
Qed.

(* Lemma hB_remove_eq : forall hB x1 x2 v,
   x1 <> x2
-> (hB_remove (x2 !hb-> v;hB) x1) x2 = Some v.
Proof.
  intros.
  unfold hB_remove.
  apply neq_comm in H.
  rewrite <- beq_neq in H.
  rewrite H.
  apply hB_update_eq.
Qed.

Lemma hB_remove_neq : forall hB x1 x2 x3 v,
   x1 <> x2 -> x3 <> x2
-> (hB_remove (x1 !hb-> v;hB) x3) x2 
   = (hB_remove hB x3) x2.
Proof.
  intros.
  unfold hB_remove.
  apply neq_comm in H0.
  rewrite <- beq_neq in H0.
  rewrite H0.
  apply hB_update_neq.
  auto.
Qed. *)

Lemma hB_remove_emp : forall x,
  hB_remove emp_heapB x = emp_heapB.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hB_remove.
  destruct (beq_nat x0 x) eqn:H1;
  trivial.
Qed.

Lemma hB_remove_work : forall hB x v,
   not_in_domB x hB
-> hB_remove (x !hb-> v;hB) x = hB.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hB_remove.
  destruct (beq_nat x0 x) eqn:H1.
  - rewrite beq_eq in H1. subst. auto.
  - rewrite beq_neq in H1.
    rewrite hB_update_neq; auto.
Qed.

(*定义五元组*)
Definition state : Type := (storeV * storeB * storeF * heapV * heapB).

(*定义状态转换*)
Inductive ext_state : Type :=
|  St: state -> ext_state    (* normal state *)
| Abt: ext_state.            (* abort *)



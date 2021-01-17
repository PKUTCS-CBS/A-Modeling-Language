Require Import Coq.Strings.String.
Require Import Aid.

Inductive id : Type :=
| Id      : string -> id.

Definition beq_id id1 id2 :=
  match id1,id2 with
  | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Theorem beq_eq_id :
  forall x y : id,
  beq_id x y = true <-> x = y.
Proof.
  intros. split.
  - intros. unfold beq_id in *. destruct x. destruct y.
   destruct (string_dec s s0). +subst. auto. +inversion H.
  - intros. unfold beq_id. destruct x. destruct y.
   destruct (string_dec s s0). +auto. +inversion H. subst.
   destruct n. auto.
Qed.

Theorem beq_neq_id : forall x y ,
  beq_id x y = false <-> x <> y.
Proof.
 split.
  - rewrite <- beq_eq_id.
    unfold not.
    intros.
    rewrite H in H0.
    discriminate.
  - unfold not.
    intros.
    rewrite <- (not_true_is_false (beq_id x y)).
    reflexivity.
    unfold not.
    rewrite beq_eq_id.
    apply H.
Qed.

Theorem beq_id_refl : forall s : id, 
  beq_id s s = true.
Proof.
  intros s.
  unfold beq_id.
  destruct s.
  destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

Lemma beq_comm_id : forall m n,
  (beq_id m n) = (beq_id n m).
Proof.
  intros.
  destruct (beq_id m n) eqn : H.
  apply beq_eq_id in H.
  rewrite H.
  rewrite beq_id_refl. trivial.
  apply beq_neq_id in H.
  symmetry. apply beq_neq_id.
  intro. subst.
  apply H. trivial.
Qed.


Definition option_elim (d : nat) (o : option nat) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.


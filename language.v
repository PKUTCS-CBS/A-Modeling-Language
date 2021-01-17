Require Import util.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Import ListNotations.

(*******语法部分********)

(*算术表达式*)
Inductive aexp: Type :=
| ANum : nat -> aexp
| AId : id -> aexp    (* Var *)
| APlus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp.

(*块表达式*)
Inductive bkexp : Type :=
| BKNum : nat -> bkexp
| BKId  : id -> bkexp     (* BKVar *)
| BKAddr: id -> aexp -> bkexp.

Inductive fexp : Type :=
(* | FNil : nil -> fexp *)
| FId : id -> fexp
| Fattach : fexp -> bkexp -> fexp.

(*布尔表达式*)
Inductive bexp: Type :=
| BTrue : bexp
| BFalse: bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp
| BOr  : bexp -> bexp -> bexp.


Inductive command: Type :=
| CSkip    : command
| CAss     : id -> aexp -> command
| CSeq     : command -> command -> command
| CIf      : bexp  -> command -> command -> command
| CWhile   : bexp -> command -> command
| CCons    : id -> aexp -> command  (*只创建一个存储空间*)
| CLookup  : id -> aexp -> command
| CMutate  : aexp -> aexp -> command
| CDispose : aexp -> command
(*file*)
| CFcreate : id -> bkexp -> command
| CFattach : id -> bkexp -> command
| CFdelete : id -> command
| CFlength : id -> id -> command
(*block*)
| CBalloc  : id -> aexp -> command
| CBnew    : id -> command
| CBappend : bkexp -> aexp -> command
| CBlookup : id -> bkexp -> aexp -> command
| CBlength : id -> bkexp -> command
| CBreplace : fexp -> aexp -> bkexp -> command
| CBtruncate : bkexp -> command
| CBdelete : bkexp -> command.


Notation " 'SKIP' " := CSkip.
Notation "x '::=' a" := (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).






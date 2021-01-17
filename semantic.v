Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import language.
Require Import state.
Require Import util.
Import ListNotations.

Fixpoint aeval (stoV: storeV) (a:aexp) : nat :=
match a with
| ANum n => n
| AId name => stoV name
| APlus a1 a2 => (aeval stoV a1) + (aeval stoV a2)
| AMult a1 a2 => (aeval stoV a1) * (aeval stoV a2)
| AMinus a1 a2 => (aeval stoV a1) - (aeval stoV a2)
end.


Fixpoint findbk (li:list nat) (loc:nat): option nat :=
match li with
| [] => None
| x::xli => if (beq_nat loc 1) then Some x else (findbk xli (loc-1))
end.

Fixpoint bkeval (stoV:storeV) (stoB:storeB) 
                (stoF:storeF) (bk:bkexp) : option nat :=
match bk with
| BKNum n => Some n
| BKId name => Some (stoB name)
| BKAddr fname a => findbk (stoF fname) (aeval stoV a)
end.
 

Fixpoint beval stoV (b:bexp) : option bool :=
match b with
| BTrue   => Some true
| BFalse  => Some false
| BEq a1 a2 => Some (beq_nat (aeval stoV a1) (aeval stoV a2))
| BLe a1 a2 => Some (leb (aeval stoV a1) (aeval stoV a2))
| BNot b1   =>(match (beval stoV b1) with
               | None => None
               | Some x => Some (negb x)
               end)
| BAnd b1 b2  =>(match (beval stoV b1), (beval stoV b2) with
                 | None,_ => None
                 | _,None => None
                 | Some x1,Some x2 => Some (andb x1 x2)
                 end)
| BOr  b1 b2  =>(match (beval stoV b1), (beval stoV b2) with
                 | None,_ => None
                 | _,None => None
                 | Some x1, Some x2 => Some (orb x1 x2)
                 end)
end.


(* auxiliary function *)
(*可选类型的nat比较*)
Definition beq_op_nat (x y: option nat) : bool :=
match x,y with
| None,None => true
| Some n1,Some n2 => beq_nat n1 n2
| _,_ => false
end.

Fixpoint nth_list (n:nat) (l:list nat) :option nat :=
match n,l with
| _, [] => None
| O,(h::t) => Some h
| S n,(h::t) => nth_list n t
end.

Fixpoint nth_list_o (n:nat) (l:list (option nat)) :option nat :=
match n,l with
| _, (None::t) => None
| _, [] => None
| S O,(Some h::t) => Some h
| O, _ => None
| S n,(Some h::t) => nth_list_o n t
end.

Fixpoint nth_update (i m:nat) (l:list nat) :list nat :=
match i,l with
| _, [] => []
| O, (h::t) => [m] ++ t
| S n,(h::t) => nth_update n m t
end.

Definition nth_list_update (i m:nat) (l:list nat) :list nat :=
let rest := firstn i l in 
 rest ++ nth_update i m l.

(* Definition sF_nth_update (s: storeF) (f:id) (i m:nat) : storeF :=
  fun x => if beq_id f x then (nth_list_update (i-1) m (s f))
           else s x. *)

Definition value_change (n:nat) :=
  fun m => if beq_nat m n then m else n.

Fixpoint list_update (li:list nat) (n : nat) : list nat :=
  map (value_change n) li.

Fixpoint in_list (li:list (option nat)) (x:option nat) : bool :=
match li with
| [] => false
| t::xli => if beq_op_nat t x then true else in_list xli x
end.

Fixpoint cuttail (li:list nat) : list nat :=
match li with
| [] => []
| [h] => []
| h :: t => h :: cuttail t
end.

Fixpoint cuttail_o (li:list (option nat)) : list (option nat) :=
match li with
| [] => []
| [_] => []
| None :: t => []
| Some h :: t => Some h :: cuttail_o t
end.

Definition get_content (nli:list (option nat)) : list nat :=
let f := fun t => match t with
                 | Some n => n
                 | None => 0
                 end
in (map f nli).

Definition o2v (m:option nat) : nat :=
  match m with
  | Some n => n
  | None => 0
  end.

Definition v2o (m:nat) : option nat :=
  Some m.


Fixpoint all_none (opli:list (option nat)) : bool :=
match opli with
| [] => true
| x::li => if beq_op_nat x None then all_none li
           else false
end.

Fixpoint h_unionB_many (hB:heapB) (locli :list (option nat)) (nli : list (list (option nat))) : heapB :=
match locli,nli with
| bloc::blocs,l::ls => h_unionB_many (hB_update hB (o2v bloc) l) blocs ls
| [],[] => hB
| _,_ => hB
end.

(* Lemma nth_update_neq :forall sF f1 f2 v i n,
   f1 <> f2
-> sF_nth_update (f2 !sf-> v ; sF) f1 i n = 
  (f2 !sf-> v;(sF_nth_update sF f1 i n)).
Proof.
Admitted. *)

Definition BlockSafe stoV stoB stoF (hv:heapV) (hB:heapB) bk bl llist: Prop :=  
    (bkeval stoV stoB stoF bk) = Some bl ->
    hB bl = Some llist ->
    forall l, in_list llist l = true ->
              exists k, hv (o2v l) = Some k.









Inductive ceval: command -> state -> ext_state -> Prop :=
(**旧指令集**)
| E_Skip  : forall stat,
              ceval CSkip stat (St stat)

| E_Ass   : forall stoV stoB stoF hV hB x a n, (aeval stoV a) = n ->
              ceval (CAss x a) (stoV,stoB,stoF,hV,hB)
                       (St ((x !sv-> n; stoV),stoB,stoF,hV,hB))

| E_Seq   : forall c1 c2 st0 st1 opst,
              ceval c1 st0 (St st1) ->
              ceval c2 st1 opst ->
              ceval (CSeq c1 c2) st0 opst
| E_Seq_Ab: forall c1 c2 st0,
              ceval c1 st0 Abt ->
              ceval (CSeq c1 c2) st0 Abt
| E_IfTure: forall stoV stoB stoF hV hB opst b c1 c2,
              beval stoV b = Some true ->
              ceval c1 (stoV,stoB,stoF,hV,hB) opst ->
              ceval (CIf b c1 c2) (stoV,stoB,stoF,hV,hB) opst
| E_IfFalse: forall stoV stoB stoF hV hB opst b c1 c2,
              beval stoV b = Some false ->
              ceval c2 (stoV,stoB,stoF,hV,hB) opst ->
              ceval (CIf b c1 c2) (stoV,stoB,stoF,hV,hB) opst
| E_If_Ab : forall stoV stoB stoF hV hB b c1 c2,
              beval stoV b = None ->
              ceval (CIf b c1 c2) (stoV,stoB,stoF,hV,hB) Abt


| E_WhileEnd : forall b stoV stoB stoF hV hB c,
                 beval stoV b = Some false ->
                 ceval (CWhile b c) (stoV,stoB,stoF,hV,hB) (St (stoV,stoB,stoF,hV,hB))

| E_WhileLoop : forall stoV stoB stoF hV hB opst b c st,
                  beval stoV b = Some true ->
                  ceval c (stoV,stoB,stoF,hV,hB) (St st) ->
                  ceval (CWhile b c) st opst ->
                  ceval (CWhile b c) (stoV,stoB,stoF,hV,hB) opst
| E_WhileLoop_Ab : forall stoV stoB stoF hV hB b c,
                  beval stoV b = Some true ->
                  ceval c (stoV,stoB,stoF,hV,hB) Abt ->
                  ceval (CWhile b c) (stoV,stoB,stoF,hV,hB) Abt
| E_While_Ab :  forall stoV stoB stoF hV hB b c,
                  beval stoV b = None ->
                  ceval (CWhile b c) (stoV,stoB,stoF,hV,hB) Abt

(**分离逻辑的指令集**)
| E_Cons : forall stoV stoB stoF hV hB a n x l,
              aeval stoV a = n ->
              hV l = None ->
              ceval  (CCons x a) (stoV,stoB,stoF,hV,hB)
                       (St ((x !sv-> l; stoV),stoB,stoF,
                            (l !hv-> n; hV), hB))

| E_Lookup : forall stoV stoB stoF hV hB x a1 l n,
                aeval stoV a1 = l ->
                hV l = Some n ->
                ceval (CLookup x a1) (stoV,stoB,stoF,hV,hB) 
                         (St ((x !sv-> n; stoV),stoB,stoF,hV,hB))

| E_Lookup_Ab : forall stoV stoB stoF hV hB x a1 l,
                   aeval stoV a1 = l ->
                   hV l = None ->
                   ceval (CLookup x a1) (stoV,stoB,stoF,hV,hB) Abt

| E_Mutate : forall stoV stoB stoF hV hB a1 a2 n1 n2,
                  aeval stoV a1 = n1 ->
                  aeval stoV a2 = n2 ->
                  in_domV n1 hV ->
                  ceval (CMutate a1 a2) (stoV,stoB,stoF,hV,hB) 
                           (St (stoV,stoB,stoF,(n1 !hv-> n2; hV),hB))

| E_Mutate_Ab : forall stoV stoB stoF hV hB a1 a2 n1,
                     aeval stoV a1 = n1 ->
                     hV n1 = None ->
                     ceval (CMutate a1 a2) (stoV,stoB,stoF,hV,hB) Abt

| E_Dispose : forall stoV stoB stoF hV hB a1 n1,
                 aeval stoV a1 = n1 ->
                 in_domV n1 hV ->
                 ceval
                   (CDispose a1) (stoV,stoB,stoF,hV,hB)
                   (St (stoV,stoB,stoF,(hV_remove hV n1),hB))

| E_Dispose_Ab : forall stoV stoB stoF hV hB a1 n1,
                    aeval stoV a1 = n1 ->
                    hV n1 = None ->
                    ceval (CDispose a1) (stoV,stoB,stoF,hV,hB) Abt

(**新指令集**)
(*文件指令 *)
| E_Fcreate : forall stoV stoB stoF hV hB f bk bloc,
                bkeval stoV stoB stoF bk = Some bloc ->
                 ceval (CFcreate f bk) (stoV,stoB,stoF,hV,hB)
                          (St (stoV,stoB,(f !sf-> [bloc]; stoF),hV,hB))
| E_Fcreate_Abt : forall stoV stoB stoF hV hB f bk,
                 bkeval stoV stoB stoF bk = None ->
                 ceval (CFcreate f bk) (stoV,stoB,stoF,hV,hB) Abt

| E_Fattach : forall stoV stoB stoF hV hB f bk ff bloc,
                        bkeval stoV stoB stoF bk = Some bloc ->
                        ff = stoF f ->
                        ceval (CFattach f bk) (stoV,stoB,stoF,hV,hB)
                                 (St (stoV,stoB,(f !sf-> (ff ++ [bloc]); stoF),hV,hB))

| E_Fattach_Abt : forall stoV stoB stoF hV hB f bk,
                          bkeval stoV stoB stoF bk = None ->
                          ceval (CFattach f bk) (stoV,stoB,stoF,hV,hB) Abt

| E_Fdelete : forall stoV stoB stoF hV hB f,
                ceval (CFdelete f) (stoV,stoB,stoF,hV,hB)
                         (St (stoV,stoB,(f !sf-> nil;stoF),hV,hB))


| E_Flength : forall stoV stoB stoF hV hB f ff m x,
              stoF f = ff ->
              length ff = m ->
              ceval (CFlength x f) (stoV,stoB,stoF,hV,hB)
                    (St ((x !sv-> m;stoV),stoB,stoF,hV,hB))


(*
| E_FBass  : forall stoV stoB stoF hV hB bk f n i ff m e,
              stoF f = ff ->
              aeval stoV e = i ->
              nth_list (i-1) ff = Some n ->
              (bkeval stoV stoB stoF bk) = Some m ->
              ceval (CFBass (BKAddr f e) bk) (stoV,stoB,stoF,hV,hB)
                  (St (stoV,stoB,
                      (f !sf-> nth_list_update (i-1) m ff; stoF)
                      ,hV,hB))



*)




(*块指令*)
| E_Ballocate : forall stoV stoB stoF hV hB b e n bloc loc,
              aeval stoV e = n ->
              hV loc = None ->
              hB bloc = None ->
              ceval (CBalloc b e) (stoV, stoB, stoF, hV, hB)
                    (St (stoV, (b !sb-> bloc; stoB), stoF,
                      (loc !hv-> n;hV), (bloc !hb-> [v2o loc];hB)))

| E_Bnew : forall stoV stoB stoF hV hB b bloc,
              hB bloc = None ->
              ceval (CBnew b) (stoV, stoB, stoF, hV, hB)
                    (St (stoV, (b !sb-> bloc; stoB), stoF, 
                          hV, (bloc !hb-> [];hB)))

| E_Bappend : forall stoV stoB stoF hV hB bk e n loc bloc llist,
              (bkeval stoV stoB stoF bk) = Some bloc ->
              hB bloc = Some llist ->
              (forall l, in_list llist l = true -> exists k, hV (o2v l) = k) ->
              aeval stoV e = n ->
              hV loc = None ->
              ceval (CBappend bk e) (stoV, stoB, stoF, hV, hB)
                    (St (stoV, stoB, stoF, (loc !hv-> n;hV), (bloc !hb-> llist ++ [(v2o loc)];hB)))


| E_Bsize : forall stoV stoB stoF hV hB bk x bloc llist m,
              (bkeval stoV stoB stoF bk) = Some bloc ->
              hB bloc = Some llist ->
              (forall l, in_list llist l = true -> exists k, hV (o2v l) = k) ->
              length llist = m ->
              ceval (CBlength x bk) (stoV,stoB,stoF,hV,hB)
                    (St ((x !sv-> m; stoV),stoB,stoF,hV,hB))


| E_Breplace : forall stoV stoB stoF hV hB bk bloc llist f ff e i,
              (bkeval stoV stoB stoF bk) = Some bloc ->
              hB bloc = Some llist ->
              (forall l, in_list llist l = true -> exists k, hV (o2v l) = k) ->
              ff = stoF f ->
              (aeval stoV e) = i ->
              ceval (CBreplace (FId f) e bk) (stoV,stoB,stoF,hV,hB)
                         (St (stoV,stoB,(f !sf-> nth_list_update i bloc ff ;stoF),hV,hB))


| E_Blookup : forall stoV stoB stoF hV hB bk bloc loc llist e x m j,
              (bkeval stoV stoB stoF bk) = Some bloc ->
              hB bloc = Some llist ->
              (forall l, in_list llist l = true -> exists k, hV (o2v l) = k) ->
              aeval stoV e = j ->
              nth_list_o j llist = Some loc ->
              hV loc = Some m ->
                ceval (CBlookup x bk e) (stoV,stoB,stoF,hV,hB)
                         (St ((x !sv-> m;stoV),stoB,stoF,hV,hB))

| E_Btruncate : forall stoV stoB stoF hV hB bk bloc llist,
              (bkeval stoV stoB stoF bk) = Some bloc ->
              hB bloc = Some llist ->
              (forall l, in_list llist l = true -> exists k, hV (o2v l) = k) ->
              ceval (CBtruncate bk) (stoV,stoB,stoF,hV,hB)
                    (St (stoV,stoB,stoF,hV,(bloc !hb-> cuttail_o llist; hB)) ).

Notation "st '=[' c ']=>' st'" := (ceval c st st') 
                                  (at level 40).








(* | E_Blookup_AbtBK : forall stoV stoB stoF hV hB b bk,
                      (bkeval stoV stoB stoF bk) = None ->
                      ceval (CBlookup b bk) (stoV,stoB,stoF,hV,hB) Abt

| E_Blookup_AbtHp : forall stoV stoB stoF hV hB b bk n,
                      (bkeval stoV stoB stoF bk) = Some n ->
                      hB n = None ->
                      ceval (CBlookup b bk) (stoV,stoB,stoF,hV,hB) Abt

| E_Bass : forall stoV stoB stoF hV hB b bk n,
              (bkeval stoV stoB stoF bk) = Some n ->
              ceval (CBass b bk) (stoV,stoB,stoF,hV,hB)
                       (St (stoV,(b !sb-> n; stoB),stoF,hV,hB))

| E_Bass_Abt : forall stoV stoB stoF hV hB b bk,
                (bkeval stoV stoB stoF bk) = None ->
                ceval (CBass b bk) (stoV,stoB,stoF,hV,hB) Abt

| E_Bmutat : forall stoV stoB stoF hV hB bk1 bk2 n1 n2,
                (bkeval stoV stoB stoF bk1) = Some n1 ->
                (bkeval stoV stoB stoF bk2) = Some n2 ->
                ceval (CBmutat bk1 bk2) (stoV,stoB,stoF,hV,hB)
                         (St (stoV,stoB,stoF,hV,(n1 !hb-> n2; hB)))

| E_Bmutat_AbtBk1 : forall stoV stoB stoF hV hB bk1 bk2,
                      (bkeval stoV stoB stoF bk1) = None ->
                      ceval (CBmutat bk1 bk2) (stoV,stoB,stoF,hV,hB) Abt

| E_Bmutat_AbtBk2 : forall stoV stoB stoF hV hB bk1 bk2 n1,
                      (bkeval stoV stoB stoF bk1) = Some n1 ->
                      (bkeval stoV stoB stoF bk2) = None ->
                      ceval (CBmutat bk1 bk2) (stoV,stoB,stoF,hV,hB) Abt

| E_Bdelete : forall stoV stoB stoF hV hB lbk bk,
                 bkeval stoV stoB stoF bk = Some lbk ->
                 in_domB lbk hB ->
                 ceval
                   (CBdelete bk) (stoV,stoB,stoF,hV,hB)
                         (St (stoV,stoB,stoF,hV,(hB_remove hB lbk)))

| E_BdeleteAbs : forall stoV stoB stoF hV hB bk,
                 bkeval stoV stoB stoF bk = None ->
                 ceval
                   (CBdelete bk) (stoV,stoB,stoF,hV,hB) Abt

| E_BdeleteAbh : forall stoV stoB stoF hV hB lbk bk,
                 bkeval stoV stoB stoF bk = Some lbk ->
                 not_in_domB lbk hB ->
                 ceval
                   (CBdelete bk) (stoV,stoB,stoF,hV,hB) Abt *)





(** * Types: Type Systems *)


(** Our next major topic is _type systems_ -- static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of the simplest
    imaginable language, to introduce the basic ideas of types and
    typing rules and the fundamental theorems about type systems:
    _type preservation_ and _progress_.  In chapter [Stlc] we'll move
    on to the _simply typed lambda-calculus_, which lives at the core
    of every modern functional programming language (including
    Coq!). *)

Require Import Coq.Arith.Arith.
Require Import Maps.
Require Import Imp.
Require Import Smallstep.

Hint Constructors multi.

(* ################################################################# *)
(** * Typed Arithmetic Expressions *)

(** To motivate the discussion of type systems, let's begin as
    usual with a tiny toy language.  We want it to have the potential
    for programs to go wrong because of runtime type errors, so we
    need something a tiny bit more complex than the language of
    constants and addition that we used in chapter [Smallstep]: a
    single kind of data (e.g., numbers) is too simple, but just two
    kinds (numbers and booleans) gives us enough material to tell an
    interesting story.

    The language definition is completely routine. *)

(* ================================================================= *)
(** ** Syntax *)

(** Here is the syntax, informally:

    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t

    And here it is formally: *)

Inductive tm : Type :=
  | iBool : bool -> tm
  | iand : tm -> tm -> tm (*added for imp maybe change tand to impand*)
  | inot : tm-> tm
  | ieq : tm -> tm -> tm
  | ible : tm -> tm -> tm
  | iNum : nat -> tm
  | iplus : tm -> tm -> tm
  | iminus : tm -> tm -> tm
  | imult : tm -> tm -> tm
  | iId : id -> tm
  | iskip : tm
  | iass : tm -> tm ->tm
  | iif : tm -> tm -> tm -> tm
  | ibind : tm -> tm -> tm
  | ijoin : tm -> tm -> tm
  | imeet : tm -> tm -> tm                        
  | iwhile : tm -> tm -> tm.                           

(*
Reserved Notation "t1 '==>' t2" (at level 40).*)
(*
Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')
  | ST_impand : forall t1 t2 t3 ,
      (tif tfalse t1) ==> tfalse
      (tif ttrue t1)==> (tif false t2) ==> tfalse
      ( 
    

where "t1 '==>' t2" := (step t1 t2).

 *)
(* ================================================================= *)
(** ** Typing *)

(** The next critical observation is that, although this
    language has stuck terms, they are always nonsensical, mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)

Inductive sec : Type :=
  | High : sec
  | Low : sec.
            
Inductive ty : Type :=
  | TBool : ty
  | TNat : ty.

Inductive ta : Type :=
  | Ety : ty -> sec -> ta
  | TCom : sec -> ta
  | TId : ty -> sec -> ta.

(*
Inductive prod (A B:Type) : Type :=
  pair : A -> B -> prod A B.

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
*)
Check Ety TBool.
(** In informal notation, the typing relation is often written
    [|- t \in T] and pronounced "[t] has type [T]."  The [|-] symbol
    is called a "turnstile."  Below, we're going to see richer typing
    relations where one or more additional "context" arguments are
    written to the left of the turnstile.  For the moment, the context
    is always empty. *)

Reserved Notation "'|-' t '\in' T" (at level 40).
(*subtyping low into high for further use, low and high as lattice, *)
Inductive has_type : tm -> ta -> Prop :=
  | T_Bool : forall (n: bool) (s: sec),
       |- iBool n \in Ety TBool s
  | T_And : forall (t1: tm) (t2:tm) (s: sec),
       |- t1 \in Ety TBool s ->
       |- t2 \in Ety TBool s ->(* HL->H, LH->H case is not handled here*)
       |- iand t1 t2 \in Ety TBool s
   | T_Not : forall (t1: tm) (t2:tm) (s: sec),
       |- t1 \in Ety TBool s ->
       |- inot t1 \in Ety TBool s
   | T_Eq : forall (t1: tm) (t2:tm) (s: sec),
       |- t1 \in Ety TNat s ->
       |- t2 \in Ety TNat s ->
       |- ieq t1 t2 \in Ety TBool s
   | T_Ble : forall (t1: tm) (t2:tm) (s: sec),
       |- t1 \in Ety TNat s ->
       |- t2 \in Ety TNat s ->
       |- ible t1 t2 \in Ety TBool s 
   | T_Num : forall (n:nat) (s: sec),
       |- iNum n \in Ety TNat s            
   | T_Plus : forall (t1: tm) (t2:tm) (s: sec),
       |- t1 \in Ety TNat s->
       |- t2 \in Ety TNat s->
       |- iplus t1 t2 \in Ety TNat s
   | T_Minus : forall (t1: tm) (t2:tm) (s: sec),
       |- t1 \in Ety TNat s->
       |- t2 \in Ety TNat s->
       |- iminus t1 t2 \in Ety TNat s
   | T_Mult : forall (t1: tm) (t2:tm) (s: sec),
       |- t1 \in Ety TNat s->
       |- t2 \in Ety TNat s->
       |- imult t1 t2 \in Ety TNat s
   | T_Id : forall (n: id) (t: ty) (s: sec),
       |- iId n \in TId t s                
   | T_Skip : forall (s:sec),
       |- iskip \in TCom s (* Verify about flow in skip*)
   | T_Ass : forall (t1: tm) (t2:tm) (t: ty) (s: sec),
       |- t1 \in (TId t) s->
       |- t2 \in Ety t s->
       |- iass t1 t2 \in TCom s 
   | T_If : forall (t1: tm) (t2:tm) (t3: tm) (s:sec),
       |- t1 \in Ety TBool s->
       |- t2 \in TCom s->          
       |- t3 \in TCom s->
       |- iif t1 t2 t3 \in TCom s
   | T_While : forall (t1: tm) (t2:tm) (s: sec) ,
       |- t1 \in Ety TBool s ->
       |- t2 \in TCom s ->
       |- iwhile t1 t2 \in TCom s
   | T_bind : forall (t1: tm) (t2: tm) (s: sec) (s': sec),
       |- t1 \in TCom s' ->(*If t1 Low/High*)
       |- t2 \in TCom s -> (*If t2 High*)
       |- ibind t1 t2 \in TCom s
   | T_meet : forall (t1: tm) (t2: tm) (s: sec),
       |- t1 \in TCom s ->
       |- t2 \in TCom s ->
       |- iand t1 t2 \in TCom s                    
where "'|-' t '\in' T" := (has_type t T).
(*Create a separate inductive type to define T_meet and T_join? *)
Check iif (iBool true) (iNum 5) (iNum 4).

(*will only compile till here cuz examples not modified yet

Example type_not_if :
  ~ ( |- iif (iNum 4) iskip iskip \in TCom).
Proof.      
unfold not. intros.
inversion H.
inversion H3.
Qed.


Example has_bool :
|- (iBool true) \in Ety TBool.
Proof.
- apply T_Bool.
Qed.

(**Example has_num_in_bool :
|- (iBool (iNum 5)) \in Ety TBool.
Proof.
- apply T_Bool.
Qed.**)

Example has_and :
|- (iand (iBool true) (iBool false)) \in Ety TBool.
Proof.
-apply T_And.
+apply T_Bool.
+apply T_Bool.
Qed.
(** -apply T_Bool. why is this not working ?? **)

Example has_num :
|- iNum 5 \in Ety TNat.
Proof.
-apply T_Num.
Qed.

Example has_not :
|- (inot (iBool true)) \in Ety TBool.
Proof.
-apply T_Not.
+apply T_Bool.
Qed.

Example has_equal :
|- (ieq (iNum 4) (iNum 5)) \in Ety TBool.
Proof.
-apply T_Eq.
+apply T_Num.
+apply T_Num.
Qed.

Example has_minus :
|- iminus (iNum 5) (iNum 4) \in Ety TNat.
Proof.
-apply T_Minus.
+apply T_Num.
+apply T_Num.
Qed.

Example has_id :
|- iId (Id 1) \in TId TNat.
Proof.
-apply T_Id.
Qed.

Check iNum 5.
Example has_while :
|- iwhile (iBool true) (iass (iId (Id 0)) (iNum 5)) \in TCom.
Proof.
  apply T_While.
  + apply T_Bool.
  + apply T_Ass with (s:= TNat).
    - apply T_Id.
    - apply T_Num.
Qed.
 
Example has_type_not :
|- (iif (iBool true) (iass (iId (Id 0)) (iNum 5)) (iass (iId (Id 0)) (iNum 4))) \in TCom.
Proof.
  apply T_If.
  + apply T_Bool.
  + apply T_Ass with (s:= TNat).
    - apply T_Id.
    - apply T_Num.   
  + apply T_Ass with (s:= TNat).
    - apply T_Id.
    - apply T_Num.
Qed.

Check iass (iId (Id 0)) (iNum 5).
Example has_ass :
|- (iass (iId (Id 0)) (iNum 5)) \in TCom.
Proof.
  apply T_Ass with (s:= TNat).
  apply T_Id.
  apply T_Num.
  Qed.
Check iass (iass (iId (Id 0)) (iNum 5)) (iass (iId (Id 0)) (iNum 6)).


Example test_not_iif :
~ (|- iif (iNum 4) iskip iskip \in TCom).
Proof.
unfold not. intros.
inversion H.
inversion H3.
Qed.


(*

Example has_not_ass :
~ (|- iass (iass (iId (Id 0)) (iNum 5)) (iass (iId (Id 0)) (iNum 6)) \in TCom).
Proof.

unfold not.
intros.
inversion H.
inversion H2.
Qed.


  apply T_Ass with (s:= TNat).
  apply T_Id.
  apply T_Num.
  Qed.*)

*)


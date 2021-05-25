(**********************************************************************)
(* Copyright 2020 Barry Jay                                           *)
(*                                                                    *) 
(* Permission is hereby granted, free of charge, to any person        *) 
(* obtaining a copy of this software and associated documentation     *) 
(* files (the "Software"), to deal in the Software without            *) 
(* restriction, including without limitation the rights to use, copy, *) 
(* modify, merge, publish, distribute, sublicense, and/or sell copies *) 
(* of the Software, and to permit persons to whom the Software is     *) 
(* furnished to do so, subject to the following conditions:           *) 
(*                                                                    *) 
(* The above copyright notice and this permission notice shall be     *) 
(* included in all copies or substantial portions of the Software.    *) 
(*                                                                    *) 
(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,    *) 
(* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF *) 
(* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND              *) 
(* NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT        *) 
(* HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,       *) 
(* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, *) 
(* OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER      *) 
(* DEALINGS IN THE SOFTWARE.                                          *) 
(**********************************************************************)

(**********************************************************************)
(*              Reflective Programs in Tree Calculus                  *)
(*                  Chapter 3: Tree Calculus                          *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import String Lia.

Set Default Proof Using "Type".


Ltac caseEq f := generalize (refl_equal f); pattern f at -1; case f. 
Ltac auto_t:= eauto with TreeHintDb. 

Open Scope string_scope.
Declare Scope tree_scope.
Open Scope tree_scope. 
  
(* Section 3.3 Tree Calculus *)

(* The type Tree0 supports inductive definitions *) 
Inductive Tree0:  Set :=
  | Ref : string -> Tree0  (* variables are indexed by strings *) 
  | Node : Tree0   
  | App : Tree0 -> Tree0 -> Tree0   
.

Hint Constructors Tree0 : TreeHintDb.

Notation "△" := Node : tree_scope.
Notation "x @ y" := (App x y) (at level 65, left associativity) : tree_scope.

Definition K := △ @ △. 
Definition I := △ @ (△ @ △) @ (△ @ △).
Definition KI := K@I. 
Definition D := △ @ (△ @ △) @ (△ @ △ @ △).
Definition d x := △ @ (△@x).
Definition Sop := d (K @ D)@(d K @(K@D)).


Ltac inv1 prop :=
match goal with
| H: prop (Ref _) |- _ => inversion H; clear H; inv1 prop
| H: prop (_ @ _) |- _ => inversion H; clear H; inv1 prop
| H: prop △ |- _ => inversion H; clear H; inv1 prop
| _ => auto
 end.

(* Equational Theory *)

(* The type Tree is axiomatic, so no inductive definitions ... *) 
Axiom Tree: Set.
Axiom Req : string -> Tree. 
Axiom Noq : Tree.
Axiom Apq : Tree -> Tree -> Tree.


(* The two types are related by quotienting *) 
Fixpoint quotient M :=
  match M with
  | Ref x => Req x
  | Node => Noq
  | M1 @ M2 => Apq (quotient M1) (quotient M2)
  end.

Definition eq_q x y := quotient x = quotient y. 

Notation "x === y" := (eq_q x y) (at level 85) : tree_scope.


(* ... but it does support axioms for equational reasoning *)
Axiom k_eq : forall y z, Apq (Apq (Apq Noq Noq) y) z = y. 
Axiom s_eq : forall x y z, Apq (Apq (Apq Noq (Apq Noq x)) y) z = Apq (Apq y z) (Apq x z). 
Axiom f_eq : forall w x y z, Apq (Apq (Apq Noq (Apq (Apq Noq w) x)) y) z = Apq (Apq z w) x.

Hint Resolve Req Noq Apq k_eq s_eq f_eq : TreeHintDb. 

Ltac ktac := rewrite ? k_eq.
Ltac stac := rewrite ? k_eq.
Ltac ftac := rewrite ? k_eq.

Ltac tree_eq := intros; cbv; repeat (rewrite ? s_eq; rewrite ? k_eq; rewrite ? f_eq); auto. 

Lemma quotient_node: quotient Node = Noq. 
  Proof. auto_t. Qed. 

Lemma quotient_app: forall M1 M2, quotient (M1 @ M2) = Apq (quotient M1) (quotient M2).
Proof. auto_t. Qed.

Lemma eq_q_refl: forall x, x===x.
Proof. unfold eq_q; auto. Qed. 

Lemma eq_q_sym: forall x y, x=== y -> y ===x.
Proof. unfold eq_q; auto. Qed. 

Lemma eq_q_trans: forall x y z, x===y -> y===z -> x === z.
Proof.  unfold eq_q; intros; eapply eq_trans; eauto. Qed. 


Ltac f_equal_q := rewrite quotient_app; apply eq_sym; rewrite quotient_app; apply eq_sym; f_equal.


Ltac unquotient_tac := repeat rewrite <- quotient_node; repeat rewrite <- quotient_app.
  

Ltac qtac e :=
  unfold eq_q; repeat ((rewrite e || auto_t) || rewrite quotient_app);
  rewrite ? quotient_node;
  repeat (rewrite ? s_eq || rewrite ? k_eq || rewrite ? f_eq); unquotient_tac; auto_t. 


(* Section 3.4: Programs *) 

Inductive program : Tree0 -> Prop :=
| pr_leaf : program △
| pr_stem : forall M, program M -> program (△ @ M)
| pr_fork : forall M N, program M -> program N -> program (△ @ M @ N)
.

Ltac program_tac := cbv; repeat (apply pr_fork || apply pr_stem || apply pr_leaf); auto.


(* Section 3.5: Propositional Logic *) 

(* Booleans *)

Definition conjunction := d (K@KI).
Definition disjunction := d (K@K) @I.
Definition implies := d (K@K). 
Definition negation := d (K@K) @ (d (K@KI) @ I).
Definition bi_implies := △@ (△@ I @ negation)@△.


Lemma conjunction_true : forall y, conjunction @ K @ y === y. 
Proof.  tree_eq. Qed. 
 


(* Section 3.6: Pairs *) 

Definition Pair := △ .
Definition first p :=  △@ p@ △@ K.
Definition second p := △ @p@ △@ KI.

Lemma first_pair : forall x y, (first (Pair @x@y)) === x. 
Proof.   tree_eq. Qed.  

Lemma second_pair : forall x y, second (Pair @x@y) === y .
Proof.  tree_eq. Qed.  


 
(* 3.7: Natural Numbers *)

Definition zero := △. 
Definition successor := K. 

Definition isZero := d (K@ (K@ (K@ KI))) @ (d (K@ K) @ △).

Definition predecessor := d (K@ KI) @ (d (K@ △) @  △).


Lemma isZero_zero : isZero @ △ === K.
Proof.  tree_eq. Qed.  

Lemma isZero_successor : forall n, isZero @ (K@ n) === KI. 
Proof.  tree_eq. Qed.  


(* Section 3.8: The Fundamental Queries *)

Definition query is0 is1 is2 :=
  d (K@is1)
   @(d (K@KI)
      @(d (K@ (K@ (K@(K@(K@ is2)))))
         @(d (K@(K@(K@ is0)))@△))).


Definition isLeaf := query K (K @ I) (K @ I).
Definition isStem := query (K @ I) K KI.
Definition isFork := query KI KI K.


Lemma query_eq_0:
  forall is0 is1 is2, query is0 is1 is2 @  △ === is0.
Proof.   tree_eq. Qed. 

Lemma query_eq_1: 
  forall is0 is1 is2 P,  query is0 is1 is2 @ (△ @ P) === is0 @ KI @ is1.
Proof. tree_eq.  Qed. 

Lemma query_eq_2:
  forall is0 is1 is2 P Q,  query is0 is1 is2 @ (△@ P@ Q) === is2.
Proof. tree_eq. Qed. 


Ltac unfold_op := unfold isLeaf, isStem, isFork, query, Sop, D, KI, I, K, d, first, second.
Ltac eqtac := unfold_op; qtac s_eq; auto_t. 
(* 
  repeat (unfold quotient; fold quotient; rewrite ? s_eq; rewrite ? k_eq; rewrite ? f_eq).
 *)

Fixpoint term_size M :=
  match M with
  | App M1 M2 => term_size M1 + term_size M2
  |  _ => 1
  end.


(* Exercises *)

(* 1 *)

Definition D_variant := Sop @ (K@(Sop @ Sop)) @ K.

Lemma d_variant_eval: forall x y z, D_variant @ x @ y @ z === y@ z @ (x @ z).
Proof. tree_eq. Qed. 

(* 2 *)
Lemma conjunction_false: forall y, conjunction @ KI @ y === K@I.
Proof.  tree_eq. Qed. 

(* 3 *) 
Lemma disjunction_true : forall y, disjunction @ K @y === K.
Proof.  tree_eq. Qed. 
 
Lemma disjunction_false: forall y, disjunction @ KI @y === y. 
Proof.  tree_eq. Qed.  

Lemma implies_true : forall y, implies @ K @ y === y. 
Proof.  tree_eq. Qed.  

Lemma implies_false: forall y, implies @ KI @ y === K.
Proof.  tree_eq. Qed.  

Lemma negation_true : negation @ K === KI.
Proof.  tree_eq. Qed.  

Lemma negation_false : negation @ (K@I) === K.
Proof.  tree_eq. Qed. 

Lemma iff_true : forall y, bi_implies @K@y === y. 
Proof.  tree_eq. Qed. 

Lemma iff_false_true : bi_implies @ KI @K === K@I.
Proof.  tree_eq. Qed. 

Lemma iff_false_false : bi_implies @ KI @ KI === K.
Proof.  tree_eq. Qed. 

(* 4 *)
Definition first0 := d (K@K) @ (d (K@ △) @ △).
Definition second0 := d (K@(K@I)) @ (d (K@ △) @ △).

Lemma first0_first: forall p, first0 @ p === (first p).
Proof.  tree_eq. Qed. 

Lemma second0_second: forall p, second0 @ p === (second p).
Proof.  tree_eq. Qed. 

(* 5 *)

Lemma predecessor_zero: predecessor @ △ === △. 
Proof.  tree_eq. Qed.  

Lemma predecessor_successor : forall n, predecessor @ (K@ n) === n.
Proof.  tree_eq. Qed.

(* 6 *)

Definition successor_variant := △.
Definition isZero_variant := d (K @ KI) @ (d (K@K) @ △).

Definition predecessor_variant :=
 d (K@K)
   @ (d (K@ (K@(K@ △)))
        @ (d (d (K@ △) @ I) @ (K@△))
     ).

Lemma predecessor_variant_zero: predecessor_variant @ △ === △. 
Proof.  tree_eq. Qed.  

Lemma predecessor_successor_variant : forall n, predecessor_variant @ (successor_variant @ n) === n.
Proof.  tree_eq. Qed.


Lemma isZero_variant_Zero : isZero_variant @ zero === K.
Proof. tree_eq. Qed.

Lemma isZero_variant_successor : forall n, isZero_variant @ (successor_variant @ n) === KI.
Proof. tree_eq. Qed. 

(* 7 *)

Lemma isLeaf_node: isLeaf @ △ === K.
Proof.  tree_eq. Qed. 

Lemma isLeaf_K: isLeaf @ K === KI.
Proof.  tree_eq. Qed. 

Lemma isLeaf_Knode: isLeaf @ (K@△) === KI.
Proof.  tree_eq. Qed. 

(* 8 *)

Fixpoint maxdepth n :=
  match n with
    0 => 0
  | S k => (1 + maxdepth k + maxdepth k * maxdepth k) (* count leaves, stems and forks *) 
  end.

(*
Compute (maxdepth 3 = 13).
Compute (maxdepth 4 = 183).
Compute (maxdepth 5 = 33673). 
*) 

Definition exactdepth n := 
  match n with
  | 0 => 0
  | S k => (maxdepth (S k) - (maxdepth k))
  end.
    
(*
Compute (exactdepth 3 = 10%Z).
Compute (exactdepth 4 = 170%Z).
Compute (exactdepth 5 = 33490%Z). 
*) 

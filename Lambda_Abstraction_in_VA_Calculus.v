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
(*            Reflective Programming in Tree Calculus                 *)
(*          Chapter 9: Lambda-Abstraction in VA-Calculus              *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith Lia Bool List String.
Require Import Reflective.Rewriting_partI.
Require Import Incompleteness_of_Combinatory_Logic.

Set Default Proof Using "Type".


Ltac auto_t := eauto with TreeHintDb.
Ltac eapply2 H := eapply H; auto_t.

Ltac split_all := simpl; intros; 
match goal with 
| H : _ /\ _ |- _ => inversion_clear H; split_all
| H : exists _, _ |- _ => inversion H; clear H; split_all 
| _ =>  try (split; split_all); try contradiction
end; try congruence; auto_t.

Ltac exist x := exists x; split_all.

(* Section 9.2: VA-Calculus *) 

Inductive VA:  Set :=
  Ref : string -> VA 
| Vop 
| Lam                                                      
| App : VA -> VA -> VA
.

Declare Scope va_scope.
Open Scope va_scope. 


Notation "x @ y" := (App x y) (at level 65, left associativity) : va_scope.

Definition v x := App Vop x. 

Fixpoint size M :=
  match M with
  | Ref _ => 1 
  | Vop => 1
  | Lam => 1 
  | M1 @ M2 => S (size M1 + size M2)
  end.

Lemma size_positive: forall M, size M >0.
Proof. induction M; split_all; lia. Qed.



(* Multiple reduction steps *) 

Inductive multi_step : (VA -> VA -> Prop) -> VA -> VA -> Prop :=
  | zero_red : forall red M, multi_step red M M
  | succ_red : forall (red: VA-> VA -> Prop) M N P, 
                   red M N -> multi_step red N P -> multi_step red M P
.
Hint Constructors multi_step: TreeHintDb.  


Definition transitive red := forall (M N P: VA), red M N -> red N P -> red M P. 
                    
Ltac one_step :=
  try red; 
match goal with 
| |- multi_step _ _ ?N => apply succ_red with N; auto_t
end.


Lemma transitive_red : forall red, transitive (multi_step red). 
Proof. red. intros red M N P r1; induction r1; split_all.   Qed. 

Definition preserves_appl (red : VA -> VA -> Prop) := 
forall M N M', red M M' -> red (M@ N) (M' @ N).

Definition preserves_appr (red : VA -> VA -> Prop) := 
forall M N N', red N N' -> red (M@ N) (M@ N').

Definition preserves_app (red : VA -> VA -> Prop) := 
forall M M', red M M' -> forall N N', red N N' -> red (M@ N) (M' @ N').

Lemma preserves_appl_multi_step : 
forall (red: VA -> VA -> Prop), preserves_appl red -> preserves_appl (multi_step red). 
Proof. red. intros red al M N M' r; induction r; auto_t. Qed.

Lemma preserves_appr_multi_step : 
forall (red: VA -> VA -> Prop), preserves_appr red -> preserves_appr (multi_step red). 
Proof. red. intros red ar M N N' r; induction r; split_all; eapply2 succ_red. Qed.

Lemma preserves_app_multi_step : 
forall (red: VA -> VA -> Prop), 
preserves_appl red -> preserves_appr red -> 
preserves_app (multi_step red). 
Proof.
  red. intros red al ar M M' r N N' r2.
  apply transitive_red with (M' @ N). 
  eapply2 preserves_appl_multi_step.
  eapply2 preserves_appr_multi_step.
Qed.


Ltac inv1 prop := 
  match goal with
  | H : prop (Ref _) |- _ => inversion H; clear H; subst;  inv1 prop
  | H : prop Vop |- _ => inversion H; clear H; subst;  inv1 prop
  | H : prop Lam |- _ => inversion H; clear H; subst;  inv1 prop
  | H : prop (_ @ _) |- _ => inversion H; clear H; subst;  inv1 prop
  | _ => split_all
 end.

Ltac inv red := 
  match goal with
  | H : red (Ref _) _ |- _ => inversion H; clear H; subst;  inv red
  | H : red Vop _ |- _ => inversion H; clear H; subst;  inv red
  | H : red Lam _ |- _ => inversion H; clear H; subst;  inv red
  | H : red (_ @ _) _ |- _ => inversion H; clear H; subst;  inv red
  | H : multi_step red (Ref _) _ |- _ => inversion H; clear H; subst;  inv red
  | H : multi_step red Vop  _ |- _ => inversion H; clear H; subst;  inv red
  | H : multi_step red Lam _ |- _ => inversion H; clear H; subst;  inv red
  | H : multi_step red (_ @ _) _ |- _ => inversion H; clear H; subst;  inv red
  | _ => split_all
 end.

(* lambda reduction  *) 



Inductive va_red1 : VA -> VA -> Prop :=
(* variables and abstractions *)
| v_red : forall M N P, va_red1 (Vop @ M @ N @ P) (Vop @ (Vop @ M @ N) @ P)
(* substitution *)
| r_v_red: forall P Q,  va_red1 (Lam @ Vop @ P @ Q)  Q (* the zero index *) 
| r_v1_red : forall M P Q,  va_red1 (Lam @ (Vop @ M) @ P @ Q) (P @ M) (*  successor indices *) 
| r_v2_red : forall M N P Q, va_red1 (Lam @ (Vop @ M @ N) @ P @ Q) (Lam @ M @ P @ Q @ (Lam @ N @ P @ Q))
| r_l_red : forall P Q, va_red1 (Lam @ Lam @ P @ Q) Lam 
| r_l1_red : forall M P Q, va_red1 (Lam @ (Lam @ M) @ P @ Q) (Lam @ Q @ M @ P) (* for environments *) 
| r_l2_red : forall M N P Q, va_red1 (Lam @ (Lam @ M @ N) @ P @ Q) (Lam @ M @ (Lam @ N @ P @ Q))
(* applications *)
| appl_va_red :  forall M M' N, va_red1 M M' -> va_red1 (M @ N) (M' @ N)  
| appr_va_red :  forall M N N', va_red1 N N' -> va_red1 (M @ N) (M @ N')
.

Hint Constructors va_red1: TreeHintDb.


(* va_red *) 

Definition va_red := multi_step va_red1. 

Lemma preserves_appl_va_red : preserves_appl va_red.
Proof. apply preserves_appl_multi_step. red; auto_t.  Qed.

Lemma preserves_appr_va_red : preserves_appr va_red.
Proof. apply preserves_appr_multi_step. red; auto_t. Qed.

Lemma preserves_app_va_red : preserves_app va_red.
Proof. apply preserves_app_multi_step;  red; auto_t. Qed.


  
Ltac eval_pc := 
intros; repeat (eapply succ_red ; [ auto 10 with TreeHintDb; fail|]); try eapply zero_red.


Definition reflective red := forall (M: VA), red M M.

Lemma reflective_va_red: reflective va_red. 
Proof. red; red; auto_t. Qed. 
Hint Resolve reflective_va_red: TreeHintDb.



(* simultaneous reduction *) 



Inductive s_red1 : VA -> VA -> Prop :=
| ref_pred : forall i, s_red1 (Ref i) (Ref i)
| v0_pred : s_red1 Vop Vop
| l0_pred : s_red1 Lam Lam 
(* variables and abstractions *)
| v_pred : forall M M' N N' P P', s_red1 M M' -> s_red1 N N' -> s_red1 P P' ->
                                  s_red1 (Vop @ M @ N @ P) (Vop @ (Vop @ M' @ N') @ P')
(* substitution *)
| r_v_pred: forall P Q Q',  s_red1 Q Q' -> s_red1 (Lam @ Vop @ P @ Q)  Q' 
| r_v1_pred : forall M M' P P' Q, s_red1 M M' -> s_red1 P P' -> s_red1 (Lam @ (Vop @ M) @ P @ Q) (P' @ M')
| r_v2_pred : forall M M' N N' P P' Q Q',
    s_red1 M M' -> s_red1 N N' -> s_red1 P P' -> s_red1 Q Q' ->
    s_red1 (Lam @ (Vop @ M @ N) @ P @ Q) (Lam @ M' @ P' @ Q' @ (Lam @ N' @ P' @ Q'))
| r_l_pred : forall P Q, s_red1 (Lam @ Lam @ P @ Q) Lam 
| r_l1_pred : forall M M' P P' Q Q', s_red1 M M' -> s_red1 P P' -> s_red1 Q Q' -> s_red1 (Lam @ (Lam @ M) @ P @ Q) (Lam @ Q' @ M' @ P') 
| r_l2_pred : forall M M' N N' P P' Q Q',
    s_red1 M M' -> s_red1 N N' -> s_red1 P P' -> s_red1 Q Q' ->
    s_red1 (Lam @ (Lam @ M @ N) @ P @ Q) (Lam @ M' @ (Lam @ N' @ P' @ Q'))
(* applications *)
| app_s_red :  forall M M' N N', s_red1 M M' -> s_red1 N N' -> s_red1 (M @ N) (M' @ N')
.

Hint Constructors s_red1: TreeHintDb.



Definition implies_red (red1 red2: VA-> VA-> Prop) := forall M N, red1 M N -> red2 M N. 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (multi_step red1) (multi_step red2).
Proof.
  red. intros red1 red2 IR M N R; induction R; split_all. 
  apply transitive_red with N; auto. 
Qed. 

Definition diamond (red1 red2 : VA -> VA -> Prop) := 
forall M N, red1 M N -> forall P, red2 M P -> exists Q, red2 N Q /\ red1 P Q. 

Lemma diamond_flip: forall red1 red2, diamond red1 red2 -> diamond red2 red1. 
Proof. unfold diamond; intros red1 red2 d M N r1 P r2; elim (d M P r2 N r1);
       intros x (?&?) ;exists x; split_all. Qed.

Lemma diamond_strip : 
forall red1 red2, diamond red1 red2 -> diamond red1 (multi_step red2). 
Proof.
  red; intros red1 red2 d;  eapply2 diamond_flip; 
  red; intros M N r; induction r; intros P0 r0; auto_t; 
  elim (d M P0 r0 N); auto; intro x; split_all; 
  elim(IHr d x); auto; intros x0 (?&?); exists x0; split; auto_t; eapply2 succ_red. 
Qed. 


Definition diamond_star (red1 red2: VA -> VA -> Prop) := forall  M N, red1 M N -> forall P, red2 M P -> 
  exists Q, red1 P Q /\ multi_step red2 N Q. 

Lemma diamond_star_strip: forall red1 red2, diamond_star red1 red2 -> diamond (multi_step red2) red1 .
Proof. 
red; intros red1 red2 d M N r; induction r; intros P0 r0; auto_t; 
elim(d M P0 r0 N); auto; intro x; split_all;
elim(IHr d x); auto; intros x0 (?&?); exists x0; split; auto_t; eapply2 transitive_red.
Qed. 

Lemma diamond_tiling : 
forall red1 red2, diamond red1 red2 -> diamond (multi_step red1) (multi_step red2).
Proof. 
  red;  intros red1 red2 d M N r;  induction r as [| red3 Q R T r1 ]; intros P0 r0; auto_t; 
  elim(diamond_strip red3 red2 d _ _ r1 P0); auto; intros x; split_all;
  elim(IHr d x); auto; intros x0 (?&?); exists x0; auto_t.
Qed. 

Hint Resolve diamond_tiling: TreeHintDb. 



Lemma s_red_refl: forall M, s_red1 M M.
Proof. induction M; split_all. Qed. 

Hint Resolve s_red_refl: TreeHintDb. 
     
Definition s_red := multi_step s_red1.

Lemma preserves_appl_s_red : preserves_appl s_red.
Proof. apply preserves_appl_multi_step. red; auto_t. Qed.

Lemma preserves_appr_s_red : preserves_appr s_red.
Proof. apply preserves_appr_multi_step. red; auto_t. Qed.

Lemma preserves_app_s_red : preserves_app s_red.
Proof. apply preserves_app_multi_step;  red; auto_t. Qed.



Lemma diamond_s_red1_s_red1 : diamond s_red1 s_red1. 
Proof.  
red; intros M N OR; induction OR; split_all; inv s_red1; auto_t; 
[
elim(IHOR1 M'0); elim(IHOR2 N'0); elim(IHOR3 P'0); split_all; exist(Vop @ (Vop @ x1 @ x0) @ x) |
elim(IHOR1 N'2); elim(IHOR2 N'1); elim(IHOR3 N'0); split_all; exist(Vop @ (Vop @ x1 @ x0) @ x) |
elim(IHOR N'); split_all; exist x | 
elim(IHOR1 M'0); elim(IHOR2 P'0);  split_all; exist(x @ x0) | 
elim(IHOR1 N'2); elim(IHOR2 N'0); split_all; exist (x @ x0) |
elim(IHOR1 M'0); elim(IHOR2 N'0); elim(IHOR3 P'0); elim(IHOR4 Q'0);  split_all;
  exist(Lam @ x2 @ x0 @ x @ (Lam @ x1 @ x0 @ x)); auto 20 with TreeHintDb | 
elim(IHOR1 N'2); elim(IHOR2 N'3); elim(IHOR3 N'1); elim(IHOR4 N'0);  split_all;
  exist(Lam @ x2 @ x0 @ x @ (Lam @ x1 @ x0 @ x)); auto 20 with TreeHintDb | 
elim(IHOR1 M'0); elim(IHOR2 P'0); elim(IHOR3 Q'0); split_all; exist (Lam @ x @ x1 @ x0) | 
elim(IHOR1 N'2); elim(IHOR2 N'0); elim(IHOR3 N'); split_all; exist (Lam @ x @ x1 @ x0) | 
elim(IHOR1 M'0); elim(IHOR2 N'0); elim(IHOR3 P'0); elim(IHOR4 Q'0);  split_all;
  exist(Lam @ x2 @ (Lam @ x1 @ x0 @ x)); auto 20 with TreeHintDb | 
elim(IHOR1 N'2); elim(IHOR2 N'3); elim(IHOR3 N'1); elim(IHOR4 N'0);  split_all;
  exist(Lam @ x2 @ (Lam @ x1 @ x0 @ x)); auto 20 with TreeHintDb | 
elim(IHOR1 (Vop @ M'0 @ N'0)); elim(IHOR2 P'); split_all; inv s_red1;
  exist(Vop @ (Vop @ N'4 @ N'3) @ x) |
elim(IHOR2 P); split_all; exist x |
elim(IHOR1 (Lam @ (Vop @ M'0) @ P')); split_all; inv s_red1; exist (N'1 @ N'4) | 
elim(IHOR1 (Lam @ (Vop @ M'0 @ N'0) @ P')); elim(IHOR2 Q'); split_all; inv s_red1;
  exist (Lam @ N'5 @ N'4 @ x @ (Lam @ N'6 @ N'4 @ x)); auto 20 with TreeHintDb |
elim(IHOR1 (Lam @ (Lam @ M'0) @ P')); elim(IHOR2 Q'); split_all; inv s_red1;
  exist (Lam @ x @ N'4 @ N'1) |
elim(IHOR1 (Lam @ (Lam @ M'0 @ N'0) @ P')); elim(IHOR2 Q'); split_all; inv s_red1;
  exist (Lam @ N'5 @ (Lam @ N'6 @ N'4 @ x)); auto 20 with TreeHintDb | 
elim(IHOR1 M'0); elim(IHOR2 N'0); split_all
].
Qed.



Hint Resolve diamond_s_red1_s_red1: TreeHintDb.

Lemma diamond_s_red1_s_red : diamond s_red1 s_red.
Proof. eapply2 diamond_strip. Qed. 

Lemma diamond_s_red : diamond s_red s_red.
Proof.  eapply2 diamond_tiling. Qed. 
Hint Resolve diamond_s_red: TreeHintDb.



Lemma va_red1_to_s_red1 : implies_red va_red1 s_red1. 
Proof.  intros M N R; induction R; split_all. Qed. 


Lemma va_red_to_s_red: implies_red va_red s_red. 
Proof. 
eapply2 implies_red_multi_step. 
red; split_all; one_step; eapply2 va_red1_to_s_red1. 
Qed. 

Lemma to_va_red_multi_step: forall red, implies_red red va_red -> implies_red (multi_step red) va_red. 
Proof. 
red;  intros red B M N R; induction R; split_all; red; split_all; 
assert(va_red M N) by eapply2 B; apply transitive_red with N; auto; eapply2 IHR. 
Qed. 


Lemma s_red1_to_va_red: implies_red s_red1 va_red .
Proof. 
  red;  intros M N OR; induction OR; split_all;
        try (eapply2 succ_red; eapply2 preserves_app_va_red); auto 10; 
          repeat eapply2 preserves_app_va_red.
Qed.


Hint Resolve s_red1_to_va_red: TreeHintDb.

Lemma s_red_to_va_red: implies_red s_red va_red. 
Proof. eapply2 to_va_red_multi_step. Qed.


Lemma diamond_va_red: diamond va_red va_red. 
Proof. 
red; intros M N r1 P r2;  
assert(s1: s_red M N) by eapply2 va_red_to_s_red; 
assert(s2: s_red M P) by eapply2 va_red_to_s_red;   
elim(diamond_s_red M N s1 P); auto; intro x; exist x; split_all; eapply2 s_red_to_va_red. 
Qed. 
Hint Resolve diamond_va_red: TreeHintDb. 


(* Confluence *)

Definition confluence (A : Set) (R : A -> A -> Prop) :=
  forall x y : A,
  R x y -> forall z : A, R x z -> exists u : A, R y u /\ R z u.

Theorem confluence_va_calculus: confluence VA va_red. 
Proof. red; split_all; eapply2 diamond_va_red. Qed. 


(* Programs *)


Ltac zerotac := try eapply2 zero_red.
Ltac succtac :=
  repeat (eapply transitive_red;
  [ eapply2 succ_red ;
    match goal with
    | |- multi_step va_red1 _ _ => idtac
    | _ => fail (*gone too far ! *)
    end
  | ]); zerotac
.
Ltac aptac := eapply transitive_red; [ eapply preserves_app_va_red |].



Definition reducible M := exists N, va_red1 M N.

Inductive program : VA -> Prop := 
| pr_V0 : program Vop
| pr_S: forall M, program M -> program (Vop @  M)
| pr_H : forall M N, program M -> program N -> program (Vop @ M @ N)
| pr_A : program Lam
| pr_A1 : forall M, program M ->  program (Lam @ M)
| pr_A2 : forall M N, program M -> program N -> program (Lam @ M @ N)
.

Hint Constructors program: TreeHintDb.

Ltac program_tac :=
  match goal with
  | |- program  Vop => eapply2 pr_V0; program_tac
  | |- program (Vop @  _) => eapply2 pr_S; program_tac
  | |- program (Vop @ _ @ _) => eapply2 pr_H; program_tac
  | |- program  Lam => eapply2 pr_A; program_tac
  | |- program (Lam @  _) => eapply2 pr_A1; program_tac
  | |- program (Lam @ _ @ _) => eapply2 pr_A2; program_tac
  | |- _ => idtac
  end.                                      


Definition valuable M := exists N,  va_red M N /\ program N.



Lemma programs_are_irreducible: forall M, program M -> forall N, va_red1 M N -> False.
Proof.
  intros M p; induction p; intros N0 r; inversion r; subst; inv va_red1; invsub;
  ((eapply2 IHp; fail) || (eapply2 IHp1; fail) || eapply2 IHp2).
Qed.



Lemma programs_are_stable: forall M, program M -> forall N, s_red1 M N -> N = M.
Proof.
  intros M p; induction p; intros N0 r; inversion r; subst; inv s_red1; invsub; 
  (match goal with H : s_red1 _ ?N |- _ =>  rewrite (IHp N); auto; fail end) || 
  (rewrite (IHp1 M'); auto;  rewrite (IHp2 N'); auto; fail) ||
  rewrite (IHp1 N'0); auto;   rewrite (IHp2 N'); auto.
Qed. 


Lemma programs_are_stable2: forall M N, s_red M N -> program M -> N = M.
Proof.
  cut(forall red M N, multi_step red M N -> red = s_red1 -> program M -> N = M); 
  [ intro H; intros; eapply H; eauto |
  intros red M N r; induction r; split_all; subst; 
  assert(N = M) by eapply2 programs_are_stable; subst; auto
    ]. 
  Qed.


Lemma triangle_s_red : forall M N P, s_red M N -> s_red M P -> program P -> s_red N P.
Proof.
  intros; assert(d: exists Q, s_red N Q /\ s_red P Q) by eapply2 diamond_s_red;
  elim d; auto; intro x; split_all;   
  assert(x = P) by eapply2 programs_are_stable2;  subst; auto. 
Qed.

Lemma refs_are_stable: forall x M, s_red (Ref x) M -> M = Ref x.
Proof.
  cut (forall red P M, multi_step red P M -> red = s_red1 -> forall x, P = Ref x -> M = Ref x); 
  [ intro aux; intros; subst;    eapply2 aux |
  intros red P M r;  induction r as [ | ???? r1]; split_all; subst; inversion r1; subst; eapply2 IHr]. 
Qed.


(* 9.3 : Combinators *)



(* Star Abstraction *)

Fixpoint substitute M x N :=
  match M with
  | Ref s => if s =? x then N else Ref s
  | Vop => Vop
  | Lam => Lam
  | M1 @ M2 => (substitute M1 x N) @ (substitute M2 x N)
  end.


Fixpoint bracket_body M x:=
  match M with
    Ref s => if s =? x then Vop else Vop @ (Ref s)
  | Vop => Vop @ Vop
  | Lam => Vop @ Lam
  | M1 @ M2 => Vop @ (bracket_body M1 x) @ (bracket_body M2 x)
  end. 

Definition bracket x M := Lam @ (bracket_body M x) @ (Lam @ Vop @ Lam).

Lemma bracket_beta: forall M x N, va_red (bracket x M @ N) (substitute M x N).
Proof.
  induction M; unfold bracket; split_all; succtac;
    [caseEq (s=?x); split_all; succtac
    | aptac; [ eapply2 IHM1 | eapply2 IHM2 | zerotac]
    ]. 
Qed.


Inductive combination : VA -> Prop :=
| is_Vop : combination Vop
| is_Lam : combination Lam 
| is_App : forall M N, combination M -> combination N -> combination (M@ N)
.
Hint Constructors combination : TreeHintDb. 

Lemma programs_are_combinations: forall p, program p -> combination p.
Proof. intros p pr; induction pr; split_all. Qed. 
       

Fixpoint occurs x M :=
  match M with
  | Ref y => eqb y x 
  | Vop | Lam => false
  | M1 @ M2 => (occurs x M1) || (occurs x M2)
  end.

Lemma occurs_combination: forall M x,  combination M -> occurs x M = false.
Proof. induction M; intros x c; inversion c; subst;simpl;auto; rewrite IHM1; auto; rewrite IHM2; auto. Qed. 


Lemma substitute_occurs_false: forall M x N, occurs x M = false -> substitute M x N = M. 
Proof.
  induction M; intros x N occ; simpl in *; auto; 
    [ rewrite occ; auto
    | rewrite orb_false_iff in *; inversion occ; rewrite IHM1; auto; rewrite IHM2; auto
    ]. 
Qed.


Fixpoint star_body x M :=
  match M with
  | Ref s =>  if s =? x then Vop else Vop @ (Ref s)
  | Vop => Vop @ Vop
  | Lam => Vop @ Lam 
  | M1 @ M2 => if occurs x (M1 @ M2)
                 then Vop @ (star_body x M1) @ (star_body x M2)
                 else Vop @ (M1 @ M2)
  end. 

Definition star x M := Lam @ (star_body x M) @ (Lam @ Vop @ Lam). 


Lemma star_id: forall x, star x (Ref x) = Lam @ Vop @ (Lam @ Vop @ Lam).
Proof. intro; unfold star, star_body, occurs; rewrite eqb_refl; auto. Qed.


Lemma star_body_occurs_false: forall M x, occurs x M = false -> star_body x M = Vop @ M. 
Proof. induction M; intros x occ;  unfold star_body; simpl in *; rewrite ? occ; auto. Qed.

Lemma star_occurs_false: forall M x, occurs x M = false -> star x M = Lam @ (Vop @ M) @ (Lam @ Vop @ Lam). 
Proof. induction M; intros x occ;  unfold star, star_body; simpl in *; rewrite ? occ; auto. Qed.


Notation "\" := star : va_scope.

Theorem star_beta: forall M x N, va_red (\x M @ N) (substitute M x N).
Proof.
  induction M; split_all; unfold star, star_body; fold star_body;
  [ caseEq (s=? x); split_all; cbv; succtac
  | cbv; succtac
  | cbv; succtac
  | caseEq (occurs x (M1 @ M2)); split_all; succtac; 
    [ aptac; [ eapply2 IHM1 | eapply2 IHM2 | zerotac]
    | succtac; rewrite orb_false_iff in *; split_all;
      rewrite ! substitute_occurs_false; auto; cbv; succtac
  ]].
Qed. 


Fixpoint ndx k :=
  match k with
  | 0 => Vop
  | S k1 => Vop @  (ndx k1)
  end.


Fixpoint env args := 
  match args with
  | nil => Lam @ Vop @ Lam 
  | cons a args1 => Lam @ (Lam @ (env args1)) @ a
  end. 

(* 
Fixpoint env_comb args := 
  match args with
  | nil => Lam @ Vop @ Lam 
  | cons a args1 => Vop @ (Vop @ Lam @ (Vop @ Lam @ (env_comb args1))) @ a
  end. 
*) 

Lemma succ_ndx_red : forall M sigma N, va_red (Lam @ (Vop @ M)  @ sigma @ N) (sigma @ M).
Proof. intros; cbv; succtac. Qed. 
  
 
Lemma env_nil_red : forall  M, va_red (env nil @ M) M.
Proof. intros; unfold env; fold env; succtac.  Qed. 

Lemma env_cons_red :
  forall a args M, va_red (env(cons a args) @ (Vop @ M)) (env args @ M).
Proof.  intros; unfold env; fold env; succtac. Qed. 

Lemma env_zero_red : forall a args , va_red (env(cons a args) @ Vop) a.
Proof.  intros; unfold env; fold env; succtac. Qed. 

Lemma env_succ_red: forall a args x , va_red (env(cons a args) @ (Vop@ x)) (env args @ x).
Proof.  intros; unfold env; fold env; succtac. Qed. 

                                      
(* Combinators *)

Definition Iop := Lam @ Vop @ Lam . 

Definition Kop := Lam @ (Lam @ (v Vop) @ (Lam @ (Lam @ (Lam @ Vop @ Lam)) @ Vop)) @ Lam . 

Definition Sop := Eval cbv in \"x" (\"y" (\"z" (Ref "x" @ Ref "z" @ (Ref "y" @ Ref "z")))). 
              
Definition KI := Lam @ Iop @ Lam.

Lemma i_red : forall M, va_red (Iop @ M) M.
Proof. intros; cbv; succtac. Qed. 

Lemma ki_red : forall M N, va_red (KI @ M @ N) N.
Proof. intros; cbv; succtac. Qed.

Lemma k_red : forall M N, va_red (Kop @ M @ N) M. 
Proof.  intros; cbv; succtac. Qed. 

  
Lemma sop_red: forall M N P, va_red (Sop @ M @ N @ P) (M@P@(N@P)). 
Proof.
  intros; cbv; succtac. aptac. succtac. zerotac. aptac. aptac. aptac. aptac. zerotac.
  aptac. aptac. succtac. succtac. zerotac. zerotac. zerotac. zerotac. zerotac. succtac.  zerotac.
  succtac. zerotac.   succtac. aptac. succtac.  aptac. aptac. aptac. succtac. aptac. aptac. succtac.
  succtac. all: zerotac. succtac. apply preserves_app_va_red. 2: zerotac. aptac. aptac. aptac. zerotac.
  aptac. aptac. succtac. succtac. all: zerotac. succtac.
Qed.


  
Definition meaningful_translation_SK_to_VA f :=
  (forall M N, sk_red1 M N -> va_red (f M) (f N)) /\ (* strong version *) 
  (forall M N, f (Incompleteness_of_Combinatory_Logic.App M N) = App (f M) (f N)) /\  (* applications *) 
  (forall M, Incompleteness_of_Combinatory_Logic.program M -> valuable (f M)) /\ (* programs *) 
  (forall i, f (Incompleteness_of_Combinatory_Logic.Ref i) = Ref i) .              (* variables *) 

Fixpoint sk_to_va M :=
  match M with
  | Incompleteness_of_Combinatory_Logic.Ref i => Ref i
  | Incompleteness_of_Combinatory_Logic.Sop => Sop
  | Incompleteness_of_Combinatory_Logic.Kop => Kop
  | Incompleteness_of_Combinatory_Logic.App M1 M2 => (sk_to_va M1) @ (sk_to_va M2)
  end.


Lemma preserves_reduction1_sk_to_va:
  forall M N, sk_red1 M N -> va_red (sk_to_va M) (sk_to_va N).
Proof.
  intros M N r; induction r; subst; split_all; 
  [eapply2 sop_red | eapply2 k_red | | ]; eapply2 preserves_app_va_red.
Qed.


Lemma preserves_reduction_sk_to_va:
  forall M N, sk_red M N -> va_red (sk_to_va M) (sk_to_va N).
Proof.
  cut (forall red M N, Incompleteness_of_Combinatory_Logic.multi_step red M N -> red = sk_red1 ->
                       va_red (sk_to_va M) (sk_to_va N)); 
    [ intro aux; intros;   eapply2 aux
    | intros red M N r; induction r; subst; split_all; subst;
      eapply transitive_red; [ eapply2 preserves_reduction1_sk_to_va | eapply2 IHr]]. 
Qed.


Theorem meaningful_translation_from_sk_to_va:
  meaningful_translation_SK_to_VA sk_to_va. 
Proof.
  red; repeat split;     
    [ eapply2 preserves_reduction1_sk_to_va
    | intros M prM; induction prM].   
  { exists Sop;   split; [ apply zero_red | cbv; auto; program_tac]. }
  {
  elim IHprM; intro x; split_all. repeat eexists. 
  unfold Sop. aptac. 2: eassumption. succtac.
  eapply transitive_red. 
  succtac. eapply transitive_red. succtac. aptac.  aptac. zerotac. aptac. aptac. zerotac.
  succtac. 1-5:  zerotac. aptac.  aptac. zerotac. aptac. aptac. zerotac. aptac. succtac.
  aptac. aptac. zerotac. aptac. zerotac. aptac. succtac. succtac. all: zerotac.
  program_tac.   }
{
  elim IHprM1; intro x; split_all; elim IHprM2; intro x0; split_all. 
   red. repeat eexists.  aptac. aptac. zerotac. eassumption. zerotac. eassumption. 
   unfold Sop. aptac.  succtac. zerotac.
   eapply transitive_red. succtac.  
   aptac. aptac. aptac. aptac. zerotac. succtac. succtac. zerotac. aptac.  aptac. zerotac. aptac.
   zerotac. aptac. aptac. zerotac. aptac. zerotac. aptac.   succtac. succtac. 1-6:  zerotac. succtac.
   zerotac. succtac. zerotac. succtac. zerotac.
   aptac.  aptac. zerotac. aptac. zerotac. aptac. aptac. zerotac. aptac. succtac. succtac. 
   1-8: zerotac.   program_tac. } 
  {exist Kop; unfold Kop, v; cbv; program_tac. }
  {
    elim IHprM; intro x; split_all; repeat eexists;
      [ aptac; [ zerotac | eassumption | unfold Kop, v; succtac] |  program_tac].
  }
Qed.



(* 9.4: Incompleteness *)


Definition is_equal eq :=
  (forall M, program M -> va_red (eq @ M @ M @ (Ref "x") @ (Ref "y")) (Ref "x"))
/\ 
( forall M N, program M -> program N -> M <> N ->
              va_red (eq @ M @ N @ (Ref "x") @ (Ref "y")) (Ref "y")). 

  

Definition identity_program id := program id /\ va_red (App id (Ref "x")) (Ref "x").
Definition identity_value id := valuable id /\ va_red (App id (Ref "x")) (Ref "x").
                       

Inductive id_red : VA -> VA -> Prop :=
| id_id : id_red  (Lam @ Vop @ (Lam @ Vop @ Lam)) (Lam @ Vop @ Lam)
| id_ref: forall i, id_red (Ref i) (Ref i)
| id_V : id_red Vop Vop 
| id_A : id_red Lam Lam 
| id_app : forall M M' N N', id_red M M' -> id_red N N' -> id_red (M @ N) (M' @ N')  
.
Hint Constructors id_red: TreeHintDb.


Lemma id_red_refl: forall M, id_red M M.
Proof. induction M; auto_t. Qed.

  
(* The pentagon for s_red1 *)

Fixpoint term_size M :=
  match M with
  Ref _ => 1 
| Vop  => 1 
| Lam => 1
| App M1 M2 => term_size M1 + term_size M2
  end.

Lemma term_size_positive: forall M, term_size M > 0.
Proof. induction M; split_all; lia. Qed. 
       

Lemma pentagon_id_red_s_red1:
  forall M N,  id_red M N ->
               forall P, s_red1 M P ->
                         exists Q1 Q2,  s_red P Q1 /\ id_red Q1 Q2 /\
                                        s_red N Q2 .
Proof.
  Ltac IHtac IHk k :=
    match goal with
  | H : id_red ?x ?y , H2 : s_red1 ?x ?z |- _ =>
    assert(sx: term_size x < k) by lia; elim (IHk x sx y H z); split_all; clear H sx
  end.
   cut (forall k M, term_size M < k ->
                   forall N,  id_red M N ->
                                forall P, s_red1 M P ->
                                          exists Q1 Q2,  s_red P Q1 /\ id_red Q1 Q2 /\
                                                         s_red N Q2 ); 
     [ intro aux; intros; eapply2 aux 
     | induction k; intros M s N ir P r; simpl in *; [ lia |  inversion ir; subst; split_all]]. 
   { inv s_red1;  exist (Lam @ Vop @ Iop);  exist Iop;  unfold Iop;  zerotac. } 
   { inv s_red1; exist(Ref i); exist (Ref i); apply zero_red. }
   { inv s_red1; exists Vop; exist Vop; apply zero_red. }
   { inv s_red1; exists Lam; exist Lam; zerotac. } 
  inversion r; clear r ir; subst; inv id_red; simpl in *; inv s_red1;   repeat (IHtac IHk k). 
   {
  exist (v (v  x3 @ x1) @ x); exist (v (v  x4 @ x2) @ x0); unfold v; auto; zerotac; 
    [ repeat  eapply2 preserves_app_s_red; zerotac
    | auto_t
    | eapply succ_red; [ eapply2 v_pred | repeat  eapply2 preserves_app_s_red; zerotac]]. 
   }
   { exist x; exist x0; eapply2 succ_red. }
   { exist x; exist x0; eapply2 succ_red. }
   { 
     exist (x @ x1); exist (x0 @ x2);
       [ eapply2 preserves_app_s_red; eapply2 zero_red |
         eapply succ_red;   [ eapply2 r_v1_pred | eapply2 preserves_app_s_red]].
   }{ 
     exist (Lam @ x5 @ x1 @ x @ (Lam @ x3 @ x1 @ x));
       exist (Lam @ x6 @ x2 @ x0 @ (Lam @ x4 @ x2 @ x0));  
    [ repeat eapply2 preserves_app_s_red; zerotac
    | auto 20 with TreeHintDb
    | eapply succ_red;  [ eapply2 r_v2_pred | repeat eapply2 preserves_app_s_red; zerotac]].
   }
   { exist Lam; exist Lam; zerotac; eapply2 succ_red. }
  {
    exist (Lam @ x @ x3 @ x1); exist (Lam @ x0 @ x4 @ x2);
      [  repeat (eapply2 preserves_app_s_red); zerotac
       | eapply succ_red; [  eapply2 r_l1_pred | repeat eapply2 preserves_app_s_red; zerotac]].
  }
  { exist (Lam @ Vop @ Iop); exist Iop; [ eapply2 preserves_app_s_red ; zerotac | ]; eapply2 succ_red. }
  {
  exist (Lam @ x5 @ (Lam @ x3 @ x1 @ x)); exist (Lam @ x6 @ (Lam @ x4 @ x2 @ x0)); 
  [ repeat eapply2 preserves_app_s_red; zerotac
  | auto 20 with TreeHintDb
  | eapply succ_red; [ eapply2 r_l2_pred | repeat eapply2 preserves_app_s_red; zerotac]
  ].
  }{
   assert(term_size M0 >0) by eapply2 term_size_positive; 
   assert(term_size N0 >0) by eapply2 term_size_positive;
   repeat (IHtac IHk k); exist (App x1 x); exist (App x2 x0); 
   eapply2 preserves_app_s_red. 
  }
Qed.


(* 
Generalizing the pentagon from s_red1 to s_red 
requires a count of the number of reductions, 
so use s_ranked instead. 
*) 



Inductive s_ranked : nat -> VA -> VA -> Prop :=
| ranked_zero: forall M,  s_ranked 0 M M
| ranked_succ: forall n M N P, s_red1 M N -> s_ranked n N P -> s_ranked (S n) M P
.

Hint Constructors s_ranked: TreeHintDb.

Lemma transitive_s_ranked:
  forall n M N, s_ranked n M N -> forall p P, s_ranked p N P ->
                                              s_ranked (n+p) M P.
Proof. induction n; intros M N r; inversion r; split_all; subst; eapply2 ranked_succ. Qed.

Lemma s_red_implies_s_ranked:
  forall M N, s_red M N -> exists n, s_ranked n M N.
Proof.
  cut(forall red M N, multi_step red M N -> red = s_red1 -> exists n, s_ranked n M N); 
  [ intro aux; intros; eapply aux; eauto
  | intros red M N r; induction r; split_all; subst; auto_t;  
    assert(aux0: exists n, s_ranked n N P) by auto; 
    elim aux0; auto; intro x; exist (S x); eapply2 ranked_succ]. 
Qed. 

  
Lemma s_ranked_implies_s_red:
  forall n M N, s_ranked n M N -> s_red M N.
Proof.
  induction n; intros M N r; inversion r; subst; auto; [apply zero_red | eapply2 succ_red; eapply2 IHn]. 
Qed.


  
Lemma diamond_s_ranked_strip :
  forall m M N, s_ranked m M N ->
                forall P, s_red1 M P ->
                          exists Q, s_ranked m P Q /\ s_red1 N Q.
Proof.
  induction m; intros M N r P rP; inversion r; subst; auto_t;
  assert(d: exists Q, s_red1 N0 Q /\ s_red1 P Q) by (eapply diamond_s_red1_s_red1; eauto);
  elim d; intro x; split_all; 
  assert(d2 : exists Q : VA, s_ranked m x Q /\ s_red1 N Q) by  eapply2 IHm;
  elim d2; auto; intro x1; exist x1; apply ranked_succ with x; auto. 
Qed.



Lemma diamond_s_ranked :
  forall n M N, s_ranked n M N ->
                forall p P, s_ranked p M P ->
                          exists Q, s_ranked n P Q /\ s_ranked p N Q.
Proof.
  induction n; intros M N r p P r2; inversion r; subst; auto_t;
  assert(d: exists Q, s_ranked p N0 Q /\ s_red1 P Q) by eapply2 diamond_s_ranked_strip;
  elim d; intro x; split_all;
  assert(d2 : exists Q : VA, s_ranked n x Q /\ s_ranked p N Q) by eapply2 IHn;
  elim d2; intros x1; exist x1; apply ranked_succ with x; auto. 
Qed.

Lemma pentagon_id_red_s_ranked:
  forall m M P,  s_ranked m M P ->
                 forall N, id_red M N ->
                           exists p Q1 Q2 n,  s_ranked p P Q1 /\ id_red Q1 Q2 /\
                                              s_ranked n N Q2 .
Proof.
  induction m; intros M P r N ir; inversion r; clear r; subst; eauto.
  (* 2 *)
  exists 0; exists P; exist N; exist 0; repeat split; auto. 
  (* 1 *)
  assert(pent: exists Q1 Q2,  s_red N0 Q1 /\ id_red Q1 Q2 /\  s_red N Q2) by 
  eapply2 pentagon_id_red_s_red1.
  elim pent; intros x x0; clear pent; split_all. 
  assert(ppr: exists n, s_ranked n N0 x) by (eapply s_red_implies_s_ranked; eauto).
  elim ppr; intro m1; clear ppr;   split_all.
  assert(d: exists Q, s_ranked m x Q /\ s_ranked m1 P Q) by eapply2 diamond_s_ranked. 
  elim d; intros x2;  clear d; split_all.
  assert(pent2: exists p Q1 Q2 n,  s_ranked p x2 Q1 /\ id_red Q1 Q2 /\ s_ranked n x1 Q2). 
  eapply IHm; eauto.
  elim(pent2). intros p; clear pent2; intros pent3; split_all.
  assert(ppr2: exists q, s_ranked q N x1) by eapply2 s_red_implies_s_ranked.
  elim(ppr2); intro q; clear ppr2; split_all.
  exists (m1 + p); exists x0; exists x3; exist (q + x4); eapply transitive_s_ranked; eauto. 
Qed.

Lemma pentagon_id_red_s_red:
  forall M P,  s_red M P ->
               forall N, id_red M N ->
                         exists Q1 Q2,  s_red P Q1 /\ id_red Q1 Q2 /\
                                        s_red N Q2 .
Proof.
  intros M P r N idr. 
  elim(s_red_implies_s_ranked _ _ r); intros.   
  assert(pent: exists p Q1 Q2 n,  s_ranked p P Q1 /\ id_red Q1 Q2 /\ s_ranked n N Q2)
    by eapply2 pentagon_id_red_s_ranked.
  elim pent. intros p; clear pent. intro pent2; elim pent2; intros Q1 pent3; clear pent2.
  elim pent3; intros Q2 n; clear pent3;  split_all. 
  exists Q1; exist Q2.
  all: eapply2 s_ranked_implies_s_red. 
Qed.

  (* 
If parallel reduction is to a variable  
then the pentagon becomes a triangle. -- not used in A_Tree! 
 *)



Lemma triangle_id_red_s_red_ref:
  forall M x, s_red M (Ref x) ->
            forall N, id_red M N ->
                      s_red N (Ref x) .
Proof.
  intros M x r N ir.
  assert(pent: exists Q1 Q2,  s_red (Ref x) Q1 /\ id_red Q1 Q2 /\
                              s_red N Q2) by  eapply2 pentagon_id_red_s_red.
  elim pent. intros Q1 pent2; clear pent.
  elim pent2; intro Q2; clear pent2; split_all.
  assert(Q1 = Ref x) by eapply2 refs_are_stable; subst.
  inv id_red.   
Qed.


Theorem equality_of_programs_is_not_definable_in_va:  forall eq,  not (is_equal eq). 
Proof.
  intros; intro premise; inversion premise as (eq0 & eq1). 
  assert(r: s_red (eq @ Iop @ (Lam @ Vop @ Iop) @ (Ref "x") @ (Ref "y")) (Ref "y")).
  eapply va_red_to_s_red. eapply2 premise. cbv; program_tac. cbv; program_tac. discriminate. 
  elim(pentagon_id_red_s_red (eq @ Iop @ (Lam @ Vop @ Iop) @ (Ref "x") @ (Ref "y")) (Ref "y")
                                  r (eq @ Iop @ Iop @ (Ref "x") @ (Ref "y"))); split_all. 
  2: repeat eapply2 id_app; eapply2 id_red_refl. 
  assert(x = Ref "y") by eapply2 refs_are_stable. subst. 
  inv id_red.   
  assert (r2: s_red (eq @ Iop @ Iop @ (Ref "x") @ (Ref "y")) (Ref "x")).
  eapply2 va_red_to_s_red.
  eapply2 eq0. cbv; program_tac. 
  elim(diamond_s_red _ _ r2 (Ref "y")); auto.  intros x (s1&s2).
  assert(x = Ref "x") by eapply2 refs_are_stable. 
  assert(x = Ref "y") by eapply2 refs_are_stable. subst; discriminate. 
Qed.


(* 9.5 comes after 9.7, for convenience. *) 

(* 9.6: Tagging  *)



Definition tag t f :=
  Lam
    @ (Vop
         @ (Vop
              @ (v (ndx 2) @ (ndx 1))
              @ (v (v (v (v f))) @ Vop)
           )
         @ (v (v (v t))))
    @ (Lam @ (Lam @ (env ((env (Kop :: nil)) :: nil))) @ Vop).


Definition getTag := (* \"" (Lam @ (Ref "") @ Iop @ KI @ Lam). *) 
  Lam @ (v (v (v (v (v Lam) @ Vop) @ (v Iop)) @ (v KI)) @ (v Lam)) @ Iop.


Lemma tag_apply : forall t f x, va_red (tag t f @ x) (f @ x).
Proof.
  intros.  unfold tag, ndx. succtac. aptac. aptac. aptac.  eapply2 env_zero_red.
  zerotac. eapply2 env_zero_red. aptac. eapply2 env_succ_red. zerotac.
  aptac. eapply2 env_nil_red. all: zerotac. unfold Kop;  succtac. 
Qed.


Lemma getTag_tag : forall t f, va_red (getTag @ (tag t f)) t.
Proof.  intros; cbv; succtac. Qed.

Lemma tag_preserves_substitute:
  forall t f x N, substitute (tag t f) x N = tag (substitute t x N) (substitute f x N). 
Proof.  intros; cbv; auto. Qed.

Lemma va_red_preserves_tags:
  forall t t' f f', va_red t t' -> va_red f f' -> va_red (tag t f) (tag t' f').
Proof.  intros; cbv; repeat eapply2 preserves_app_va_red. Qed. 


(* 9.8 Translation from Tree Calculus *) 

Definition stem x :=
  Lam @
     (Lam @ (v (v (v Vop) @ Vop) @ (v (v (v Vop)) @ Vop)) @
      (Vop @
       (v Lam @ (v Lam @ (v (v Lam @ (v Lam @ (Lam @ Vop @ Lam))) @ (v Vop)))) @
       Vop)) @ (Lam @ (Lam @ (Lam @ Vop @ Lam)) @ x).

   
Lemma stem_red : forall x y z,  va_red (App (App (stem x) y) z) (App (App y z) (App x z)).
Proof.
  intros; cbv; succtac. aptac. aptac. aptac. aptac. aptac. succtac. succtac. succtac.
  zerotac.  succtac. zerotac. succtac. zerotac. zerotac. succtac.
  eapply2 preserves_app_va_red.
  aptac. aptac. aptac. aptac. zerotac. succtac. succtac. zerotac. succtac. zerotac. succtac.
  all: zerotac.
Qed. 

Lemma valuable_stem: forall x, valuable x -> valuable (stem x).
Proof.
  unfold valuable; split_all. exist (stem x0).
  cbv; repeat eapply2 preserves_app_va_red. cbv; program_tac. 
Qed.

Definition fork x y :=
  Lam
    @  (Lam
          @ (v (v (ndx 0) @ (v x)) @ (v y))
          @ Iop
       )
    @ Iop
    . 


  
Lemma fork_red: forall w x y z, va_red (App (App (fork w x) y) z) (App (App z w) x).
Proof.
  intros; unfold fork, ndx; succtac.
  eapply2 preserves_app_va_red. eapply2 preserves_app_va_red. all: cbv; succtac.
Qed.  

Lemma substitution_stem :
  forall f x N, (substitute (stem f) x N) = stem (substitute f x N).
Proof. intros; cbv; auto. Qed.


Lemma substitution_fork :
  forall f g x N, (substitute (fork f g) x N) = fork (substitute f x N) (substitute g x N).
Proof. intros; cbv; auto. Qed.


Lemma valuable_fork: forall x y, valuable x -> valuable y -> valuable (fork x y).
Proof.
  unfold valuable; split_all. exist (fork x1 x0).
  cbv; repeat eapply2 preserves_app_va_red. cbv; program_tac. 
Qed.


Lemma substitute_preserves_va_red1:
  forall M M', va_red1 M M' -> forall x N, va_red1 (substitute M x N) (substitute M' x N).
Proof.  intros M M' r; induction r; split_all. Qed.

Lemma substitute_preserves_va_red:
  forall M M', va_red M M' -> forall x N, va_red (substitute M x N) (substitute M' x N).
Proof.
  cut(forall red M M', multi_step red M M' -> red = va_red1 ->
                       forall x N, va_red  (substitute M x N) (substitute M' x N)).
  intro aux;  intros.  eapply2 aux.
  intros red M M' r; induction r; split_all; subst.
  eapply succ_red. eapply2 substitute_preserves_va_red1. eapply2 IHr.
Qed.

(* 
Compute(bracket "z" (Ref "g" @ (Ref "x") @ (Ref "y") @ (Ref "z"))). 
 *)

Definition kernel :=
  tag Kop
      (\"x"
         (tag
            (stem (Ref "x"))
            (\"y"
               (tag
                  (fork (Ref "x") (Ref "y"))
                  (Lam @ (v (v (v (v getTag) @ (v (Ref "x"))) @ (v (Ref "y"))) @ Vop) @
       (Lam @ Vop @ Lam))
      )))).



Lemma kernel_program: program kernel.
Proof. cbv; program_tac. Qed. 

(* 
Compute(term_size kernel). 
*)

Lemma kernel1_red :
  forall x,
    va_red (kernel @ x)
           (tag (stem x)
                (substitute
                   (\"y" (tag (fork (Ref "x") (Ref "y"))
                                  (Lam
                                     @ (v (v (v (v getTag) @ (v (Ref "x"))) @ (v (Ref "y")))
                                            @ Vop) @
       (Lam @ Vop @ Lam))))
                   "x" x))
 
.
Proof.
  intros x; unfold kernel; succtac. eapply transitive_red. eapply2 tag_apply.
  eapply transitive_red.  eapply2 star_beta. 
  rewrite ! tag_preserves_substitute.    rewrite substitution_stem. unfold substitute; fold substitute.
  rewrite eqb_refl.  zerotac. 
Qed.


Lemma kernel2_red :
  forall x y,  
    va_red (kernel @ x @ y)
          (tag (fork x y)
               (Lam @
     (Vop @
      (v (v (v getTag) @ (v x)) @
       (Lam @ (v Vop) @ (Lam @ Vop @ Lam) @ y @ (Lam @ Vop @ (Lam @ Vop @ Lam) @ y))) @ Vop) @
     (Lam @ Vop @ Lam))
          ).
Proof.
  intros x y.   aptac. eapply2 kernel1_red.   zerotac.
  eapply transitive_red. eapply2 tag_apply.
  unfold tag, fork, star, star_body; fold star_body. simpl.  
  succtac. eapply2 preserves_app_va_red.   succtac. eapply2 preserves_app_va_red.
  eapply2 preserves_app_va_red.   eapply2 preserves_app_va_red. succtac. 
  eapply2 preserves_app_va_red.   eapply2 preserves_app_va_red. succtac. 
  eapply2 preserves_app_va_red.   eapply2 preserves_app_va_red. succtac. 
  eapply2 preserves_app_va_red.   succtac. eapply2 preserves_app_va_red. succtac.
  eapply2 preserves_app_va_red.   succtac.
  eapply2 preserves_app_va_red.   eapply2 preserves_app_va_red.   succtac. eapply2 preserves_app_va_red.
  succtac.   eapply2 preserves_app_va_red.   succtac. eapply2 preserves_app_va_red. succtac. 
Qed.


Lemma kernel3_red:  forall x y z, va_red (kernel @ x @ y @ z) (getTag @ x @ y @ z).
Proof.
  intros x y z.  aptac. eapply2 kernel2_red. zerotac.
  eapply transitive_red. eapply2 tag_apply. succtac. eapply2 preserves_app_va_red.
  eapply2 preserves_app_va_red. succtac. 
Qed.


Lemma get_tag_kernel_red:
  forall y z, va_red (App (App (App getTag kernel) y) z) y.
Proof. intros x y; unfold kernel.  aptac. aptac.  eapply2 getTag_tag. all: zerotac. cbv; succtac. Qed. 

Lemma get_tag_stem_red:
  forall x y z, va_red (getTag @ (kernel @ x) @ y @ z) (y @ z @ (x @ z)). 
Proof.
  intros x y z; intros; aptac. aptac. aptac. zerotac. eapply2 kernel1_red.
  eapply2 getTag_tag. all: zerotac. eapply2 stem_red.   
Qed.


Lemma get_tag_fork_red:
  forall w x y z, va_red (getTag @ (kernel @ w @ x) @ y @ z) (z @ w @ x). 
Proof.
  intros w x y z. intros. aptac. aptac. aptac.  zerotac. eapply2 kernel2_red. all: zerotac.
  cbv; repeat eapply2 is_App.   aptac. aptac.   eapply2 getTag_tag. all: zerotac.   cbv; succtac.   
Qed.


(* translation *)

Definition meaningful_translation_tree_to_va (f: Tree -> VA) :=
   (forall i, f (Rewriting_partI.Ref i) = Ref i) /\              (* variables *) 
  (forall M N, f(Rewriting_partI.App M N) = App (f M) (f N)) /\  (* applications *) 
  (forall M N, t_red1 M N -> va_red (f M) (f N)) /\ (* strong version *) 
  (forall M, Rewriting_partI.program M -> valuable (f M)).

Fixpoint tree_to_va M :=
  match M with
  | Rewriting_partI.Ref i => Ref i
  | Node => kernel
  | Rewriting_partI.App M1 M2 => App (tree_to_va M1) (tree_to_va M2)
  end.

  
Lemma preserves_reduction1_tree_to_va:
  forall M N, t_red1 M N -> va_red (tree_to_va M) (tree_to_va N).
Proof.
  assert(combination getTag) by repeat eapply2 is_App. 
  intros M N r; induction r; subst; split_all.
  (* 5 *) 
  4,5: eapply2 preserves_app_va_red.
  (* 3 *)
  eapply transitive_red. eapply2 kernel3_red.  eapply2 get_tag_kernel_red. 
  (* 2 *) 
  eapply transitive_red. eapply2 kernel3_red.
  aptac. aptac. aptac.    zerotac. eapply2 kernel1_red. 
  eapply2 getTag_tag.   all: zerotac. eapply2 stem_red.   
  (* 1 *)
  eapply transitive_red. eapply2 kernel3_red.
  aptac. aptac. aptac.    zerotac. eapply2 kernel2_red. 
  eapply2 getTag_tag.   all: zerotac.  cbv; succtac. 
Qed.



Lemma preserves_reduction_tree_to_va:
  forall M N, t_red M N -> va_red (tree_to_va M) (tree_to_va N).
Proof.
  cut (forall red M N, Rewriting_partI.multi_step red M N -> red = t_red1 -> va_red (tree_to_va M) (tree_to_va N)).
  intros aux; intros; eapply2 aux. 
  intros red M N r; induction r; subst; split_all; subst.
  eapply transitive_red. eapply2 preserves_reduction1_tree_to_va. eapply2 IHr. 
Qed.

Lemma valuable_trees:
  forall p, Rewriting_partI.program p ->
            exists q, va_red (tree_to_va p) q /\ program q /\ exists t f, q = tag t f. 
Proof.
  intros p pr; induction pr; split_all. 
  (* 3 *)
  exist kernel. cbv; program_tac. repeat eexists; auto. 
  (* 2 *)
  repeat eexists. aptac. zerotac. eassumption.  eapply transitive_red. eapply2 kernel1_red.
  eapply va_red_preserves_tags. zerotac. 
  instantiate(1:= \"y"
          (tag (fork x (Ref "y"))
             (Lam @ (v (v (v (v getTag) @ (v x)) @ (v (Ref "y"))) @ Vop) @
                  (Lam @ Vop @ Lam)))). 
  unfold tag, fork, v, star, star_body; fold star_body. simpl.
  rewrite ! (occurs_combination x).  simpl.
  eapply2 preserves_app_va_red. eapply2 programs_are_combinations.
  subst; unfold tag in *; unfold v in *; inv1 program.  program_tac. 
  unfold tag, fork, v, star, star_body; fold star_body. simpl.
  rewrite ! (occurs_combination x1).  simpl.
  rewrite ! (occurs_combination x0).  simpl. program_tac. 
  cbv; program_tac.   1,2: eapply2 programs_are_combinations.
  cbv; program_tac.
  eauto.
  (* 1 *)
  subst. repeat eexists. 
  aptac. aptac. zerotac. eassumption.  zerotac. eassumption.
  eapply transitive_red. eapply2 kernel2_red.  eapply va_red_preserves_tags. zerotac.
  aptac. aptac. zerotac. aptac. aptac. zerotac. aptac. zerotac. succtac. all: zerotac.
  cbv; program_tac.
Qed.



  
Theorem meaningful_translation_from_tree_to_va:
  meaningful_translation_tree_to_va tree_to_va. 
Proof.
  split_all. 
  eapply2 preserves_reduction1_tree_to_va.
  elim(valuable_trees M); split_all.   exist x. 
Qed.

(* 
Compute (term_size kernel). = 200 
 *)


(* 9.5 Translation to Tree Calculus *)


Require Import Rewriting_partI.

Definition normalisable (M: Tree) := exists Q, t_red M Q /\ program Q.


Definition zero_rule := Eval cbv in \"a" (\"y" (\"z" (Ref "z"))).
Definition successor_rule := Eval cbv in \"x" (\"a" (\"y" (bracket "z" (Ref "y" @ Ref "x")))).
Definition application_rule :=
  Eval cbv in
    \"w" (\"x" (\"a" (\"y" (\"z" (Ref "a" @ Ref "w" @ Ref "y" @ Ref "z"
                                      @ (Ref "a" @ Ref "x" @ Ref "y" @ Ref "z")))))).
Definition empty_rule := Eval cbv in \"a" (\"y" (\"z" (Ref "a"))).
Definition substitution_rule := Eval cbv in \"x" (\"a" (\"y" (\"z" (Ref "a" @ Ref "z" @ Ref "x" @ Ref "y")))).
Definition abstraction_rule :=
  Eval cbv in
    \"w" (\"x" (\"a" (\"y" (\"z" (Ref "a" @ Ref "w" @ (Ref "a" @ Ref "x" @ Ref "y" @ Ref "z")))))).




Definition V_t :=
  Y2_t 
    zero_rule
    (\"x"
      (\"a"
        (tag
           (successor_rule @ Ref "x")
           (\"y"
             (tag
                (application_rule @ Ref "x" @ Ref "y")
                (bracket "z" (Ref "a" @ (Ref "a" @ Ref "x" @ Ref "y") @ Ref "z"))
    ))))).

Definition A_t :=
  Y2_t
    empty_rule
    (\"x"
      (\"a"
        (tag
           (substitution_rule @ Ref "x")
           (\"y"
             (tag
                (abstraction_rule @ Ref "x" @ Ref "y")
                (getTag @ Ref "x" @ Ref "a" @ Ref "y")                
    ))))).

(* 
Compute (term_size V_t).  (* 909 *) 
Compute (term_size A_t).  (* 757 *)  
*)

Lemma getTag_A0 : t_red (getTag @ A_t) empty_rule. 
Proof. apply getTag_Y2_t.  Qed.

Lemma getTag_A1 :  forall x, t_red (getTag @ (A_t @ x)) (substitution_rule @ x).
Proof.
  intros. aptac. zerotac. apply Y2_t_red. fold A_t. 
  unfold getTag, tag, d, I; starstac ("y" :: "a" :: "x" :: nil).
Qed.

Lemma getTag_A2 :  forall x y, t_red (getTag @ (A_t @ x @ y)) (abstraction_rule @ x @ y).
Proof.
  intros. aptac. zerotac. aptac. apply Y2_t_red. zerotac. fold A_t. 
  unfold getTag, tag, d, I; starstac ("y" :: "a" :: "x" :: nil).
  unfold getTag, tag, d, I; trtac. 
Qed.


Lemma getTag_V0 : t_red (getTag @ V_t) zero_rule. 
Proof. apply getTag_Y2_t.  Qed.

Lemma getTag_V1 :  forall x, t_red (getTag @ (V_t @ x)) (successor_rule @ x).
Proof.
  intros. aptac. zerotac. apply Y2_t_red. fold V_t. 
  unfold getTag, tag, d, I; starstac ("y" :: "a" :: "x" :: nil).
Qed.

Lemma getTag_V2 :  forall x y, t_red (getTag @ (V_t @ x @ y)) (application_rule @ x @ y).
Proof.
  intros. aptac. zerotac. aptac. apply Y2_t_red. zerotac. fold V_t. 
  unfold bracket. unfold eqb, Ascii.eqb, Bool.eqb.
  unfold getTag, tag, d, I; starstac ("y" :: "a" :: "x" :: nil).
  unfold getTag, tag, d, I; trtac. 
Qed.


Fixpoint va_to_tree M :=
  match M with
  | Lambda_Abstraction_in_VA_Calculus.Ref i => Ref i
  | Vop => V_t
  | Lam  => A_t
  | Lambda_Abstraction_in_VA_Calculus.App M1 M2 => (va_to_tree M1) @ (va_to_tree M2)
  end.


Lemma V_t3_red: forall x y z, t_red (V_t @ x @ y @ z) (V_t @ (V_t @ x @ y) @ z). 
Proof.
  intros. aptac. aptac. eapply2 Y2_t_red. zerotac.  fold V_t. all: zerotac. 
  unfold bracket. unfold eqb, Ascii.eqb, Bool.eqb.
  unfold tag, wait, d, I, K.   starstac ("y" :: "a" :: "x" :: nil).  
Qed.


Lemma V_t0_red :  forall f sigma,   t_red (getTag @ V_t @ f @ sigma) I.
Proof. tree_red. Qed.

Lemma AV_t0_red : forall y z,   t_red (A_t @ V_t @ y @ z) z.
Proof. 
  intros; unfold A_t. aptac. aptac. apply Y2_t_red. all: zerotac. fold A_t. 
  unfold tag; startac "x"; trtac. startac "x"; trtac. 
  starstac ("y" :: "a" :: "x" :: nil). aptac. aptac. aptac. apply getTag_Y2_t. all: zerotac.
  unfold zero_rule; trtac.
Qed.


Lemma AV_t1_red : forall x y z,   t_red (A_t @ (V_t @ x) @ y @ z) (y @ x).
Proof. 
  intros; unfold A_t. aptac. aptac. apply Y2_t_red. all: zerotac. fold A_t. 
  unfold tag; startac "x"; trtac. startac "x"; trtac. 
  starstac ("y" :: "a" :: "x" :: nil). aptac. aptac. aptac. aptac. 1, 3-8:zerotac.
  unfold V_t. apply Y2_t_red. fold V_t. 
  unfold getTag, tag, successor_rule; starstac ("x" :: "a" :: nil).
Qed.



Lemma AV_t2_red : forall w x y z, t_red (A_t @ (V_t @ w @ x) @ y @ z) (A_t @ w @ y @ z @ (A_t @ x @ y @ z)).
Proof. 
  intros; unfold A_t. aptac. aptac. apply Y2_t_red. all: zerotac. fold A_t. 
  unfold tag; startac "x"; trtac. startac "x"; trtac. 
  starstac ("y" :: "a" :: "x" :: nil). aptac. aptac. aptac. aptac. 1, 3-8:zerotac.
  unfold V_t. aptac. apply Y2_t_red. zerotac. fold V_t. zerotac. 
  unfold getTag, tag, wait, d, I, K, application_rule; starstac ("x" :: "a" :: "y" :: nil). 
Qed.

Lemma AA_t0_red : forall y z,   t_red (A_t @ A_t @ y @ z) A_t.
Proof. 
  intros; unfold A_t at 1. aptac. aptac. apply Y2_t_red. all: zerotac. fold A_t. 
  unfold tag; startac "x"; trtac. startac "x"; trtac. 
  starstac ("y" :: "a" :: "x" :: nil). aptac. aptac. aptac. apply getTag_Y2_t. all: zerotac.
  unfold empty_rule; trtac.
Qed.


Lemma AA_t1_red : forall x y z,   t_red (A_t @ (A_t @ x) @ y @ z) (A_t @ z @ x @ y).
Proof. 
  intros; unfold A_t at 1. aptac. aptac. apply Y2_t_red. all: zerotac. fold A_t. 
  unfold tag; startac "x"; trtac. startac "x"; trtac. 
  starstac ("y" :: "a" :: "x" :: nil). aptac. aptac. aptac. aptac. 1, 3-8:zerotac.
  unfold A_t. apply Y2_t_red. fold A_t. 
  unfold getTag, tag, substitution_rule; starstac ("y" :: "a" ::"x" :: nil). 
Qed.



Lemma AA_t2_red : forall w x y z, t_red (A_t @ (A_t @ w @ x) @ y @ z) (A_t @ w @ (A_t @ x @ y @ z)).
Proof. 
  intros; unfold A_t. aptac. aptac. apply Y2_t_red. all: zerotac. fold A_t. 
  unfold tag; startac "x"; trtac. startac "x"; trtac. 
  starstac ("y" :: "a" :: "x" :: nil). aptac. aptac. aptac. aptac. 1, 3-8:zerotac.
  unfold A_t. aptac. apply Y2_t_red. zerotac. fold A_t. zerotac. 
  unfold getTag, tag, abstraction_rule; starstac ("y" :: "a" :: "x" :: nil).
Qed.


Lemma A_t_program: program A_t.
Proof. program_tac. Qed. 

Lemma V_t_program: program V_t.
Proof. program_tac. Qed. 


Lemma normalisable_Vt1: forall M, normalisable M -> normalisable (V_t @ M).
Proof.
  intros M prM; inversion prM as [M1 (?&?)]; repeat eexists.
  eapply transitive_red. apply Y2_t_red. fold V_t.  unfold bracket. unfold eqb, Ascii.eqb, Bool.eqb. 
  eapply transitive_red. unfold tag, wait, d, I, K; starstac ("y" :: "a" :: "x" :: nil).
  eapply transitive_red. ap2tac; zerotac; trtac. 
  unfold successor_rule, application_rule; trtac. program_tac. 
Qed. 

Lemma normalisable_Vt2: forall M N, normalisable M -> normalisable N -> normalisable (V_t @ M @ N).
Proof.
  intros M N prM prN; inversion prM as [M1 (?&?)]; inversion prN as [N1 (?&?)]; repeat eexists.
  aptac. apply Y2_t_red. zerotac. fold V_t.  unfold bracket. unfold eqb, Ascii.eqb, Bool.eqb.
  eapply transitive_red. unfold tag, wait, d, I, K; starstac ("y" :: "a" :: "x" :: nil).
  eapply transitive_red. ap2tac; zerotac; trtac. 
  unfold application_rule; trtac. program_tac. 
Qed. 

Lemma normalisable_At1:
  forall M, normalisable M -> normalisable (getTag @ M @ A_t) -> normalisable (A_t @ M).
Proof.
  intros M prM prT; inversion prM as [M1 (?&?)].
  inversion prT.   inversion H1.
  repeat eexists.
  eapply transitive_red. apply Y2_t_red. fold A_t.  
  eapply transitive_red. unfold tag, wait, d, I, K; starstac ("y" :: "a" :: "x" :: nil).
 eapply transitive_red. ap2tac; zerotac.
  unfold substitution_rule, abstraction_rule; trtac. program_tac. 
Qed. 

Lemma normalisable_At2:
  forall M N, normalisable M -> normalisable N -> normalisable (getTag @ M @ A_t @N) ->
              normalisable (A_t @ M @ N).
Proof.
  intros M N prM prN prT; inversion prM as [M1 (?&?)]. inversion prN as [N1 (?&?)].
  inversion prT as [AMN (?&?)]. 
  repeat eexists.
  aptac. apply Y2_t_red. zerotac. fold A_t.  
  eapply transitive_red. unfold tag, wait, d, I, K; starstac ("y" :: "a" :: "x" :: nil).
 eapply transitive_red. ap2tac; zerotac.
  unfold abstraction_rule; trtac. program_tac. 
Qed. 

Require Import Rewriting_theorems.

Lemma preserves_programs_va_to_tree: 
  forall M, Lambda_Abstraction_in_VA_Calculus.program M ->
            normalisable (va_to_tree M)   /\
            normalisable (getTag @ (va_to_tree M) @ A_t) /\
            forall x, normalisable x ->
                        normalisable (getTag @ (va_to_tree M) @ A_t @ x)                           
.
Proof.
  intros M pr; induction pr;  simpl.
  (* 6 *)   
  split.
  exists V_t; split; [zerotac |program_tac].
  split.
  repeat eexists. aptac. apply getTag_V0. zerotac. unfold zero_rule; trtac.  program_tac. 
  repeat eexists. aptac. aptac. apply getTag_V0. zerotac. unfold zero_rule; trtac.  zerotac. trtac.
  program_tac.
  (* 5 *)
  split.
  apply normalisable_Vt1; auto. tauto. 
  split.
  inversion IHpr. inversion H. inversion H1. 
  repeat eexists.  aptac. apply getTag_V1. zerotac.
  eapply transitive_red. ap2tac; zerotac.   unfold successor_rule; trtac. program_tac.
  intros.
  inversion IHpr. inversion H0. inversion H2.  inversion H. inversion H5. 
  repeat eexists.  aptac. aptac. apply getTag_V1. zerotac.
  eapply transitive_red. ap2tac; zerotac.   unfold successor_rule; trtac. apply H6. trtac. program_tac.
  (* 4 *)
  split.
  apply normalisable_Vt2; auto; tauto. 
  split.
  inversion IHpr1. inversion H. inversion H1. 
  inversion IHpr2. inversion H4. inversion H6. 

  assert(normalisable (A_t @ x)). apply normalisable_At1. 
  exists x; split; auto. zerotac. 
  inversion H0. inversion H9. inversion H11. 
  elim(confluence_tree_calculus _ _ H12 (getTag @ x @ A_t)); intros; auto. 
  inversion H14.
  assert(x2 = x1). apply programs_are_stable2; auto.  apply t_red_to_s_red; auto. subst.
  exists x1; split; auto. ap2tac; zerotac.

  assert(normalisable (A_t @ x0)). apply normalisable_At1. 
  exists x0; split; auto. zerotac. 
  inversion H5. inversion H10. inversion H12. 
  elim(confluence_tree_calculus _ _ H13 (getTag @ x0 @ A_t)); intros; auto. 
  inversion H15.
  assert(x2 = x1). apply programs_are_stable2; auto.  apply t_red_to_s_red; auto. subst.
  exists x1; split; auto. ap2tac; zerotac.

   inversion H9; inversion H10. inversion H11; inversion H12. 

  repeat eexists.  aptac. apply getTag_V2. zerotac.
  eapply transitive_red. ap2tac; zerotac.
  eapply transitive_red. unfold application_rule; trtac.
  ap2tac; zerotac.
  program_tac.

  intros.
  
  inversion IHpr1. inversion H0. inversion H2.  inversion H. inversion H5. inversion H1.
  inversion IHpr2. inversion H10. inversion H11. inversion H12.  (* inversion H11. inversion H15.  *) 

 assert(normalisable (A_t @ x2 @ x1)). apply normalisable_At2. 
  exists x2; split; auto. zerotac. 
  exists x1; split; auto. zerotac. 
  elim (H14 x1); intros; auto.   2:   exists x1; split; auto; zerotac. 
  inversion H17. 
  elim(confluence_tree_calculus _ _ H18 (getTag @ x2 @ A_t @ x1)); intros; auto. 
  2: ap2tac; zerotac.   inversion H20.
  assert(x4 = x3). apply programs_are_stable2; auto.  apply t_red_to_s_red; auto. subst.
  exists x3; split; auto. ap2tac; zerotac.

 assert(normalisable (A_t @ x0 @ x1)). apply normalisable_At2. 
  exists x0; split; auto. zerotac. 
  exists x1; split; auto. zerotac. 
  elim (H9 x1); intros; auto.   2:   exists x1; split; auto; zerotac. 
  inversion H18. 
  elim(confluence_tree_calculus _ _ H19 (getTag @ x0 @ A_t @ x1)); intros; auto. 
  2: ap2tac; zerotac.   inversion H21.
  assert(x4 = x3). apply programs_are_stable2; auto.  apply t_red_to_s_red; auto. subst.
  exists x3; split; auto.

  inversion H17; inversion H18. inversion H19; inversion H20. 
  
  repeat eexists.  aptac. aptac. apply getTag_V2. zerotac.
  eapply transitive_red. ap2tac; zerotac.   unfold application_rule; trtac. apply H6.
  eapply transitive_red. trtac. ap2tac; zerotac. program_tac.

  (* 3 *)
  split.
  exists A_t; split; [zerotac |program_tac].
  split.
  repeat eexists. aptac. apply getTag_A0. zerotac. unfold empty_rule; trtac.  program_tac. 
  repeat eexists. aptac. aptac. apply getTag_A0. zerotac. unfold empty_rule; trtac.  zerotac. trtac.
  program_tac.
  (* 2 *)
  split.
  apply normalisable_At1; auto; tauto. 
  split.
  inversion IHpr. inversion H. inversion H1. 
  repeat eexists.  aptac. apply getTag_A1. zerotac.
  eapply transitive_red. ap2tac; zerotac.   unfold substitution_rule; trtac. program_tac.
  intros.
  inversion IHpr. inversion H0. inversion H2.  inversion H. inversion H5. 
  repeat eexists.  aptac. aptac. apply getTag_A1. zerotac.
  eapply transitive_red. ap2tac; zerotac.   unfold substitution_rule; trtac. apply H6. trtac. program_tac.
  (* 1 *)
  split.
  apply normalisable_At2; auto. tauto.  tauto. apply IHpr1. tauto. 
  split.
  inversion IHpr1. inversion H. inversion H1. 
  inversion IHpr2. inversion H4. inversion H6. 

  assert(normalisable (A_t @ x)). apply normalisable_At1. 
  exists x; split; auto. zerotac. 
  inversion H0. inversion H9. inversion H11. 
  elim(confluence_tree_calculus _ _ H12 (getTag @ x @ A_t)); intros; auto. 
  inversion H14.
  assert(x2 = x1). apply programs_are_stable2; auto.  apply t_red_to_s_red; auto. subst.
  exists x1; split; auto. ap2tac; zerotac.

  assert(normalisable (A_t @ x0)). apply normalisable_At1. 
  exists x0; split; auto. zerotac. 
  inversion H5. inversion H10. inversion H12. 
  elim(confluence_tree_calculus _ _ H13 (getTag @ x0 @ A_t)); intros; auto. 
  inversion H15.
  assert(x2 = x1). apply programs_are_stable2; auto.  apply t_red_to_s_red; auto. subst.
  exists x1; split; auto. ap2tac; zerotac.

   inversion H9; inversion H10. inversion H11; inversion H12. 

  repeat eexists.  aptac. apply getTag_A2. zerotac.
  eapply transitive_red. ap2tac; zerotac.
  eapply transitive_red. unfold abstraction_rule; trtac.
  ap2tac; zerotac.
  program_tac.

  intros.
  
  inversion IHpr1. inversion H0. inversion H2.  inversion H. inversion H5. inversion H1.
  inversion IHpr2. inversion H10. inversion H11. inversion H12.  (* inversion H11. inversion H15.  *) 

 assert(normalisable (A_t @ x2 @ x1)). apply normalisable_At2. 
  exists x2; split; auto. zerotac. 
  exists x1; split; auto. zerotac. 
  elim (H14 x1); intros; auto.   2:   exists x1; split; auto; zerotac. 
  inversion H17. 
  elim(confluence_tree_calculus _ _ H18 (getTag @ x2 @ A_t @ x1)); intros; auto. 
  2: ap2tac; zerotac.   inversion H20.
  assert(x4 = x3). apply programs_are_stable2; auto.  apply t_red_to_s_red; auto. subst.
  exists x3; split; auto. ap2tac; zerotac.

  assert(normalisable (A_t @ x0)). apply normalisable_At1. 
  exists x0; split; auto. zerotac. 
  inversion H8.   inversion H18.
  elim(confluence_tree_calculus _ _ H19 (getTag @ x0 @ A_t)); intros; auto. 
  2: ap2tac; zerotac.   inversion H21.
  assert(x4 = x3). apply programs_are_stable2; auto.  apply t_red_to_s_red; auto. subst.
  exists x3; split; auto.

  inversion H17; inversion H18. inversion H19; inversion H20. 
  
  repeat eexists.  aptac. aptac. apply getTag_A2. zerotac.
  eapply transitive_red. ap2tac; zerotac.   unfold abstraction_rule; trtac. apply H6.
  eapply transitive_red. trtac. ap2tac; zerotac. program_tac.
Qed.

Lemma preserves_combination_ac_to_tree:
  forall M, Lambda_Abstraction_in_VA_Calculus.combination M -> combination (va_to_tree M).
Proof.  intros M c; induction c; zerotac; cbv; auto 1000 with *. Qed.


Lemma preserves_reduction1_va_to_tree:
  forall M N, va_red1 M N -> t_red (va_to_tree M) (va_to_tree N).
Proof.
  intros M N r; induction r; subst; split_all;
    try (eapply2 preserves_app_t_red; zerotac; fail).
  (* 7 *)
  eapply2 V_t3_red. 
  eapply2 AV_t0_red.
  eapply2 AV_t1_red.
  eapply2 AV_t2_red.
  eapply2 AA_t0_red.
  eapply2 AA_t1_red.
  eapply2 AA_t2_red.
Qed.

  
Definition meaningful_translation_ac_to_tree (f: VA -> Tree) :=
  (forall M N, va_red1 M N -> t_red (f M) (f N)) /\ (* strong version *) 
  (forall M N, f(Lambda_Abstraction_in_VA_Calculus.App M N) = (f M) @ (f N)) /\  (* applications *) 
  (forall i, f (Lambda_Abstraction_in_VA_Calculus.Ref i) = Ref i) /\              (* variables *) 
  (forall M, Lambda_Abstraction_in_VA_Calculus.program M -> normalisable (f M)).


  
Theorem meaningful_translation_from_ac_to_tree:
  meaningful_translation_ac_to_tree va_to_tree. 
Proof.
  split_all. 
  eapply2 preserves_reduction1_va_to_tree.
  eapply2 preserves_programs_va_to_tree. 
Qed.

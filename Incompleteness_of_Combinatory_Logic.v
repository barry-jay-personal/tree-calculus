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
(*         Chapter 8: Incompleteness of Combinatory Logic             *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)



Require Import Arith Lia Bool List String.
Require Import Reflective.Rewriting_partI.

Set Default Proof Using "Type".

Ltac invsub := 
match goal with 
| H : _ = _ |- _ => injection H; clear H; invsub 
| _ => intros; subst
end. 


(* 8.2: SK-Calculus *) 


Inductive SK:  Set :=
  | Ref : string -> SK  (* variables are indexed by strings *) 
  | Sop : SK   
  | Kop : SK 
  | App : SK -> SK -> SK   
.

Hint Constructors SK : TreeHintDb.

Open Scope string_scope. 
Declare Scope sk_scope.
Open Scope sk_scope. 

Notation "x @ y" := (App x y) (at level 65, left associativity) : sk_scope.



Definition Iop := Sop @ Kop @ Kop. 


Inductive combination : SK -> Prop :=
| is_S : combination Sop
| is_K : combination Kop 
| is_App : forall M N, combination M -> combination N -> combination (M@ N)
.
Hint Constructors combination : TreeHintDb. 

(* SK-reduction *) 
Inductive sk_red1 : SK -> SK -> Prop :=
| s__red: forall (M N P : SK), sk_red1 (Sop @M@ N@ P) (M@P@(N@P))
| k_red : forall M N, sk_red1 (Kop @ M@ N) M 
| appl_red : forall M M' N, sk_red1 M M' -> sk_red1 (M@ N) (M' @ N)  
| appr_red : forall M N N', sk_red1 N N' -> sk_red1 (M@ N) (M@ N')  
.
Hint Constructors sk_red1 : TreeHintDb. 

(* Multiple reduction steps *) 

Inductive multi_step : (SK -> SK -> Prop) -> SK -> SK -> Prop :=
  | zero_red : forall red M, multi_step red M M
  | succ_red : forall (red: SK-> SK -> Prop) M N P, 
                   red M N -> multi_step red N P -> multi_step red M P
.
Hint Constructors multi_step : TreeHintDb.


Definition transitive red := forall (M N P: SK), red M N -> red N P -> red M P. 

Lemma transitive_red : forall red, transitive (multi_step red). 
Proof. red; induction 1; intros; simpl;  auto. apply succ_red with N; auto. Qed. 

Definition preserves_appl (red : SK -> SK -> Prop) := 
forall M N M', red M M' -> red (M@ N) (M' @ N).

Definition preserves_appr (red : SK -> SK -> Prop) := 
forall M N N', red N N' -> red (M@ N) (M@ N').

Definition preserves_app (red : SK -> SK -> Prop) := 
forall M M', red M M' -> forall N N', red N N' -> red (M@ N) (M' @ N').

Lemma preserves_appl_multi_step : 
forall (red: SK -> SK -> Prop), preserves_appl red -> preserves_appl (multi_step red). 
Proof. red; intros red hy M N M' r; induction r; auto with TreeHintDb; eapply succ_red; eauto. Qed.

Lemma preserves_appr_multi_step : 
forall (red: SK -> SK -> Prop), preserves_appr red -> preserves_appr (multi_step red). 
Proof. red; intros red hy M N M' r; induction r; auto with TreeHintDb; eapply succ_red; eauto. Qed.


Lemma preserves_app_multi_step : 
forall (red: SK -> SK -> Prop), 
preserves_appl red -> preserves_appr red -> 
preserves_app (multi_step red). 
Proof.
red; intros red pl pr M M' rM N N' rN;  
  apply transitive_red with (M' @ N); [ apply preserves_appl_multi_step | apply preserves_appr_multi_step] ;
    auto.
Qed.



(* sk_red *) 

Definition sk_red := multi_step sk_red1.

Lemma sk_red_refl: forall M, sk_red M M. Proof. intros; apply zero_red. Qed.
Hint Resolve sk_red_refl : TreeHintDb. 

Lemma preserves_appl_sk_red : preserves_appl sk_red.
Proof. apply preserves_appl_multi_step. red; auto_t. Qed.

Lemma preserves_appr_sk_red : preserves_appr sk_red.
Proof. apply preserves_appr_multi_step. red; auto_t. Qed.

Lemma preserves_app_sk_red : preserves_app sk_red.
Proof. apply preserves_app_multi_step;  red; auto_t. Qed.



Ltac eval_tac1 := 
match goal with 
| |-  sk_red ?M _ => red; eval_tac1
(* 4 apps *) 
| |- multi_step sk_red1 (_ @ _ @ _ @ _ @ _) _ => 
  eapply transitive_red;  [eapply preserves_app_sk_red; [eval_tac1|auto_t] |auto_t]
(* 3 apps *) 
| |- multi_step sk_red1 (Sop @ _ @ _ @ _) _  => eapply succ_red; auto_t 
| |- multi_step sk_red1 (Kop @ _ @ _ @ _) _ =>
    eapply transitive_red;  [eapply preserves_app_sk_red; [eval_tac1|auto_t] |]; auto_t
| |- multi_step sk_red1 (_ @ _ @ _ @  _) (_ @ _)  =>  eapply preserves_app_sk_red; eval_tac1
(* 2 apps *) 
| |- multi_step sk_red1 (Sop @ _ @ _) (Sop  @ _ @ _) _ =>
  apply preserves_app_sk_red; [ apply preserves_app_sk_red |]; eval_tac1
| |- multi_step sk_red1 (Kop @ _ @ _ )  _  => eapply succ_red; auto_t 
| |- multi_step sk_red1 (_ @ _ @ _) (_ @ _)  => eapply preserves_app_sk_red; eval_tac1
| |- multi_step sk_red1 (_ @ _) (_ @ _) => apply preserves_app_sk_red; eval_tac1
| _ => auto_t
end.

Ltac eval_tac := intros; cbv; repeat eval_tac1. 


Ltac zerotac := try apply zero_red.
Ltac succtac :=
  repeat (eapply transitive_red;
  [ eapply succ_red; auto_t ;
    match goal with | |- multi_step sk_red1 _ _ => idtac | _ => fail end
  | ])
.
Ltac aptac := eapply transitive_red; [ eapply preserves_app_sk_red |].
                                             
Ltac ap2tac:=
  unfold sk_red; 
  eassumption || 
              match goal with
              | |- multi_step _ (_ @ _) _ => try aptac; [ap2tac | ap2tac | ]
              | _ => idtac
              end. 

Ltac trtac := unfold Iop; succtac;  zerotac. 

Lemma i_red: forall M, sk_red (Iop @ M) M.
Proof. eval_tac. Qed. 

Lemma i_alt_red: forall y M, sk_red (Sop @Kop@ y@ M) M. 
Proof. eval_tac. Qed. 




Ltac inv1 prop := 
match goal with 
| H: prop (_ @ _) |- _ => inversion H; clear H; inv1 prop
| H: prop Sop |- _ => inversion H; clear H; inv1 prop
| H: prop Kop |- _ => inversion H; clear H; inv1 prop
| H: prop (Ref _) |- _ => inversion H; clear H; inv1 prop
| _ =>  subst; intros; auto_t
 end.



Ltac inv red := 
match goal with 
| H: multi_step red (_ @ _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red Sop _ |- _ => inversion H; clear H; inv red
| H: multi_step red Kop _ |- _ => inversion H; clear H; inv red
| H: red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: red (_ @ _) _ |- _ => inversion H; clear H; inv red
| H: red Sop _ |- _ => inversion H; clear H; inv red
| H: red Kop _ |- _ => inversion H; clear H; inv red
| H: multi_step red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ (_ @ _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ Sop |- _ => inversion H; clear H; inv red
| H: multi_step red _ Kop |- _ => inversion H; clear H; inv red
| H: red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: red _ (_ @ _) |- _ => inversion H; clear H; inv red
| H: red _ Sop |- _ => inversion H; clear H; inv red
| H: red _ Kop |- _ => inversion H; clear H; inv red
| _ => subst; intros; auto_t
 end.




Definition implies_red (red1 red2: SK-> SK-> Prop) := forall M N, red1 M N -> red2 M N. 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (multi_step red1) (multi_step red2).
Proof. red. 
intros red1 red2 IR M N R; induction R; intros; auto with TreeHintDb. 
apply transitive_red with N; auto. 
Qed. 


Lemma to_sk_red_multi_step: forall red, implies_red red sk_red -> implies_red (multi_step red) sk_red. 
Proof. 
red.  intros red B M N R; induction R; intros.
red; intros; auto with TreeHintDb. 
assert(sk_red M N) by (apply B; auto). 
apply transitive_red with N; auto. 
apply IHR; auto with TreeHintDb. 
Qed.


Inductive s_red1 : SK -> SK -> Prop :=
  | ref_s_red : forall i, s_red1 (Ref i) (Ref i)
  | sop_s_red :  s_red1 Sop Sop
  | kop_s_red :  s_red1 Kop Kop
  | app_s_red :
      forall M M' ,
      s_red1 M M' ->
      forall N N' : SK, s_red1 N N' -> s_red1 (M@ N) (M' @ N')  
  | s_s_red: forall (M M' N N' P P' : SK),
             s_red1 M M' -> s_red1 N N' -> s_red1 P P' ->                  
             s_red1  (Sop @M @ N @ P) (M' @ P' @ (N' @ P'))
  | k_s_red : forall M  M' N,  s_red1 M M' -> s_red1 (Kop @ M @ N) M' 
.

Hint Constructors s_red1 : TreeHintDb.

Lemma s_red_refl: forall M, s_red1 M M.
Proof. induction M; intros; auto with TreeHintDb. Qed. 

Hint Resolve s_red_refl : TreeHintDb. 
     
Definition s_red := multi_step s_red1.

Lemma preserves_appl_s_red : preserves_appl s_red.
Proof. apply preserves_appl_multi_step. red; auto_t. Qed.

Lemma preserves_appr_s_red : preserves_appr s_red.
Proof. apply preserves_appr_multi_step. red; auto_t. Qed.

Lemma preserves_app_s_red : preserves_app s_red.
Proof. apply preserves_app_multi_step;  red; auto_t. Qed.


Lemma sk_red1_to_s_red1 : implies_red sk_red1 s_red1.
Proof. red; intros M N B; induction B; intros; auto with TreeHintDb. Qed. 


Lemma sk_red_to_s_red: implies_red sk_red s_red.
Proof.
  apply implies_red_multi_step.
  red; intros.  eapply succ_red. eapply sk_red1_to_s_red1; auto_t. apply zero_red.
Qed. 


Lemma s_red1_to_sk_red: implies_red s_red1 sk_red .
Proof.
  red; intros M N OR; induction OR; auto_t.
  2,3: eapply succ_red; auto_t.
  all: ap2tac; zerotac. 
Qed.

Hint Resolve s_red1_to_sk_red: TreeHintDb.

Lemma s_red_to_sk_red: implies_red s_red sk_red. 
Proof. apply to_sk_red_multi_step; auto with TreeHintDb. Qed.





(* Diamond Lemmas *) 


Definition diamond (red1 red2 : SK -> SK -> Prop) := 
forall M N, red1 M N -> forall P, red2 M P -> exists Q, red2 N Q /\ red1 P Q. 

Lemma diamond_flip: forall red1 red2, diamond red1 red2 -> diamond red2 red1. 
Proof.
  unfold diamond; intros red1 red2 d1 M N r1 P r2; elim (d1 M P r2 N r1); intros x (?&?);
    exists x; tauto.
Qed.

Lemma diamond_strip : 
forall red1 red2, diamond red1 red2 -> diamond red1 (multi_step red2). 
Proof.
  intros red1 red2 d; eapply diamond_flip; intros M N r; induction r;
    [intro P; exist P |
     intros P0 r0;
     elim (d M P0 r0 N); auto_t; intros x (?&?);  
     elim(IHr d x); auto; intros x0 (?&?); exist x0;  eapply2 succ_red
    ]. 
Qed. 


Definition diamond_star (red1 red2: SK -> SK -> Prop) := forall  M N, red1 M N -> forall P, red2 M P -> 
  exists Q, red1 P Q /\ multi_step red2 N Q. 

Lemma diamond_star_strip: forall red1 red2, diamond_star red1 red2 -> diamond (multi_step red2) red1 .
Proof. 
  intros red1 red2 d M N r; induction r; intros P0 r0;
  [ exist P0 | 
  elim(d M _ r0 N); auto; intros x (r1&r2);   
  elim(IHr d x); auto; intros x0 (?&?); 
  exist x0; eapply2 transitive_red
    ]. 
Qed. 

Lemma diamond_tiling : 
forall red1 red2, diamond red1 red2 -> diamond (multi_step red1) (multi_step red2).
Proof. 
  intros red1 red2 d M N r; induction r as [| ? ? ? ? r1 r2]; 
    [  intro P; exist P |
       intros P0 r0; 
       elim(diamond_strip red red2 d M N r1 P0); auto;
       intros N3 (r3&?); 
       elim(IHr2 d N3 r3); intros P1 (?&?);  
       exist P1;  eapply2 succ_red
  ].  
Qed. 

Hint Resolve diamond_tiling: TreeHIntDb. 



Lemma diamond_s_red1 : diamond s_red1 s_red1. 
Proof.  
red. intros M N r; induction r; intros P0 rP; auto_t.
(* 3 *)
inversion rP; clear rP; subst; inv s_red1; inv s_red1; auto_t. 
(* 5 *)
elim(IHr1 M'0); auto; intros x (?&?);
  elim(IHr2 N'0); auto; intros x0 (?&?); exists (x@ x0); split; auto_t.
(* 4 *)
elim(IHr1 (Sop @ M'0 @ N'0)); auto_t; intros x (?&?); inv s_red1; invsub. 
elim(IHr2 P'); auto_t; intros x (?&?).
exist (N'4 @ x @ (N'3 @ x)).
(* 3 *)
elim(IHr1 (Kop@ P0)); auto_t; intros x (?&?); inv s_red1; invsub; auto_t. 
(* 2 *)
inversion rP; clear rP; subst; inv s_red1; invsub. 
elim(IHr1 N'2); elim(IHr2 N'1); elim(IHr3 N'0); auto_t; intros x (?&?) x0 (?&?) x1 (?&?).
exist (x1 @ x @ (x0 @ x)).
elim(IHr1 M'0); elim(IHr2 N'0); elim(IHr3 P'0);  auto_t; intros x (?&?) x0 (?&?) x1 (?&?).
exist (x1 @ x @ (x0 @ x)).
(* 1 *) 
inversion rP; clear rP; subst; inv s_red1; invsub; auto_t.
elim(IHr N'0); auto; intros x (?&?); exist x. 
Qed.



Hint Resolve diamond_s_red1: TreeHintDb.

Lemma diamond_s_red1_s_red : diamond s_red1 s_red.
Proof. eapply diamond_strip; auto_t. Qed. 

Lemma diamond_s_red : diamond s_red s_red.
Proof.  apply diamond_tiling; auto_t. Qed. 
Hint Resolve diamond_s_red: TreeHIntDb.


(* Confluence *)

Definition confluence (A : Set) (R : A -> A -> Prop) :=
  forall x y : A,
  R x y -> forall z : A, R x z -> exists u : A, R y u /\ R z u.

Theorem confluence_s_red: confluence SK s_red. 
Proof. red; intros; eapply diamond_s_red; auto_t. Qed. 


 

Theorem confluence_sk_red: confluence SK sk_red. 
Proof. 
  red; intros.
  match goal with H: sk_red ?x ?y , H1 : sk_red ?x ?z |- _ => 
                  assert(py: s_red x y) by  (apply sk_red_to_s_red; auto_t);
                    assert(pz: s_red x z) by (apply sk_red_to_s_red; auto_t);
                    elim(diamond_s_red x y py z); auto_t end.
  intros x0 (?&?); exists x0; split; auto_t; apply s_red_to_sk_red; auto_t. 
Qed. 
Hint Resolve confluence_sk_red: TreeHintDb.

(* programs *)

Inductive program : SK -> Prop :=
| pr_S0 : program Sop
| pr_S1 : forall M, program M -> program (Sop @ M)
| pr_S2 : forall M1 M2, program M1 -> program M2 -> program (Sop @ M1 @ M2)
| pr_K0 : program Kop
| pr_K1 : forall M, program M -> program (Kop @ M) .

Hint Constructors program: TreeHintDb.


Ltac program_tac :=
  cbv; repeat (apply pr_S0 || apply pr_S1 || apply pr_S2 || apply pr_K0 || apply pr_K1); auto_t. 


(* normal forms *) 

Inductive active : SK -> Prop := 
| active_ref : forall i, active (Ref i)
| active_app : forall M N, active M -> active (M@ N)
.


Inductive normal : SK -> Prop := 
| nf_ref : forall i, normal (Ref i)
| nf_S : normal Sop
| nf_K : normal Kop                
| nf_app : forall M N, active M -> normal M -> normal N -> normal (M@ N)
| nf_S1 : forall M, normal M -> normal (Sop @ M)
| nf_K1 : forall M, normal M -> normal (Kop @ M)
| nf_S2 : forall M N, normal M -> normal N -> normal (Sop @ M @ N)
.


Hint Constructors active normal : TreeHintDb.


Lemma active_sk_red1 :
  forall M, active M -> forall N, sk_red1 M N  -> active N.
Proof.  intros M a; induction a; intros; inv sk_red1; inv1 active. Qed.   

  
                    Lemma active_sk_red2:
  forall M N P, active M -> sk_red1 (M@ N) P ->
                (exists M1, P = M1 @ N /\ sk_red1 M M1)
                \/ (exists N1, P = M@ N1 /\ sk_red1 N N1).
Proof. induction M; intros; inv sk_red1; auto_t; inv1 active. Qed. 
                      

Lemma active_sk_red:
  forall M N P, active M -> sk_red (M@ N) P ->
                (exists M1 N1, P = M1 @ N1 /\ sk_red M M1 /\ sk_red N N1).
Proof.
  cut(forall red M P, multi_step red M P -> red = sk_red1 -> 
forall M1 M2, M = M1 @ M2 -> active M1 -> 
                (exists P1 P2, P = P1 @ P2 /\ sk_red M1 P1 /\ sk_red M2 P2));
    [ intro c;  intros; eapply2 c
    |
    intros red M P r; induction r; intros; subst; auto_t; inv sk_red1 ;
    [ inv1 active
    | inv1 active 
    | eelim IHr; [ | auto | auto_t| eapply active_sk_red1; auto_t];
      intros x ex; elim ex; intros P2 (?&?&?); subst;
      repeat eexists; auto_t; eapply succ_red; auto_t
    |  eelim IHr;  [ | auto | auto_t |]; auto;  intros x ex; elim ex; intros x0 (?&?&?); subst;
       exists x; exist x0 ; eapply2 succ_red
    ]]. 
Qed.



Lemma normal_is_irreducible: forall M, normal M -> forall N, sk_red1 M N -> False.
Proof.
  intros M n; induction n; intros; inv sk_red1;
    ((apply IHn1; fail) || (apply IHn2; fail) || (apply IHn; fail) || inv1 active).  
Qed.


Lemma active_is_stable:
  forall M N P, active M -> s_red1 (M@ N) P ->
                (exists M1 N1, P = M1 @ N1 /\ s_red1 M M1 /\ s_red1 N N1).
Proof.
  induction M; intros N P a r; inv s_red1; auto_t; inversion a; subst; eauto 10 with *; inv1 active.
Qed.   


Lemma normal_is_stable: forall M, normal M -> forall N, s_red1 M N -> N = M.
Proof. intros M n; induction n; intros; inv s_red1; repeat f_equal; auto; inv1 active. Qed.


Lemma normal_is_stable2: forall M N, s_red M N -> normal M -> N = M.
Proof.
  cut(forall red M N, multi_step red M N -> red = s_red1 -> normal M -> N = M); 
  [ intro c; intros; eapply2 c  
  | intros red M N r; induction r; intros; subst; auto_t; 
    assert(N = M) by (eapply normal_is_stable; eauto); subst; auto
  ].
  Qed.


Lemma triangle_s_red : forall M N P, s_red M N -> s_red M P -> normal P -> s_red N P.
Proof.
  intros; assert(d: exists Q, s_red N Q /\ s_red P Q) by (eapply diamond_s_red; auto_t);
  elim d; intros x (?&?); 
  assert(x = P) by (eapply normal_is_stable2; eauto);  subst; auto. 
Qed.


Lemma programs_are_normal: forall M, program M -> normal M.
Proof.  intros M pr; induction pr; intros; auto_t. Qed. 


Definition normalisable M := exists N,  sk_red M N /\ program N.


Ltac normal_tac :=
  cbv;
  repeat (apply nf_S2 || apply nf_K1 || apply nf_S1 || apply nf_app ||
          apply nf_K || apply nf_S || apply nf_ref);
  apply programs_are_normal; 
  auto_t. 

Ltac stable_tac :=
  match goal with
  | H : s_red ?Q ?R |- _ =>
    assert(R=Q) by (apply normal_is_stable2; auto_t; cbv; normal_tac); clear H 
  | H : s_red1 ?Q ?R |- _ =>
    assert(R=Q) by (apply normal_is_stable; auto_t; cbv; normal_tac); clear H
  | H : sk_red ?Q ?R |- _ => assert(s_red Q R) by (apply sk_red_to_s_red; auto_t); clear H; stable_tac 
  | _ => auto_t
  end; subst; try discriminate.

(* 8.3 Combinators in SK-Calculus *) 


Fixpoint bracket x M := 
match M with 
| Ref y =>  if eqb x y then Iop else (Kop @ (Ref y))
| Sop => Kop @ Sop
| Kop => Kop @ Kop 
| M1 @ M2 => Sop @ (bracket x M1) @ (bracket x M2) 
end
.


(* star abstraction *)


Fixpoint occurs x M :=
  match M with
  | Ref y => eqb x y
  | Sop => false
  | Kop => false 
  | M1 @ M2 => (occurs x M1) || (occurs x M2)
  end.


Fixpoint star x M :=
  match M with
  | Ref y => if eqb x y then Iop else Kop @ (Ref y)
  | Sop  => Kop @ Sop
  | Kop => Kop @ Kop 
  | M1 @ (Ref y) =>
    if eqb x y
    then if negb (occurs x M1)
         then M1
         else Sop @ (star x M1) @ Iop
    else if negb (occurs x M1)
         then Kop @ (M1 @ (Ref y))
         else Sop @ (star x M1) @ (Kop @ (Ref y))
  | M1 @ M2 => if occurs x (M1 @ M2)
                 then Sop @ (star x M1) @ (star x M2) 
                 else Kop @ (M1 @ M2)
  end.



Lemma star_id: forall x, star x (Ref x) = Iop.
Proof. intro; unfold star, occurs; rewrite eqb_refl; auto. Qed.


Lemma eta_red: forall M x, occurs x M = false -> star x (M@ (Ref x)) = M.
Proof.  intros M x occ; unfold star at 1; fold star; rewrite eqb_refl; rewrite occ; auto. Qed.


Lemma star_occurs_false: forall M x, occurs x M = false -> star x M = Kop @ M. 
Proof.
  induction M; simpl in *; auto_t; intros x occ;  rewrite occ; auto.
  rewrite orb_false_iff in occ;  elim occ.   intros occ1 occ2; rewrite ! occ1.  
  caseEq M2; simpl; intros; subst; simpl in *; intros; auto_t.
  rewrite occ2; auto.   
Qed.


Lemma star_occurs_true:
  forall M1 M2 x, occurs x (M1 @ M2) = true -> M2 <> Ref x ->
                  star x (M1 @ M2) = Sop @ (star x M1) @ (star x M2).
Proof.
  intros M1 M2 x occ ne; unfold star at 1; fold star. 
  caseEq M2; 
    [ intros s e; subst;  assert(neq: x=? s = false) by (apply eqb_neq; congruence); 
      simpl in *; rewrite neq in *; rewrite orb_false_r in *; rewrite occ; auto
    | | |]; intros; subst; rewrite ? occ; auto. 
                 
Qed.

Ltac star_tac x :=
  repeat ( (rewrite (star_occurs_true _ _ x); [| unfold occurs; fold occurs; rewrite ? orb_true_r; simpl; auto; fail| cbv; discriminate]) || 
          (rewrite eta_red; [| cbv; auto; fail]) ||
          rewrite star_id || 
          (rewrite (star_occurs_false _ x); [| unfold occurs; fold occurs; auto; cbv; auto; fail])
         ).


Notation "\" := star : sk_scope.


(* reprise of Extensional_Programs *) 

(* Fixpoints *) 

Definition omega := Sop @ (Kop @ (Sop @ Iop)) @ (Sop @ Iop @ Iop).
(*
  \(\(App (Ref 0) (App (App (Ref 1) (Ref 1)) (Ref 0)))).
*) 
Definition Yop := App omega omega. 

Lemma y_red: forall f, sk_red (Yop @ f) (f @ (Yop @ f)).
Proof.
  (* delicate proof since rhs is not normal *)
  intros; unfold Yop at 1; unfold omega at 1.
  aptac. eapply2 succ_red. zerotac.
  aptac;
    [ aptac;
      [ eapply2 succ_red
      | instantiate(1:= Yop); eapply2 succ_red; aptac; eval_tac
      | zerotac]
    | zerotac
    |  eapply2 succ_red; aptac; [  eval_tac | zerotac | aptac; [ succtac | |]; zerotac]
    ]. 
Qed. 
  

(* Waiting *) 

Definition wait M N := Sop @ (Sop @ (Kop @ M) @ (Kop @ N)) @ Iop.
Definition Wop := \"x" (\"y" (wait (Ref "x") (Ref "y"))). 

Lemma wait_red: forall M N P, sk_red (wait M N @ P) (M@ N @ P).
Proof.  intros; cbv; repeat (eapply2 succ_red). Qed. 

 
Lemma w_red1 : forall M N, sk_red (Wop @ M @ N) (wait M N).
Proof.  eval_tac.  Qed.    

Lemma w_red : forall M N P, sk_red (Wop @ M@ N @ P) (M@ N @ P).
Proof.  eval_tac.  Qed.    
 
 
(* Fixpoint Functions *)



Definition self_apply := Sop @ Iop @ Iop. 

Definition self_apply2 f :=  Sop @ self_apply @ (Kop @ f). 
(* compare to \w. wwf *)

Definition Y2_aux w f := wait (self_apply2 f) w.
(* compare to [x] self_apply2 f w x *) 
       
Definition omega2 := \"w" (\"f" (Ref "f" @ (Y2_aux (Ref "w") (Ref "f")))).

Definition Y2 f := Y2_aux omega2 f. 

Lemma self_apply2_red : forall f w, sk_red (self_apply2 f @ w) (w @ w @ f).
Proof. eval_tac. Qed. 

Lemma Y2_aux_red: forall w f x, sk_red(Y2_aux w f @ x) (self_apply2 f @ w @ x).
Proof. intros; unfold Y2_aux; apply wait_red.  Qed.


Lemma Y2_program: forall f, program f -> program (Y2 f). 
Proof. intros; program_tac; auto. Qed.


Theorem fixpoint_function : forall f x, sk_red(Y2 f @ x) (f@ (Y2 f) @ x).
Proof. eval_tac. Qed.
  
Definition Y2_red := fixpoint_function.


(* Y3 *)


Definition Y3_aux_primer :=
  \"x" (bracket "y" ((Ref "sf") @ (Ref "w") @ (Ref "x") @ (Ref "y"))).


Definition Y3_aux w f :=
Sop @ (Sop @ (Kop @ Sop) @ (Sop @ (Kop @ (Sop @ (Sop @ (Kop @ self_apply2 f) @ (Kop @ w)))) @ Kop)) @
    (Kop @ (Sop @ Kop @ Kop)).
       
Definition omega3 := \"w" (\"f" (Ref "f" @ (Y3_aux (Ref "w") (Ref "f")))).

Definition Y3 f := Y3_aux omega3 f. 

Lemma Y3_aux_red: forall w f x y, combination w -> sk_red (Y3_aux w f @ x @ y) (self_apply2 f @ w @ x @ y).
Proof.  intros; unfold Y3_aux, Y3_aux_primer, bracket. succtac; zerotac.  Qed.


Lemma Y3_program: forall f, program f -> program (Y3 f). 
Proof. intros; program_tac. Qed.


Theorem Y3_red : forall f x y, sk_red (Y3 f @ x @ y) (f@ (Y3 f) @ x @ y).
Proof. eval_tac. Qed.


(* Y4 *)


Definition Y4_aux_primer :=
  \"x" (\"y" (bracket "z" ((Ref "sf") @ (Ref "w") @ (Ref "x") @ (Ref "y") @ (Ref "z")))).


Definition Y4_aux w f := Sop @
       (Sop @ (Kop @ Sop) @
        (Sop @ (Kop @ (Sop @ (Kop @ Sop))) @
         (Sop @
          (Sop @ (Kop @ Sop) @
           (Sop @ (Kop @ Kop) @
            (Sop @ (Kop @ Sop) @ (Sop @ (Kop @ (Sop @ (Sop @ (Kop @ self_apply2 f) @ (Kop @ w)))) @ Kop)))) @
          (Kop @ Kop)))) @ (Kop @ (Kop @ (Sop @ Kop @ Kop))).

Definition omega4 := \"w" (\"f" (Ref "f" @ (Y4_aux (Ref "w") (Ref "f")))).

Definition Y4 f := Y4_aux omega4 f. 

Lemma Y4_aux_red:
  forall w f x y z, combination w -> sk_red(Y4_aux w f @ x @ y @ z) (self_apply2 f @ w @ x @ y @ z).
Proof.
  intros; unfold Y4_aux, Y4_aux_primer, bracket.
  do 16 (eapply2 succ_red).
  aptac;
    [ aptac;
      [ aptac;
        [ aptac;
          [ aptac;
            [ eval_tac
            | eapply2 succ_red
            | aptac;
              [ zerotac
              | aptac; [  eval_tac
                       |  eapply2 succ_red
                       |  aptac;
                          [ zerotac
                          | aptac; [ eval_tac | eapply2 succ_red | eapply2 succ_red]
                          | ]
                       ]
              |]
            ]
          |  |]
        | |]
      | |]
    | |];
    zerotac; 
    aptac;
    [ aptac;  [ eapply2 succ_red |  zerotac | eapply2 succ_red]
    | zerotac
    | succtac; zerotac
      ].
Qed.


Lemma Y4_program: forall f, program f -> program (Y4 f). 
Proof. intros; program_tac. Qed.


Theorem Y4_red : forall f x y z, sk_red (Y4 f @ x @ y @ z) (f@ (Y4 f) @ x @ y @ z).
Proof.
  eval_tac.
  apply preserves_app_sk_red. apply preserves_app_sk_red. apply preserves_app_sk_red.
  apply preserves_app_sk_red. all: eval_tac.
Qed.


(* Basic Arithmetic *) 

(* Church Numerals *) 

Definition church_zero := Kop @ Iop .
Definition church_successor := \"n" (\"f" (\"x" ((Ref "f") @ ((Ref "n") @ (Ref "f") @ (Ref "x"))))).

Lemma church_successor_red :
  forall n f x, sk_red (church_successor @ n @ f @ x) (f@ (n @ f @ x)).
Proof.  eval_tac. Qed. 

Definition church_plus m := App m church_successor.

Lemma church_plus_zero: forall n, sk_red (church_plus church_zero @ n) n.
Proof. eval_tac. Qed.


Lemma church_plus_successor:
  forall m n,  sk_red (church_plus (church_successor @ m) @ n)
                      (church_successor @ (church_plus m @ n)).
Proof.  eval_tac.  Qed. 
    
Definition church_times m n := m@ (church_plus n) @ church_zero.

Lemma church_times_zero: forall n, sk_red (church_times church_zero n) church_zero.
Proof. eval_tac. Qed.


Lemma church_times_successor:
  forall m n,  sk_red (church_times (church_successor @ m) n)
                      ((church_plus n) @ (church_times m n)).
Proof.  eval_tac. Qed. 


(* 
   The combinator corresponding to Kleene's predecessor for the Church numerals in lambda-calculus  
   does not have the desired properties because star abstraction breaks redexes. 
 *)

Definition church_predecessor :=
  \"n" (\"f" (\"x"
                           ((Ref "n")
                              @ (\"g" (\"h" (App (Ref "h") (App (Ref "g") (Ref "f")))))
                              @ (\"u" (Ref "x"))
                              @ (\"u" (Ref "u"))
           ))).

(* Scott numerals *)

Definition scott_zero := Kop .
Definition scott_successor := Sop @ (Kop @ Kop) @ (Sop @ (Kop @ (Sop @ Iop)) @ Kop).


Lemma scott_successor_red :
  forall n f x, sk_red (scott_successor @ n @ x @ f) (f@ n). 
Proof.  eval_tac. Qed. 

Definition scott_plus :=
  Y3 (\"p" (\"m" (\"n"
                               ((Ref "n") @ (Ref "m") @
                                    ((Ref "p") @ (scott_successor @ (Ref "m"))))))).

Lemma scott_plus_zero: forall m, sk_red (scott_plus @ m @ scott_zero) m.
Proof. eval_tac.  Qed.

Lemma scott_plus_successor:
  forall m n,  sk_red (scott_plus @ m @ (scott_successor @ n))
                      (scott_plus @ (scott_successor @ m) @ n).
Proof.
 intros; auto_t. unfold scott_plus at 1. eapply transitive_red. apply Y3_red. fold scott_plus. 
 star_tac "n";  star_tac "m"; star_tac "p";  trtac.  unfold scott_successor at 1; trtac. 
Qed.

Definition scott_times :=
  Y3 (\"p" (\"m" (\"n"
                   ((Ref "n")
                      @ scott_zero
                      @ (\"n1" (scott_plus
                                  @ (Ref "m")
                                  @ ((Ref "p") @ (Ref "m") @ (Ref "n1")))))))).

Lemma scott_times_zero: forall m, sk_red (scott_times @ m @ scott_zero) scott_zero.
Proof. eval_tac.  Qed.


Lemma scott_times_successor:
  forall m n,  sk_red (scott_times @ m @ (scott_successor @ n))
                      (scott_plus @ m @ (scott_times @ m @ n)).
Proof.
 intros; auto_t. unfold scott_times at 1. eapply transitive_red. apply Y3_red. fold scott_times. 
 star_tac "n1"; star_tac "n"; star_tac "m"; star_tac "p". 
 unfold scott_successor; trtac.
Qed.


Definition scott_predecessor := Sop @ (Sop @ Iop @ (Kop @ Kop)) @ (Kop @ Iop).

Lemma scott_predecessor_zero: sk_red (App scott_predecessor scott_zero) scott_zero.
Proof. eval_tac. Qed. 

Lemma scott_predecessor_successor: forall n, sk_red (scott_predecessor @ (scott_successor @ n)) n.
Proof. eval_tac. Qed. 

Definition scott_minus := 
  Y3 (\"p" (\"m" (\"n"
                               ((Ref "n") @ (Ref "m") @
                                    ((Ref "p") @ (scott_predecessor @ (Ref "m"))))))).

Lemma scott_minus_zero: forall m, sk_red (scott_minus @ m @ scott_zero) m.
Proof. eval_tac.  Qed.


Lemma scott_minus_successor:
  forall m n,  sk_red (scott_minus @ (scott_successor @ m) @ (scott_successor @ n))
                      (scott_minus @ m @ n).
Proof.
  intros; auto_t. unfold scott_minus at 1. eapply transitive_red. apply Y3_red. fold scott_minus.
  star_tac "n"; star_tac "m"; star_tac "p";   trtac. 
 unfold scott_predecessor at 1; unfold scott_successor at 1. trtac. 
 repeat  apply preserves_app_sk_red;  eval_tac. 
Qed.



(* 8.4 Incompleteness of Combinatory Logic *) 


(* 
Combinatory logic cannot distinguish SKS and SKK. 
Hence equality is not definable, so SK-calculus is not complete.
Hence it does not have any tagged identities, 
so there is no meaningful translation from tree calculus to SK-calculus 

The proofs introduce a new relation id_red that is paramterised by an identity function id.
The main technical result is a pentagon.

                id
   M ------------> N 
   |               |
 p |               | p
   P - - -> Q - -> R
        p       id

Here are the details. 
*) 
                         

(* compounds *)

Inductive compound : SK -> Prop :=
| S1 : forall M,  compound (Sop @ M)
| S2 : forall M N, compound (Sop @ M @ N)
| K1 : forall M,  compound (Kop @ M)
.

Hint Constructors compound: TreeHintDb.


Definition left_component M :=
  match M with
  | Ref _ => Iop 
  | Sop => Iop
  | Kop => Iop 
  | M1 @ _ => M1
  end.
  
Definition right_component M :=
  match M with
  | Ref _ => M
  | Sop => M
  | Kop => M 
  | _ @ M2 => M2
  end.


Lemma preserves_compounds_s_red: forall M N, s_red M N -> compound M -> compound N. 
Proof.
  cut(forall red M N, multi_step red M N -> red = s_red1 -> compound M -> compound N);
    [intro c; intros; eapply2 c
    | intros red M N r; induction r as [ | ? ? ? ? r1 r2]; split_all; subst; eapply2 IHr2;   
      inversion r1; subst; inv1 compound; try discriminate; inv s_red1; discriminate]. 
Qed.

Lemma preserves_components_s_red:
  forall M N, s_red M N -> compound M ->
              s_red (left_component M) (left_component N) /\
              s_red (right_component M) (right_component N). 
Proof.
  cut(forall red M N, multi_step red M N -> red = s_red1 -> compound M ->
              s_red (left_component M) (left_component N) /\
              s_red (right_component M) (right_component N)); 
    [ intro c; intros; eapply2 c
    | intros red M N r; induction r; intros e c; subst; try split; zerotac; 
      inversion c; subst; inv s_red1; elim IHr; auto_t; simpl; intros; eapply2 succ_red
    ]. 
Qed.

(* ranked reduction *)


Inductive p_ranked : nat -> SK -> SK -> Prop :=
| ranked_zero: forall M,  p_ranked 0 M M
| ranked_succ: forall n M N P, s_red1 M N -> p_ranked n N P -> p_ranked (S n) M P
.

Hint Constructors p_ranked : TreeHintDb.

Lemma transitive_p_ranked:
  forall n M N, p_ranked n M N -> forall p P, p_ranked p N P ->
                                              p_ranked (n+p) M P.
Proof. induction n; intros; inversion H; subst; auto; eapply2 ranked_succ. Qed.

Lemma s_red_implies_p_ranked:
  forall M N, s_red M N -> exists n, p_ranked n M N.
Proof.
  cut(forall red M N, multi_step red M N -> red = s_red1 -> exists n, p_ranked n M N);
    [ intro c; intros; eapply2 c
    | intros red M N r; induction r; intros; subst; 
      [ exist 0
      | assert(r1: exists n, p_ranked n N P) by auto;
        elim r1; intro k; intros; exists (S k); eapply2 ranked_succ
    ]]. 
Qed. 

  
Lemma p_ranked_implies_s_red:
  forall n M N, p_ranked n M N -> s_red M N.
Proof. induction n; intros M N r; inversion r; subst; auto; [zerotac | eapply2 succ_red; eapply2 IHn]. Qed.


  
Lemma diamond_p_ranked_strip :
  forall m M N, p_ranked m M N ->
                forall P, s_red1 M P ->
                          exists Q, p_ranked m P Q /\ s_red1 N Q.
Proof.
  induction m; intros M N rN P rP;
    [inversion rN; subst; auto; exist P
    | inversion rN as [| ? ? M1 ? r1 r2]; subst; 
      assert(d: exists Q, s_red1 M1 Q /\ s_red1 P Q) by eapply2 diamond_s_red1; 
      elim d; intros Q (?&?);   
      elim (IHm M1 N r2 Q); auto_t;  
      intros x0 (?&?); exist x0; eapply2 ranked_succ
     ]. 
Qed.



Lemma diamond_p_ranked :
  forall n M N, p_ranked n M N ->
                forall p P, p_ranked p M P ->
                          exists Q, p_ranked n P Q /\ p_ranked p N Q.
Proof.
  induction n; intros M N rN p P rP;
    [ inversion rN; subst; auto; exist P
    | inversion rN as  [| ? ? M1 ? r1 r2]; subst; 
      assert(d: exists Q, p_ranked p M1 Q /\ s_red1 P Q) by eapply2 diamond_p_ranked_strip; intros; auto_t;
      elim d; intros M2 (?&?);   elim (IHn M1 N r2 p M2); auto;
      intros M3 (?&?); exist M3; eapply2 ranked_succ
    ]. 
Qed.



(* back to main line *) 

Definition is_equal eq :=
  (forall M, program M -> sk_red (eq @ M @ M @ (Ref "x") @ (Ref "y")) (Ref "x"))
/\ 
( forall M N, program M -> program N -> M <> N ->
              sk_red (eq @ M @ N @ (Ref "x") @ (Ref "y")) (Ref "y")). 


(* substitution *)

Fixpoint substitute (M N : SK) x  :=
  match M with
  | Ref y => if eqb x y then N else M
  | Sop | Kop  => M 
  | M1 @ M2 => (substitute M1 N x) @ (substitute M2 N x)
  end.


Definition substitute_preserves_l (red: SK -> SK -> Prop) := 
forall (M M' N : SK) k, red M M' -> red  (substitute M N k) (substitute M' N k).

Lemma substitute_preserves_l_multi_step : 
forall (red: SK -> SK -> Prop), substitute_preserves_l red -> 
  substitute_preserves_l (multi_step red). 
Proof. red; induction 2; intros; auto_t; eapply2 succ_red.  Qed.


Lemma substitute_preserves_l_s_red1: substitute_preserves_l s_red1.
Proof. red; intros M M' N s r;  induction r; subst; simpl; auto_t. Qed. 
 
Lemma substitute_preserves_l_s_red: substitute_preserves_l s_red.  
Proof. eapply substitute_preserves_l_multi_step; eapply substitute_preserves_l_s_red1.  Qed. 


Lemma substitute_preserves_programs: forall p, program p -> forall x N, substitute p x N = p. 
Proof.  intros p pr; induction pr; intros; simpl; repeat f_equal; auto_t. Qed. 


(* separators  *)

Definition separator M N s := 
  s_red (s@ M @ (Ref "x") @ (Ref "y")) (Ref "x") /\
  s_red (s @ N @ (Ref "x") @ (Ref "y")) (Ref "y") 
.
  
Definition identity_program id := program id /\ sk_red (id@ (Ref "x")) (Ref "x").
                       

Inductive id_red : SK -> SK -> Prop :=
| id_I : forall id, identity_program id -> id_red id Iop
| id_ref: forall i, id_red (Ref i) (Ref i)
| id_S : id_red Sop Sop
| id_K : id_red Kop Kop    
| id_app : forall M M' N N', id_red M M' -> id_red N N' ->
                               id_red (M@ N) (M' @ N')  
.
Hint Constructors id_red : TreeHintDb.


Lemma id_red_refl: forall M, id_red M M.
Proof. induction M; auto_t. Qed.

Lemma id_red_K : forall M, id_red Kop M -> M = Kop.
Proof.  intros; inv id_red; inv1 identity_program; stable_tac. Qed. 


Lemma id_red_K1 : forall M N, id_red (Kop @ M) N -> exists P, N = Kop @ P /\ id_red M P.
Proof.
  intros M N r; inv id_red; inv1 identity_program; auto_t. inversion H0. clear H0. inv1 program. 
  (* 2 *)
  inv1 program. 
  assert(r1: s_red M (Ref "x")) by  
      (eapply triangle_s_red; [ | apply sk_red_to_s_red | ]; auto_t; apply sk_red_to_s_red; trtac);
  subst.  stable_tac; inv1 program.
  (* 1 *) 
  stable_tac. 
Qed.

Lemma id_red_S : forall M, id_red Sop M -> M = Sop.
Proof.  intros; inv id_red; inv1 identity_program; stable_tac. Qed. 


Lemma id_red_S1 : forall M N, id_red (Sop @ M) N -> exists P, N = Sop @ P /\ id_red M P.
Proof.
  intros; inv id_red; inv1 identity_program; auto_t;
    [ match goal with H0 : program _ |- _ =>  inversion H0; subst end |]; stable_tac. 
Qed.

Lemma id_red_S2 :
  forall M N P, id_red (Sop @ M @ N) P ->
                (exists Q R, P = Sop @ Q @ R /\ id_red M Q /\ id_red N R)
                \/
                (P = Iop /\ identity_program (Sop @ M @ N)).
Proof.
  intros; inv id_red; inv1 identity_program; left; auto_t; 
  [ match goal with H0 : program _ |- _ =>  inversion H0 end |]; stable_tac.  
Qed.



  
(* Here is the pentagon for s_red1 *)
 
 
Lemma pentagon_id_red_s_red1:
  forall M N,  id_red M N ->
               forall P, s_red1 M P ->
                         exists Q1 Q2,  s_red P Q1 /\ id_red Q1 Q2 /\
                                        s_red N Q2 .
Proof.
  intros M N r; induction r; intros P rP; inv1 identity_program; inv s_red1. 
  (* 7 *)
  match goal with H: identity_program _ |- _ => inversion H; clear H end; 
  stable_tac;  exists id, Iop; repeat split; [ zerotac | apply id_I;  red; intros; auto_t | zerotac]. 
  (* 6 *)
  exists(Ref i), (Ref i); repeat split; zerotac; auto_t. 
  exists Sop, Sop;  repeat split; zerotac; auto_t.
  exists Kop, Kop;  repeat split; zerotac; auto_t.
  (* 3 *)
  match goal with
    r1: id_red M ?M', r2: id_red N ?N' , H1 : s_red1 M ?M'0 , H3 : s_red1 N ?N'0 |- _ =>
    assert(ex1: exists Q1 Q2 : SK, s_red M'0 Q1 /\ id_red Q1 Q2 /\ s_red M' Q2) by eapply2 IHr1; 
      assert(ex2: exists Q1 Q2 : SK, s_red N'0 Q1 /\ id_red Q1 Q2 /\ s_red N' Q2) by eapply2 IHr2
  end. 
  elim ex1; intros M1 ex12; elim ex12; intros M2 (?&?&?). 
  elim ex2; intros N1 ex22; elim ex22; intros N2 (?&?&?). 
      exists (M1@N1), (M2@N2); split_all; eapply2 preserves_app_s_red.  
  (* 2 *)
  all: cycle 1.
  elim(IHr1 (Kop @ P)); auto_t; intros P1 ex1. elim ex1; intros P2 (?&?&?).  
  elim(preserves_components_s_red (Kop @ P) P1); simpl; auto_t; intros;  stable_tac.   
  caseEq P1; intros; subst; simpl in *; subst; try discriminate.
  clear r1. match goal with H : id_red _ _ |- _ =>   elim(id_red_K1 _ _ H); auto end.
  intros P3 (?&?); subst. 
  repeat eexists; [ eassumption | eassumption | ]. 
  eapply transitive_red; [eapply preserves_app_s_red ; [eassumption |] |] ; trtac;
    eapply2 succ_red.
  (* 1 *)
  match goal with | H: s_red1 N P' |- _ =>
                    elim(IHr2 P'); auto_t; intros x1 ex1; elim ex1; intros P1 (?&? &?) end. 
  elim(IHr1 (Sop @ M'0 @ N'0)); auto_t;  intros x2 ex2;  elim ex2; intros P2 (?&?&?); auto_t. 
  match goal with H: s_red (_ @ _) _ |- _ =>
                  elim(preserves_components_s_red _ _ H); intros; clear H; simpl in *; auto_t end.
  match goal with H: s_red (_ @ _) _ |- _ =>
                  elim(preserves_components_s_red _ _ H); intros; clear H; simpl in *; auto_t end.
  assert(left_component (left_component x2) = Sop) by (apply normal_is_stable2; auto_t).
  caseEq x2; intros; subst; simpl in *; subst; try discriminate.
  match goal with H: left_component ?s = Sop |- _ => 
                  caseEq s; intros; subst; simpl in *; subst; try discriminate end.
  clear r1 r2. match goal with H : id_red _ _ |- _ => elim(id_red_S2 _ _ _ H) end.
  (* 2 *)
  intro ex3; elim ex3; intros Q ex4.  elim ex4; intros R (?&?&?); subst. 
  match goal with H: s_red M'0 ?s2, H1: s_red N'0 ?s0 , H2: id_red s2 ?x0 , H3: id_red ?s0 ?x3 |- _ =>
                  exists (s2 @ x1 @ (s0 @ x1)),  (Q @ P1 @ (R @ P1)); repeat split end; 
  [repeat apply preserves_app_s_red; auto_t | repeat apply id_app; auto_t; apply id_red_refl|]. 
  eapply transitive_red; [eapply preserves_app_s_red; eassumption| ]. eapply succ_red.
  eapply2 s_s_red.  zerotac. 
  (* 1 *)
  intros (?&p); subst;   inv1 identity_program.  exists x1, P1; repeat split; auto_t. 
  (* 2 *)
  match goal with
    H : sk_red (Sop @ ?s2@ ?s0 @ (Ref "x")) (Ref "x") |- _ => 
    assert (s_red (s2 @ (Ref "x") @ (s0 @ (Ref "x"))) (Ref "x")) by 
        (eapply triangle_s_red; auto_t; [| apply sk_red_to_s_red; eassumption]; eapply2 succ_red)
  end.
  assert(sk_red (substitute (s2 @ (Ref "x") @ (s0 @ (Ref "x"))) x1 "x")
                    (substitute (Ref "x") x1 "x")) by 
        (apply s_red_to_sk_red; apply substitute_preserves_l_s_red; zerotac; auto_t);
  simpl in *; auto. 
  match goal with | pr: program _ |- _ => inversion pr; subst end.
 rewrite ! substitute_preserves_programs in *; auto.
 eapply transitive_red;
   [ eapply preserves_app_s_red; eapply preserves_app_s_red; eauto |]; apply sk_red_to_s_red; auto.
   (* 1 *)
  eapply transitive_red; [ eapply preserves_app_s_red; eassumption | ].
  cbv; eapply succ_red. eapply2 s_s_red.  eapply succ_red. eapply2 k_s_red. zerotac.
Qed.


(* 
Generalizing the pentagon from s_red1 to s_red 
requires a count of the number of reductions, 
so use p_ranked instead. 
*) 

Lemma pentagon_id_red_p_ranked:
  forall m M P,  p_ranked m M P ->
                 forall N, id_red M N ->
                           exists p Q1 Q2 n,  p_ranked p P Q1 /\ id_red Q1 Q2 /\
                                              p_ranked n N Q2 .
Proof.
  induction m; intros M P r N r1; inversion r; clear r; subst; auto.
  (* 2 *)
  exists 0, P, N; exist 0.
  (* 1 *)
  assert(ex:exists Q1 Q2,  s_red N0 Q1 /\ id_red Q1 Q2 /\  s_red N Q2) by  eapply2 pentagon_id_red_s_red1.
  elim  ex; intros N1 ex1; elim ex1; intros N2 (?&?&?).
  assert(ex2:exists n, p_ranked n N0 N1) by (eapply s_red_implies_p_ranked; auto_t); intros; auto_t.
  elim ex2; intros n r2.
  match goal with
    H2: p_ranked ?x1 N0 ?x |- _ => 
    assert(ex3:exists Q, p_ranked m x Q /\ p_ranked x1 P Q) by (eapply diamond_p_ranked; auto_t); intros
  end.
  elim ex3; intros N3 (r3&r4).
  assert(ex4:exists p Q1 Q2 n,  p_ranked p N3 Q1 /\ id_red Q1 Q2 /\ p_ranked n N2 Q2)
    by (eapply IHm; auto_t).
  elim ex4; intros p ex5; elim ex5; intros Q1 ex6; elim ex6; intros Q2 ex7; elim ex7; intros x (?&?&?). 
  assert(ex8:exists q, p_ranked q N N2) by (eapply s_red_implies_p_ranked; auto_t).
  elim ex8; intros q r5. 
    exists (n + p), Q1, Q2, (q+x); repeat split; auto_t; eapply transitive_p_ranked; auto_t. 
Qed.

Lemma pentagon_id_red_s_red:
  forall M P,  s_red M P ->
               forall N, id_red M N ->
                         exists Q1 Q2,  s_red P Q1 /\ id_red Q1 Q2 /\
                                        s_red N Q2 .
Proof.
  intros M P r N rN. 
  elim(s_red_implies_p_ranked _ _ r); intros; auto_t.   
  assert(ex: exists p Q1 Q2 n,  p_ranked p P Q1 /\ id_red Q1 Q2 /\ p_ranked n N Q2) 
    by eapply2 pentagon_id_red_p_ranked.
  elim ex; intros ? ex1; elim ex1; intros ? ex2. elim ex2; intros ? ex3; elim ex3; intros n (?&?&?).
  match goal with
     rN: id_red M N, H0 : id_red ?x1 ?x2 |- _ => 
     exists x1, x2; repeat split; auto_t; eapply p_ranked_implies_s_red; auto_t
  end. 
Qed.

  (* 
If parallel reduction is to a variable  
then the pentagon becomes a triangle.
 *)



Lemma triangle_id_red_s_red_ref:
  forall M x, s_red M (Ref x) ->
            forall N, id_red M N ->
                      s_red N (Ref x) .
Proof.
  intros M x r N rN;
  assert(ex: exists Q1 Q2, s_red (Ref x) Q1 /\ id_red Q1 Q2 /\ s_red N Q2) by eapply2 pentagon_id_red_s_red; 
    elim ex; intros Q1 ex2; elim ex2; intros Q2 (?&?&?); auto_t;
  stable_tac;  inv id_red; inv1 identity_program; inv1 program. 
Qed.



Theorem no_separable_identities_in_SK :
  forall id1 id2 s,  ~(identity_program id1 /\ identity_program id2 /\ separator id1 id2 s).
Proof.
  intros id1 id2 s. intros (?&?&?); auto_t.
  match goal with H2: separator _ _ _ |- _ => inversion H2; subst end. 
  assert(r1: s_red (s @ Iop @ (Ref "x") @ (Ref "y")) (Ref "y")) by 
  (eapply triangle_id_red_s_red_ref;
    [ eassumption; auto_t;  repeat apply id_app; auto_t; apply id_red_refl
    | repeat apply id_app; auto_t; apply id_red_refl
    ]);
  assert(r2: s_red (s @ Iop @ (Ref "x") @ (Ref "y")) (Ref "x"))  by  
  (eapply triangle_id_red_s_red_ref; [   eassumption | repeat apply id_app; auto_t; apply id_red_refl]);
  elim(diamond_s_red _ _ r1 _ r2); intros x (?&?);  repeat stable_tac.   
Qed.



Theorem equality_of_programs_is_not_definable_in_SK:  forall eq,  not (is_equal eq). 
Proof.
  intro eq; intro iseq;
  assert(s_red (eq @ (Sop @ Kop @ Sop) @ Iop @ (Ref "x") @ (Ref "y")) (Ref "y")) by 
  (apply sk_red_to_s_red; apply iseq; cbv; auto 20 with *;  discriminate); 
  assert(id_red (eq @ (Sop @ Kop @ Sop) @ Iop @ (Ref "x") @ (Ref "y"))
                (eq @ Iop @ Iop @ (Ref "x") @ (Ref "y"))) by 
      (eapply id_app;
       [ eapply id_app;
         [ eapply id_app;
           [ eapply id_app;
             [ apply id_red_refl
             | apply id_I; intros; auto_t; eval_tac]
            |]
          |]
        |];
       apply id_red_refl);  
  assert(r1: s_red (eq @ Iop @ Iop @ (Ref "x") @ (Ref "y")) (Ref "x")) by 
      (apply sk_red_to_s_red; apply iseq; cbv; auto_t);
  assert(r2: s_red (eq @ Iop @ Iop @ (Ref "x") @ (Ref "y")) (Ref "y")) by 
      (eapply triangle_id_red_s_red_ref; auto_t);
  elim(diamond_s_red _ _ r1 _ r2); split_all; repeat stable_tac; auto_t. 
Qed.


(* 8.5 Meaningful Translation *)


                       (* some tree machinery *)
Definition RefT := Rewriting_partI.Ref.
Definition ApT := Rewriting_partI.App.
Definition SopT := Rewriting_partI.Sop.
Definition KopT := Rewriting_partI.K.
Definition IopT := Rewriting_partI.Id.
Definition programT := Rewriting_partI.program. 
Definition identity_programT id := programT id /\ t_red (ApT id (RefT "x")) (RefT "x").
Definition normalisableT M := exists N,  t_red M N /\ Rewriting_partI.program N.


Definition separatorT M N s := 
  t_red (ApT (ApT (ApT s M) (RefT "x")) (RefT "y")) (RefT "x") /\
  t_red (ApT (ApT (ApT s N) (RefT "x")) (RefT "y")) (RefT "y") 
.

Definition irreducible M := forall N, t_red1 M N -> False.

Lemma programs_are_irreducible: forall M, programT M -> irreducible M.
Proof.
  intros M prM; induction prM; intro M1; intro r; auto; inversion r; subst; Rewriting_partI.inv t_red1.
Qed.



Definition meaningful_translation_sk_to_tree (f: SK -> Tree) :=
  (forall M N, sk_red1 M N -> t_red (f M) (f N)) /\ (* strong version *) 
  (forall M N, f(M@ N) = ApT (f M) (f N)) /\  (* applications *) 
  (forall M, program M -> normalisableT (f M)) /\
  (forall i, f (Ref i) = RefT i).              (* variables *) 



Fixpoint sk_to_tree t := 
match t with 
| Ref x => Rewriting_partI.Ref x
| Sop => Rewriting_partI.Sop 
| Kop =>  K
| u@ v => Rewriting_partI.App (sk_to_tree u) (sk_to_tree v)
end.


Theorem sk_to_tree_red: 
forall M N, sk_red1 M N -> t_red (sk_to_tree M) (sk_to_tree N).
Proof.
intros; induction H; subst; simpl;  unfold_op; tree_red;
eapply2 preserves_app_t_red; eapply Rewriting_partI.zero_red.
Qed. 

Open Scope tree_scope.

Theorem meaningful_translation_from_sk_to_tree:
  meaningful_translation_sk_to_tree sk_to_tree. 
Proof. 
  repeat split; (try (split_all; fail)). 
  (* 2 *)
  intros; eapply2 sk_to_tree_red.
  (* 1 *)
  intros M prM; induction prM; subst.  
  (* 5 *)
  exist SopT; [apply Rewriting_partI.zero_red | Rewriting_partI.program_tac].
  (* 4 *)  
  inversion IHprM as [ x (?&?)]; auto_t. 
  exist (△ @ (△@(K@x)) @(△@K@(K@△))).
  eapply Rewriting_partI.transitive_red. eapply preserves_app_t_red.
  apply Rewriting_partI.zero_red. eassumption. tree_red. Rewriting_partI.program_tac.
  (* 3 *) 
  inversion IHprM1 as [ x1 (?&?)]; inversion IHprM2 as [ x2 (?&?)]; subst; intros; auto_t. 
  exists (△ @ (△@x2)@x1); split.
  eapply Rewriting_partI.transitive_red. eapply preserves_app_t_red. eapply preserves_app_t_red.
  apply Rewriting_partI.zero_red. eassumption. eassumption. tree_red. Rewriting_partI.program_tac.
  (* 2 *) 
  exist KopT. apply Rewriting_partI.zero_red. Rewriting_partI.program_tac.
  (* 1 *)
  inversion IHprM as [x (?&?)]; subst; intros; auto_t. 
  exists (K@ x); split.
  eapply Rewriting_partI.transitive_red. eapply preserves_app_t_red.
  apply Rewriting_partI.zero_red.  eassumption. tree_red. Rewriting_partI.program_tac.
Qed.


(* 8.6 No Trees in Combinatory Logic *) 

Definition meaningful_translation_tree_to_sk (f: Tree -> SK) :=
  (forall M N, t_red M N ->
               exists P, sk_red (f M) P /\        (* equivalence *) 
                         sk_red (f N) P) /\
  (forall M N, f(ApT M N) = App (f M) (f N)) /\  (* applications *) 
  (forall M, programT M -> normalisable (f M)) /\ (* programs *) 
  (forall i, f (RefT i) = Ref i)               (* variables *)
    .


Lemma meaningful_translation_preserves_identity_programs:
  forall f, meaningful_translation_tree_to_sk f ->
            forall id, identity_programT id ->
                       exists id2, sk_red (f id) id2 /\ identity_program id2.
Proof.
  intros f mt id pr;  inversion pr; inversion mt as (?&r2&?&r).  
  assert(ex:exists Q, sk_red (f (ApT id (RefT "x"))) Q /\ sk_red (f (RefT "x")) Q) by auto;
    elim ex; intros x (?&?); auto_t.   
  rewrite r in *.   stable_tac. 
  rewrite r2 in *.  
  assert(nf: normalisable (f id)) by auto_t. elim nf; intros x (?&?). 
  assert (e: exists Q, s_red (Ref "x") Q /\ s_red (App x (Ref "x")) Q) .  
        eapply diamond_s_red; auto_t. 
     eapply sk_red_to_s_red; eassumption. 
      eapply preserves_app_s_red; [ apply sk_red_to_s_red | auto]. auto. rewrite r.  zerotac. 
  elim e; intros x0 (?&?).   stable_tac. 
  exist x; eapply2 s_red_to_sk_red.  
  Qed. 



Lemma meaningful_translation_preserves_separators:
  forall f, meaningful_translation_tree_to_sk f ->
            forall M N s, separatorT M N s -> separator (f M) (f N) (f s).
Proof.
  intros f mf M N s sep; elim mf. intros f_red f_rest. elim f_rest; intros f_app f_rest2.
  elim f_rest2; intros f_prog f_ref. 
  (* 2 *)
  inversion sep.
  assert(ex:exists Q, sk_red (f (ApT (ApT (ApT s M) (RefT "x")) (RefT "y"))) Q /\ sk_red (f (RefT "x")) Q)
    by (apply f_red; auto_t). 
  assert(ey:exists Q, sk_red (f (ApT (ApT (ApT s N) (RefT "x")) (RefT "y"))) Q /\ sk_red (f (RefT "y")) Q)
    by (apply f_red; auto_t). 
  elim ex; intros qx (?&?); elim ey; intros qy (?&?); auto_t. 
  all: rewrite ! f_app in *; rewrite ! f_ref in *. repeat stable_tac. 
  split_all. 
Qed.


Open Scope sk_scope. 


Theorem no_translation_tree_to_sk:
  forall f, ~(meaningful_translation_tree_to_sk f). 
Proof.
  (* combine the previous two lemmas *)
  intro f; intro mf; elim mf;
    intros f_red f_rest; elim f_rest; intros f_app f_rest2; elim f_rest2; intros f_prog f_ref. 
  (* 1 *)
  assert(eK: exists idK, sk_red (f (tag KopT IopT)) idK /\ identity_program idK) .     
  eapply meaningful_translation_preserves_identity_programs; repeat split; auto_t;
  [ Rewriting_partI.program_tac |  eapply Rewriting_partI.transitive_red; [apply tag_apply | tree_red]]. 
  assert(eKI: exists idKI, sk_red (f (tag (ApT KopT IopT) IopT)) idKI /\ identity_program idKI) by     
  (apply meaningful_translation_preserves_identity_programs; auto_t; 
  intros; split; [ Rewriting_partI.program_tac |  eapply Rewriting_partI.transitive_red; [apply tag_apply | tree_red]]). 
  elim eK; intros x (?&?); elim eKI; intros x0 (?&?); auto_t.
  apply (no_separable_identities_in_SK x x0 (f getTag)); split; auto_t.
  split; auto_t.
  (* 1 *)
  assert(s_red (App (App (App (f getTag) (f (tag KopT IopT))) (Ref "x")) (Ref "y"))
               (App (App (App (f getTag) x) (Ref "x")) (Ref "y"))). 
  repeat apply preserves_app_s_red. 2: apply sk_red_to_s_red. all: zerotac.  
  assert(eq: exists Q, sk_red (f (ApT (ApT (ApT getTag (tag KopT IopT)) (RefT "x")) (RefT "y"))) Q /\
                   sk_red (f (RefT "x")) Q).
  eapply f_red.
  eapply Rewriting_partI.transitive_red. eapply preserves_app_t_red.  eapply preserves_app_t_red.
  tree_red.  1,2: eapply Rewriting_partI.zero_red. tree_red. auto. 
  (* 1 *) 
 assert(s_red (App (App (App (f getTag) (f (tag (ApT KopT IopT) IopT))) (Ref "x")) (Ref "y"))
               (App (App (App (f getTag) x0) (Ref "x")) (Ref "y"))). 
  repeat apply preserves_app_s_red. 2: apply sk_red_to_s_red. all: zerotac.  
  assert(eq: exists Q, sk_red (f (ApT (ApT (ApT getTag (tag (ApT KopT IopT) IopT)) (RefT "x")) (RefT "y"))) Q /\
                   sk_red (f (RefT "y")) Q).
  eapply f_red.
  eapply Rewriting_partI.transitive_red. eapply preserves_app_t_red.  eapply preserves_app_t_red.
  tree_red.  1,2: eapply Rewriting_partI.zero_red. tree_red. auto_t. 
  (* 1 *) 
  split.
  (* 2 *)
  eapply triangle_s_red. eassumption.  rewrite <- ! f_ref; auto_t. rewrite <- ! f_app. 
  assert(t_red (ApT (ApT (ApT getTag (tag KopT IopT)) (RefT "x")) (RefT "y")) (RefT "x")).
  Rewriting_partI.aptac. Rewriting_partI.aptac. eapply getTag_tag. Rewriting_partI.zerotac. 
  Rewriting_partI.zerotac. Rewriting_partI.zerotac. Rewriting_partI.trtac.
  elim(f_red _ _ H5); auto_t. intros x1 (?&?).  rewrite ! f_ref in *.  stable_tac.
  apply sk_red_to_s_red. auto_t. auto_t. 
  (* 1 *)
  eapply triangle_s_red. eassumption.  rewrite <- ! f_ref; auto_t. rewrite <- ! f_app. 
  assert(t_red (ApT (ApT (ApT getTag (tag (ApT KopT IopT) IopT)) (RefT "x")) (RefT "y")) (RefT "y")).
  Rewriting_partI.aptac. Rewriting_partI.aptac. eapply getTag_tag. Rewriting_partI.zerotac. 
  Rewriting_partI.zerotac. Rewriting_partI.zerotac. Rewriting_partI.trtac. cbv; Rewriting_partI.trtac.
  elim(f_red _ _ H5); auto_t. intros x1 (?&?).  rewrite ! f_ref in *.  stable_tac.
  apply sk_red_to_s_red. auto_t. auto_t. 
Qed.


 (* Exercises *) 

(* 1. Define B as a combination of S and K *) 

Definition Bop := Sop @ (Sop @ (Kop @ Sop) @ (Sop @ (Kop @ Kop) @ Sop)) @ (Kop @ Kop).

Lemma b_red : forall x y z, sk_red (Bop @x@y@z) (x@z@y).
Proof. eval_tac. Qed. 

(* 2. Define C as a combination of S and K *) 

Definition Cop := Sop @ (Kop @ Sop) @ Kop. 

Lemma c_red : forall x y z, sk_red (Cop @x@y@z) (x@(y@z)). 
Proof.  eval_tac.  Qed. 

(* 3. Check the truth table for conjuction. *) 

Definition conj := Bop @ Bop @ (Kop @ Iop). 

Lemma conj_red : forall x y, sk_red (conj @ x @ y) (x @ y @ (Kop @ Iop)) .
Proof. eval_tac. Qed. 

Lemma conj_true : forall y, sk_red (conj @ Kop @ y) y .
Proof. eval_tac. Qed. 

Lemma conj_false : forall y, sk_red (conj @ (Kop @ Iop) @ y) (Kop @ Iop) .
Proof. eval_tac. Qed.

(* 4 Check iff *) 

Definition iff :=
  Sop @ Sop @ (Kop @ (Sop @ (Sop @ Iop @ (Kop @ (Kop @ Iop))) @ (Kop @ Kop))).

Lemma iff_red : 
forall x y, sk_red (iff @ x @ y) (x @ y @ (y @ (Kop @ Iop) @ Kop)). 
Proof. eval_tac.  Qed.

Lemma iff_true: forall y, sk_red (iff @ Kop @ y) y.
Proof. eval_tac.  Qed.

Lemma iff_false: 
forall y, sk_red (iff @ (Kop @ Iop) @ y) (y @ (Kop @ Iop) @ Kop).
Proof. eval_tac.  Qed.

(* 6 *)

Lemma Bop_as_star : 
\"f" (\"x" (\"y" (App (App (Ref "f") (Ref "y")) (Ref "x")))) = Bop. 
Proof. eval_tac. Qed. 

Lemma Cop_as_star : 
\"g" (\"f" (\"x" (App (Ref "g") (App (Ref "f") (Ref "x"))))) = Cop.
Proof. eval_tac. Qed.  



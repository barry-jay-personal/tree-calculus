(**********************************************************************)
(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)
(**********************************************************************)
(**********************************************************************)
(* This Program is free sofut even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 021101301 USA                                                     *)
(**********************************************************************)

(**********************************************************************)
(*            Reflective Programming in Tree Calculus                 *)
(*         Chapter 10: Divide and Conquer in SF-Calculus              *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Add LoadPath "." as Reflective.

Require Import Arith Lia Bool List String.
Require Import Reflective.Rewriting_partI. (* not used until 10.4 *) 

Set Default Proof Using "Type".

Open Scope string_scope.
Declare Scope sf_scope.
Open Scope sf_scope.

Ltac caseEq f := generalize (refl_equal f); pattern f at -1; case f. 
Ltac auto_t:= eauto with SFHintDb. 
Ltac eapply2 H := eapply H; auto_t; try lia.
Ltac split_all := simpl; intros; 
match goal with 
| H : _ /\ _ |- _ => inversion_clear H; split_all
| H : exists _, _ |- _ => inversion H; clear H; split_all 
| _ =>  try (split; split_all); try contradiction
end; try congruence; auto_t.
Ltac exist x := exists x; split_all.

(* 10.2: SF-Calculus *) 



Inductive SF:  Set :=
  | Ref : string -> SF 
  | Sop : SF   
  | Fop : SF 
  | App : SF -> SF -> SF   
.

Hint Constructors SF: sf_scope.


Notation "x @ y" := (App x y) (at level 65, left associativity) : sf_scope.


Definition Kop := App Fop Fop. 
Definition Iop := App (App Sop Kop) Kop. 

Ltac unfold_op:= unfold Iop, Kop. 



Fixpoint term_size M :=
  match M with
  | App M1 M2 => term_size M1 + term_size M2
  |  _ => 1
  end.

(* SF-reduction *) 
Inductive sf_red1 : SF -> SF -> Prop :=
| s_red: forall (M N P : SF),
             sf_red1 
                  (App (App (App Sop M) N) P) 
                  (App (App M P) (App N P))
| ff0_red : forall M N, sf_red1 (App (App (App Fop Fop) M) N) M
| ff1_red : forall M P Q, sf_red1 (App (App (App Fop (App Fop M))P)Q) (App (App Q Fop) M)
| ff2_red : forall M N P Q, sf_red1 (App(App(App Fop (App(App Fop M) N))P)Q) (App(App Q (App Fop M)) N) 
| fs0_red : forall M N, sf_red1 (App (App (App Fop Sop) M) N) M
| fs1_red : forall M P Q, sf_red1 (App (App (App Fop (App Sop M))P)Q) (App (App Q Sop) M)
| fs2_red : forall M N P Q, sf_red1 (App(App(App Fop (App(App Sop M) N))P)Q) (App(App Q (App Sop M)) N) 
| appl_red : forall M M' N, sf_red1 M M' -> sf_red1 (App M N) (App M' N)  
| appr_red : forall M N N', sf_red1 N N' -> sf_red1 (App M N) (App M N')  
.
Hint Constructors sf_red1: SFHintDb. 

(* Multiple reduction steps *) 

Inductive multi_step : (SF -> SF -> Prop) -> SF -> SF -> Prop :=
  | zero_red : forall red M, multi_step red M M
  | succ_red : forall (red: SF-> SF -> Prop) M N P, 
                   red M N -> multi_step red N P -> multi_step red M P
.
Hint Constructors multi_step: SFHintDb.  


Ltac inv1 prop := 
match goal with 
| H: prop (App  _ _) |- _ => inversion H; clear H; inv1 prop
| H: prop Sop |- _ => inversion H; clear H; inv1 prop
| H: prop Fop |- _ => inversion H; clear H; inv1 prop
| H: prop (Ref _) |- _ => inversion H; clear H; inv1 prop
| _ => split_all
 end.

Ltac inv red := 
match goal with 
| H: multi_step red (App _ _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red Sop _ |- _ => inversion H; clear H; inv red
| H: multi_step red Fop _ |- _ => inversion H; clear H; inv red
| H: red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: red (App _ _) _ |- _ => inversion H; clear H; inv red
| H: red Sop _ |- _ => inversion H; clear H; inv red
| H: red Fop _ |- _ => inversion H; clear H; inv red
| H: multi_step red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ (App _ _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ Sop |- _ => inversion H; clear H; inv red
| H: multi_step red _ Fop |- _ => inversion H; clear H; inv red
| H: red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: red _ (App _ _) |- _ => inversion H; clear H; inv red
| H: red _ Sop |- _ => inversion H; clear H; inv red
| H: red _ Fop |- _ => inversion H; clear H; inv red
| _ => subst; split_all 
 end.



Definition transitive red := forall (M N P: SF), red M N -> red N P -> red M P. 

Lemma transitive_red : forall red, transitive (multi_step red). 
Proof. red; induction 1; intros; simpl;  auto. apply succ_red with N; auto. Qed. 

Definition preserves_appl (red : SF -> SF -> Prop) := 
forall M N M', red M M' -> red (App M N) (App M' N).

Definition preserves_appr (red : SF -> SF -> Prop) := 
forall M N N', red N N' -> red (App M N) (App M N').

Definition preserves_app (red : SF -> SF -> Prop) := 
forall M M', red M M' -> forall N N', red N N' -> red (App M N) (App M' N').

Lemma preserves_appl_multi_step : 
forall (red: SF -> SF -> Prop), preserves_appl red -> preserves_appl (multi_step red). 
Proof.
red. intros red p M N M' r; induction r; intros; simpl;  auto with *.
eapply succ_red; [ eapply2 p |];  auto.
Qed.

Lemma preserves_appr_multi_step : 
forall (red: SF -> SF -> Prop), preserves_appr red -> preserves_appr (multi_step red). 
Proof.
red. intros red p M N M' r; induction r; intros; simpl;  auto with *.
eapply succ_red; [ eapply2 p |];  auto.
Qed.

Lemma preserves_app_multi_step : 
forall (red: SF -> SF -> Prop), 
preserves_appl red -> preserves_appr red -> 
preserves_app (multi_step red). 
Proof.
red. intros red al ar M M' rM N N' rN.  
apply transitive_red with (App M' N). 
apply preserves_appl_multi_step; auto.
apply preserves_appr_multi_step; auto.
Qed.



(* sf_red *) 

Definition sf_red := multi_step sf_red1. 

Lemma preserves_appl_sf_red : preserves_appl sf_red.
Proof. apply preserves_appl_multi_step. red; auto with *. Qed.

Lemma preserves_appr_sf_red : preserves_appr sf_red.
Proof. apply preserves_appr_multi_step. red; auto with *. Qed.

Lemma preserves_app_sf_red : preserves_app sf_red.
Proof. apply preserves_app_multi_step;  red; auto with *. Qed.


Ltac eval_sf := 
intros; unfold_op; 
repeat (eapply succ_red ; [ auto 10 with *; fail|]); try eapply zero_red.

Ltac zerotac := try eapply2 zero_red.
Ltac succtac :=
  repeat (eapply transitive_red;
  [ eapply2 succ_red ;
    match goal with
    | |- multi_step sf_red1 _ _ => idtac
    | _ => fail (*gone too far ! *)
    end
  | ])
.
Ltac aptac := eapply transitive_red; [ eapply preserves_app_sf_red |].

Ltac trtac := unfold_op; unfold sf_red; succtac; 
  match goal with
  | |- multi_step sf_red1 Fop _ => zerotac
  | |- multi_step sf_red1 (Fop @ _ @ _ @ _) _ =>
    eapply transitive_red;
    [ eapply preserves_app_sf_red ;
      [ eapply preserves_app_sf_red ;
        [ eapply preserves_app_sf_red ; [| trtac ] (* reduce the argument of △ *) 
        | ]
      | ]
     |] ;
    zerotac; (* put the "redex" back together *) 
    match goal with
    | |- multi_step sf_red1 (Fop @ ?arg @ _ @ _) _ =>
      match arg with
      | Sop  => trtac (* made progress so recurse *) 
      | Sop @ _  => trtac (* made progress so recurse *) 
      | Sop @ _ @ _ => trtac (* made progress so recurse *) 
      | Fop  => trtac (* made progress so recurse *) 
      | Fop @ _  => trtac (* made progress so recurse *) 
      | Fop @ _ @ _ => trtac (* made progress so recurse *) 
      | _ => idtac (* no progress so stop *)
      end
    | _ => idtac (* for safety ? *) 
    end 
  | |- multi_step sf_red1 (_ @ _) _ => (* not a ternary tree *) 
    eapply transitive_red; [ eapply preserves_app_sf_red ; trtac |] ; (* so reduce the function *)
    match goal with
    | |- multi_step sf_red1 (Fop @ ?arg @ _ @ _) _ =>
      match arg with
      | Sop  => trtac (* made progress so recurse *) 
      | Sop @ _  => trtac (* made progress so recurse *) 
      | Sop @ _ @ _ => trtac (* made progress so recurse *) 
      | Fop  => trtac (* made progress so recurse *) 
      | Fop @ _  => trtac (* made progress so recurse *) 
      | Fop @ _ @ _ => trtac (* made progress so recurse *) 
       | _ => idtac (* no progress so stop *)
      end
    | _ => idtac
    end
  | _ => idtac (* the head is not △ *) 
  end;
  zerotac; succtac; zerotac. 

Ltac ap2tac:=
  unfold sf_red; 
  eassumption || 
              match goal with
              | |- multi_step _ (_ @ _) _ => try aptac; [ap2tac | ap2tac | ]
              | _ => idtac
              end. 


(* compounds *)


Inductive compound : SF -> Prop := 
| s1_compound: forall M, compound (App Sop M)
| s2_compound: forall M N, compound (App (App Sop M) N)
| f1_compound: forall M, compound (App Fop M)
| f2_compound: forall M N, compound (App (App Fop M) N)
.

Hint Constructors SF compound: SFHintDb. 

Definition left_component M := 
match M with 
| App M1 M2 => M1 
| _ => Iop
end.

Definition right_component M := 
match M with 
| App M1 M2 => M2
| M => M
end.

Inductive program : SF -> Prop :=
| s0_program: program Sop
| s1_program: forall M, program M -> program (App Sop M)
| s2_program: forall M N, program M -> program N -> program (App (App Sop M) N)
| f0_program: program Fop
| f1_program: forall M, program M -> program (App Fop M)
| f2_program: forall M N, program M -> program N -> program (App (App Fop M) N)
.

Ltac program_tac :=
  cbv; repeat (eapply2 s2_program || eapply2 f2_program || eapply2 f1_program || eapply2 s1_program ||
               eapply2 s0_program || eapply2 f0_program ). 


(* Combinations *)

Inductive combination : SF -> Prop :=
| is_Sop : combination Sop
| is_Fop : combination Fop
| is_App : forall M N, combination M -> combination N -> combination (App M N)
.
Hint Constructors program combination: SFHintDb. 

Lemma programs_are_combinations: forall M, program M -> combination M.
Proof.  induction M; intro p; inversion p; subst; repeat eapply2 is_App; auto with *. Qed. 

Hint Resolve programs_are_combinations: SFHintDb.

Ltac combination_tac := repeat (apply is_App || apply is_Fop || apply is_Sop); auto_t. 

(* star abstraction *)


Fixpoint occurs x M :=
  match M with
  | Ref y => eqb x y 
  | Sop | Fop  => false
  | App M1 M2 => (occurs x M1) || (occurs x M2)
  end.

Lemma occurs_combination: forall M x,  combination M -> occurs x M = false.
Proof.  induction M; intros x c; inversion c; subst; split_all; rewrite IHM1; auto; rewrite IHM2; auto. Qed. 

Lemma occurs_program: forall M x,  program M -> occurs x M = false.
Proof. intros; eapply2 occurs_combination; eapply2 programs_are_combinations. Qed.

Hint Resolve occurs_combination occurs_program: SFHintDb. 

Fixpoint star x M :=
  match M with
  | Ref y =>  if eqb x y then Iop else (App Kop (Ref y))
  | Sop  => App Kop Sop 
  | Fop  => App Kop Fop 
  | App M1 (Ref y) => if eqb x y
                      then if occurs x M1
                           then App (App Sop (star x M1)) Iop
                           else M1
                      else  if occurs x M1
                           then App (App Sop (star x M1)) (App Kop (Ref y))
                            else App Kop (App M1 (Ref y))
  | App M1 M2 => if occurs x (App M1 M2)
                 then App (App Sop (star x M1)) (star x M2)
                 else App Kop (App M1 M2)
  end.

Notation "\" := star : sf_scope. 

Lemma star_combination: forall M x, combination M -> \x M = App Kop M. 
Proof.
  induction M; intros x c; simpl in *; auto; inversion c; clear c; subst; auto.
  match goal with
    H2: combination M2 |- _ => inversion H2; subst; auto;  rewrite ! occurs_combination; simpl; auto end.
Qed.

Lemma star_id: forall x, \x (Ref x) = Iop.
Proof. intro; unfold star, occurs; rewrite eqb_refl; auto. Qed.

Lemma star_occurs_false: forall M x, occurs x M = false -> \x M = App Kop M. 
Proof.
  induction M; intros x occ; simpl in *; auto.
  match goal with H0 : ?b = false |- _ =>   rewrite H0; auto end.
  rewrite occ. rewrite orb_false_iff in occ; elim occ. intros occ1 occ2; rewrite occ1.
  caseEq M2; intros; subst; simpl in *; auto. rewrite occ2; auto. 
Qed.


Lemma eta_red: forall M x, occurs x M = false -> \x (App M (Ref x)) = M.
Proof.  intros M x occ; unfold star at 1; fold star; rewrite eqb_refl; rewrite occ; auto. Qed.

Lemma star_occurs_true:
  forall M1 M2 x, occurs x (App M1 M2) = true -> M2 <> Ref x ->
                  \x (App M1 M2) = App (App Sop (\x M1)) (\x M2).
Proof.
  intros M1 M2 x occ ne; unfold star at 1; fold star.
  caseEq M2; intros; subst; simpl in *. 
  match goal with
    H: Ref ?s <> Ref x |- _ => assert(neb: eqb x s = false) by (eapply2 eqb_neq; congruence)
  end. 
  rewrite neb in *.   rewrite orb_false_r in *. all: rewrite occ; auto. 
Qed.



Ltac startac x :=
  repeat ( (rewrite (star_occurs_true _ _ x); [| unfold_op; unfold occurs; fold occurs; rewrite ? orb_true_r; simpl; auto with *; fail| cbv; discriminate]) || 
          (rewrite eta_red; [| ((eapply2 occurs_combination; fail) || cbv; auto with *; fail)]) ||
          rewrite star_id || 
          (rewrite (star_occurs_false _ x); [| unfold_op; unfold occurs; fold occurs; auto with *; ((rewrite ! occurs_combination; cbv; auto with *; fail) || cbv; auto with *; fail)])
         ).

Ltac starstac1 xs :=
  match xs with
  | nil => trtac
  | ?x :: ?xs1 => startac x; starstac1 xs1
  end.
Ltac starstac xs := repeat (starstac1 xs).


(* Fixpoints *) 


Definition ω := \"w" (\"f" (App (Ref "f") (App (App (Ref "w") (Ref "w")) (Ref "f")))).
Definition Y := App ω ω. 


(* 3.8 Waiting *) 

Definition wait x y := Sop @ (Sop @ (Kop @ x) @ (Kop @ y)) @ Iop.

Definition wait1 x := Sop @ (Sop @ (Kop @ Sop) @ (Sop @ (Kop @ (Sop @ (Kop @ x))) @ Kop)) @ (Kop @ Iop). 

Definition W := \"x" (\"y" (wait (Ref "x") (Ref "y"))). 


 
Lemma w_red1 : forall M N, sf_red (App (App W M) N) (wait M N).
Proof.  intros; cbv; eval_sf. Qed.    

Lemma w_red : forall M N P, sf_red (App (App (App W M) N) P) (App (App M N) P).
Proof. intros; cbv; eval_sf. Qed. 
 
(* Fixpoint Functions *) 

Definition ω2 := \"w" (\"f" (App (Ref "f") ((wait (wait (Ref "w") (Ref "w"))) (Ref "f")))).
Definition Y2 f  := wait (wait ω2 ω2) f.

Lemma Y2_program: forall f, program f -> program (Y2 f). 
Proof. intros; cbv; auto 100 with SFHintDb.  Qed.

Definition ω3 :=
  \"w" (\"f" (wait1 (App (Ref "f") (wait1 (wait (wait (Ref "w") (Ref "w")) (Ref "f")))))). 

Definition Y3 f := wait1 (wait (wait ω3 ω3) f).

Lemma Y3_program: forall f, program f -> program (Y3 f). 
Proof. intros; cbv; auto 100 with SFHintDb. Qed.

Lemma wait_red : forall f x y, sf_red (wait f x @ y) (f@x@y).
Proof. intros; cbv; trtac. Qed.


Lemma ω2_red : forall x f,  sf_red (ω2 @ x @ f) (f @ (wait (wait x x) f)).
Proof.  intros; cbv;  eval_sf; eapply preserves_app_sf_red; eval_sf. Qed.

       
Lemma Y2_red: forall f x, sf_red (Y2 f @ x) (f @ (Y2 f) @ x).
Proof.
  intros; unfold Y2 at 1; eapply transitive_red;
    [eapply2 wait_red
    | aptac; [ eapply2 wait_red | zerotac | aptac; [ eapply2  ω2_red | |]]];
    zerotac.
Qed.

Lemma Y3_red: forall f x y, sf_red (Y3 f @ x@y) (f @ (Y3 f) @ x @y).
Proof. intros; cbv; eval_sf; repeat  (eapply2 preserves_app_sf_red;  eval_sf). Qed.



(* natural numbers  *) 

Definition zero := Fop. 
Definition successor := Sop.

Definition predecessor n := App (App (App Fop n) zero) (App Kop Iop).

Lemma predecessor_zero: sf_red (predecessor zero) zero. 
Proof. unfold zero, predecessor; eval_sf. Qed. 

Lemma predecessor_successor : forall n, sf_red (predecessor (App successor n)) n.
Proof. unfold successor, predecessor; eval_sf. Qed.   

Definition isZero n := App (App (App Fop n) Kop) (App Kop (App Kop (App Kop Iop))).

Lemma isZero_zero : sf_red (isZero zero) Kop. 
Proof. unfold isZero, zero; eval_sf. Qed.

Lemma isZero_successor: forall n, sf_red (isZero (App successor n)) (App Kop Iop).
Proof. unfold isZero, successor; eval_sf. Qed. 

Definition plus_comb := Y2 (\"p" (\"n" (
App (App (App Fop (Ref "n")) Iop) (App Kop (App (App Sop 
 (App (App Sop (App Kop Sop)) (App (App Sop (App Kop Kop)) (Ref "p"))))
 (App Kop successor)))))).


Lemma plus_comb_red_zero: forall n, sf_red (App (App plus_comb zero) n) n.
Proof.
  intros; unfold plus, plus_comb, zero; trtac; aptac;
    [ eapply Y2_red
    | zerotac
    | starstac ("n" :: "p" :: nil)
    ].
Qed. 

    
Lemma plus_comb_red_successor: 
forall m n, sf_red (App (App plus_comb (App successor m)) n) 
                   (App (App plus_comb m) (App successor n)).
Proof.
  unfold plus, successor; eval_sf; aptac;
    [unfold plus_comb; eapply Y2_red
    | zerotac
    | fold plus_comb; starstac ("n" :: "p" :: nil)].
Qed. 
 

(* 10.3 Examples *)

(* size *) 

Definition size := Y2 (\"s" (\"x" 
  (App (App (App Fop (Ref "x")) (App successor zero))
       (\"x1" (\"x2" (App (App plus_comb (App (Ref "s") (Ref "x1"))) (App (Ref "s") (Ref "x2")))))))).

Lemma size_Fop : sf_red (App size Fop) (App successor zero).
Proof. 
  unfold size; eval_sf. eapply transitive_red. unfold size. eapply Y2_red. fold size. 
  starstac ("x" :: "s" :: nil). 
Qed. 

Lemma size_compound: 
forall P Q, compound (App P Q) -> 
sf_red (App size (App P Q)) (App (App plus_comb (App size P)) (App size Q)).
Proof. 
  intros P Q c; unfold size; eval_sf. eapply transitive_red. eapply Y2_red. fold size.
  starstac ("x2" :: "x1" :: "x" :: "s" :: nil).  inversion c; trtac. 
Qed. 

(* equality *) 

Definition conjunction x y := x @ y @ (Kop @ Iop).
Definition if_and_only_if x y := x @ y @ (y @ (Kop @ Iop) @ Kop).

Definition isF x := x @ (Kop @ Iop) @ (Kop @(Kop @ Iop)) @ Kop.

Lemma isF_F: sf_red (isF Fop) Kop. 
Proof. cbv; eval_sf. Qed. 

Lemma isF_S: sf_red (isF Sop) (Kop @ Iop). 
Proof. cbv; eval_sf. Qed. 


Definition eqatom x y := if_and_only_if (isF x) (isF y).

Lemma eqatom_S_S: sf_red (eqatom Sop Sop) Kop. 
Proof. cbv; eval_sf. Qed. 

Lemma eqatom_S_F: sf_red (eqatom Sop Fop) (Kop@Iop). 
Proof. cbv; eval_sf. Qed. 

Lemma eqatom_F_S: sf_red (eqatom Fop Sop) (Kop@Iop). 
Proof. cbv; eval_sf. Qed. 

Lemma eqatom_F_F: sf_red (eqatom Fop Fop) Kop. 
Proof. cbv; eval_sf. Qed. 


Definition equal :=
  Y3 (\"e" (\"x" (\"y"
                   (Fop
                      @ (Ref "x")
                      @ (Fop
                           @ (Ref "y")
                           @ (eqatom (Ref "x") (Ref "y"))
                           @ (Kop @ (Kop @ (Kop @ Iop)))
                        )
                      @ (\"x1" (\"x2"
                                 (Fop
                                    @ (Ref "y")
                                    @ (Kop @ Iop)
                                    @ (\"y1" (\"y2"
                                               ((Ref "e")
                                                  @ (Ref "x1")
                                                  @ (Ref "y1")
                                                  @ ((Ref "e")
                                                       @ (Ref "x2")
                                                       @ (Ref "y2")
                                                    )
                                                  @ (Kop @ Iop)
     )))))))))).



Lemma equal_red: 
  forall M N, combination M -> combination N -> sf_red (App (App equal M) N)
                                                       (Fop @ M @
     (Fop @ N @
      (M @ (Fop @ Fop @ (Sop @ (Fop @ Fop) @ (Fop @ Fop))) @
       (Fop @ Fop @ (Fop @ Fop @ (Sop @ (Fop @ Fop) @ (Fop @ Fop)))) @ (Fop @ Fop) @
       (N @ (Fop @ Fop @ (Sop @ (Fop @ Fop) @ (Fop @ Fop))) @
        (Fop @ Fop @ (Fop @ Fop @ (Sop @ (Fop @ Fop) @ (Fop @ Fop)))) @ (Fop @ Fop)) @
       (N @ (Fop @ Fop @ (Sop @ (Fop @ Fop) @ (Fop @ Fop))) @
        (Fop @ Fop @ (Fop @ Fop @ (Sop @ (Fop @ Fop) @ (Fop @ Fop)))) @ (Fop @ Fop) @
        (Fop @ Fop @ (Sop @ (Fop @ Fop) @ (Fop @ Fop))) @ (Fop @ Fop))) @
      (Fop @ Fop @ (Fop @ Fop @ (Fop @ Fop @ (Sop @ (Fop @ Fop) @ (Fop @ Fop)))))) @
     (Sop @
      (Fop @ Fop @ (Sop @ (Fop @ Fop @ (Fop @ N @ (Fop @ Fop @ (Sop @ (Fop @ Fop) @ (Fop @ Fop))))))) @
      (Sop @
       (Sop @ (Fop @ Fop @ Sop) @
        (Sop @ (Fop @ Fop @ (Sop @ (Fop @ Fop @ Sop))) @
         (Sop @ (Fop @ Fop @ (Sop @ (Fop @ Fop @ (Sop @ (Fop @ Fop @ Sop))))) @
          (Sop @
           (Sop @ (Fop @ Fop @ Sop) @
            (Sop @ (Fop @ Fop @ (Fop @ Fop)) @
             (Sop @ (Fop @ Fop @ Sop) @
              (Sop @ (Fop @ Fop @ (Sop @ (Fop @ Fop @ Sop))) @
               (Sop @ (Fop @ Fop @ (Sop @ (Fop @ Fop @ (Fop @ Fop)))) @ equal))))) @
           (Fop @ Fop @ (Sop @ (Fop @ Fop @ (Fop @ Fop)) @ equal)))))) @
       (Fop @ Fop @
        (Fop @ Fop @ (Fop @ Fop @ (Fop @ Fop @ (Fop @ Fop @ (Sop @ (Fop @ Fop) @ (Fop @ Fop)))))))))). 
Proof.
  unfold equal; intros. eapply transitive_red. eapply Y3_red. fold equal. 
  starstac ("y2" :: "y1" :: "x2" :: "x1" :: "y" :: "x" :: "e" :: nil).
  eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. zerotac. trtac.
  eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. zerotac.
  unfold eqatom, if_and_only_if, isF;   starstac ("y" :: "x" :: nil).
   starstac ("y" :: "x" :: nil).
  starstac ("y" :: "x" :: "e" :: nil).
Qed.


Lemma equal_comb_S_S : sf_red (App (App equal Sop) Sop) Kop.
Proof. eapply transitive_red. eapply2 equal_red. eval_sf. Qed.


Lemma equal_comb_S_F : sf_red (App (App equal Sop) Fop) (Kop@Iop).
Proof. eapply transitive_red. eapply2 equal_red. eval_sf. Qed.


Lemma equal_comb_F_S : sf_red (App (App equal Fop) Sop) (Kop@Iop).
Proof. eapply transitive_red. eapply2 equal_red. eval_sf. Qed.


Lemma equal_comb_F_F : sf_red (App (App equal Fop) Fop) Kop.
Proof. eapply transitive_red. eapply2 equal_red. eval_sf. Qed.

Lemma unequal_S_compound : 
forall M, compound M -> combination M -> sf_red (App (App equal Sop) M) (App Kop Iop). 
Proof. intros M cp cb.  eapply transitive_red.  eapply2 equal_red. inversion cp; subst; eval_sf. Qed. 

Lemma unequal_F_compound : 
forall M, compound M -> combination M -> sf_red (App (App equal Fop) M) (App Kop Iop). 
Proof. intros M cp cb.  eapply transitive_red.  eapply2 equal_red. inversion cp; subst; eval_sf. Qed. 


Lemma unequal_compound_S : 
forall M, combination M -> compound M ->  sf_red (App (App equal M) Sop) (App Kop Iop). 
Proof. intros M cp cb. eapply transitive_red.  eapply2 equal_red.  inversion cb; subst; eval_sf. Qed. 

Lemma unequal_compound_F : 
forall M, combination M -> compound M ->  sf_red (App (App equal M) Fop) (App Kop Iop). 
Proof. intros M cp cb. eapply transitive_red.  eapply2 equal_red.  inversion cb; subst; eval_sf. Qed. 

Lemma equal_compounds : 
forall M N, compound M -> compound N -> combination M -> combination N -> 
              sf_red (App (App equal M) N)
(App (App (App (App equal (left_component M)) (left_component N))
(App (App equal (right_component M)) (right_component N)))
 (App Kop Iop)). 
Proof.
  intros M N cM cN; intros.  eapply transitive_red.  eapply2 equal_red.
  inversion cM; inversion cN; subst; eval_sf. Qed.


Ltac equal_tac :=
  match goal with
  | |-  sf_red (equal @ (_@_) @ (_@_)) _ =>
    eapply transitive_red;
    [eapply2 equal_compounds
    | simpl; aptac;  [aptac; equal_tac | |]]; zerotac; equal_tac
  | |-  sf_red (equal @ Sop @ Sop) _ => eapply2 equal_comb_S_S; equal_tac
  | |-  sf_red (equal @ Sop @ Fop) _ => eapply2 equal_comb_S_F; equal_tac
  | |-  sf_red (equal @ Fop @ Sop) _ => eapply2 equal_comb_F_S; equal_tac
  | |-  sf_red (equal @ Fop @ Fop) _ => eapply2 equal_comb_F_F; equal_tac
  | |-  sf_red (equal @ Sop @ (_@_)) _ => eapply2 unequal_S_compound; equal_tac
  | |-  sf_red (equal @ (_@_) @Sop) _ => eapply2 unequal_compound_S; equal_tac
  | |-  sf_red (equal @ Fop @ (_@_)) _ => eapply2 unequal_F_compound; equal_tac
  | |-  sf_red (equal @ (_@_) @Fop) _ => eapply2 unequal_compound_F; equal_tac
  | _ => split_all; trtac
  end.

Theorem equal_sf_programs: forall M,  program M -> sf_red (equal @ M @ M) Kop. 
Proof.  intros M prM; induction prM; intros; equal_tac. Qed. 


Theorem unequal_sf_programs:
  forall M,  program M -> forall N, program N -> M<> N -> sf_red (equal @ M @ N) (Kop @ Iop). 
Proof.
  intros M prM; induction prM; intros P prP neq; inversion prP; intros; subst; try congruence;  equal_tac;
    try (eapply2 IHprM; congruence); 
    (assert(d: M=M0 \/ M<>M0) by repeat decide equality; inversion d; subst;   
      [ aptac; [ aptac; [ eapply2 equal_sf_programs | eapply2 IHprM2; congruence |] | |]
       |aptac; [ aptac; [ eapply2 IHprM1 | |] | |]] ; zerotac; trtac).
Qed.

(* tagging *)

Definition tag t f := Sop @ (Sop @ (Kop @ Kop) @ f) @ t.


Definition get_tag x := Fop @ x @ Fop @ (Kop @ Iop).

Lemma tag_red: forall t f x, sf_red (tag t f @ x) (f@x).
Proof. intros; cbv; eval_sf. Qed.

Lemma get_tag_red: forall t f, sf_red (get_tag (tag t f)) t. 
Proof. intros; cbv; eval_sf. Qed. 


Lemma get_tag_program: forall x, program x -> exists y, sf_red (get_tag x) y /\ program y.
Proof.
  intros x pr; induction pr; unfold get_tag; split_all;
    [ exist Fop; eapply2 succ_red
    | exist M; unfold_op; trtac
    | exist N; unfold_op; trtac 
    | exist Fop; eapply2 succ_red
    | exist M; unfold_op; trtac 
    | exist N; unfold_op; trtac
      ]. 
Qed.

(* 10.4 Translation from Tree Calculus *) 

Definition kernel :=
  tag
    Kop
    (\"x"
       (tag
          (Sop @ Sop @ (Kop @ (Ref "x")))
          (\"y"
             (tag
                (Kop @ (Sop @ (Sop @ Iop @ (Kop @ (Ref "x")))  @ (Kop @ (Ref "y"))))
                (get_tag (Ref "x") @ (Ref "y"))
    )))). 

(* 
Compute (term_size kernel). 
 *)

(* 
Definition RefSF := Ref. 
Definition AppSF := App.
Definition programSF := program.
Definition combinationSF := combination.
Ltac combinationSF_tac := Divide_and_Conquer_in_SF_Calculus.combination_tac.  

*) 

Definition meaningful_translation_tree_to_sf (f: Rewriting_partI.Tree -> SF) := 
  (forall M N, t_red1 M N -> sf_red (f M) (f N)) /\ (* strong version *) 
  (forall M N, f(Rewriting_partI.App M N) = (f M) @ (f N)) /\  (* applications *) 
  (forall i, f (Rewriting_partI.Ref i) = Ref i) /\              (* variables *) 
  (forall M, Rewriting_partI.program M -> exists M', sf_red (f M) M' /\ program M').


Fixpoint tree_to_sf M :=
  match M with
    Rewriting_partI.Ref i => Ref i
  | Node => kernel
  | Rewriting_partI.App M1 M2 =>  (tree_to_sf M1) @ (tree_to_sf M2)
  end.


Lemma tree_to_sf_preserves_combinations:
  forall M, Rewriting_partI.combination M -> combination (tree_to_sf M). 
Proof.   induction M; intro c; inversion c; subst; simpl; combination_tac. Qed. 

Lemma tree_to_sf_preserves_programs:
  forall M, Rewriting_partI.program M -> combination (tree_to_sf M). 
Proof.
  intros; eapply2 tree_to_sf_preserves_combinations;
    eapply2 Rewriting_partI.programs_are_combinations.
Qed.



Ltac kernel_tac :=   intros; unfold kernel; aptac; [ aptac; [ eapply2 tag_red | | ] | | ]; zerotac;
    unfold tag, get_tag; starstac ("y" :: "x" :: nil). 


Lemma tree_to_sf_tag:
  forall M, Rewriting_partI.program M ->
            exists t x, sf_red (tree_to_sf M) (tag t x) /\ program t /\ program x /\ 
                         (t = Kop \/ exists t1, t = Sop @ Sop @ (Kop @ t1) \/ t = Kop @ t1). 
Proof.
  cut (forall k M, Rewriting_partI.term_size M <k -> Rewriting_partI.program M ->
            exists t x, sf_red (tree_to_sf M) (tag t x) /\ program t /\ program x /\ 
                         (t = Kop \/ exists t1, t = Sop @ Sop @ (Kop @ t1) \/ t = Kop @ t1)); 
  [intro c; intros; eapply2 c |];
  induction k; intros M sz prM; [ lia | inversion prM as [ | M0 | ]; clear prM; subst; simpl in sz];simpl; 
    [ exists Kop,
        (\"x"
          (tag
             (Sop @ Sop @ (Kop @ (Ref "x")))
             (\"y"
               (tag
                  (Kop @ (Sop @ ((Sop @ Iop) @ (Kop @ (Ref "x")))  @ (Kop @ (Ref "y"))))
                  (get_tag (Ref "x") @ (Ref "y"))
        )))); repeat split; [ zerotac| program_tac | program_tac | auto]
                              
    | elim(IHk M0); auto_t; [ | lia]; 
      intros t0 ex;  elim ex; clear ex; intros f0 (?&?&?&[?|?]); subst; 
      (repeat eexists;
       [eapply transitive_red;
        [ unfold kernel; eapply2 tag_red 
        | unfold tag, get_tag; eapply transitive_red;
          [starstac ("y" :: "x" :: nil) 
          | eapply transitive_red; [ap2tac; zerotac | unfold tag;  trtac]]]
       | program_tac
       | program_tac
       | eauto])

    | elim (IHk N); auto_t; try lia; intros t2 ex; elim ex; clear ex; intro f2; split_all;
      elim (IHk M0); auto_t; try lia; intros t1 ex; elim ex; clear ex; intros f1 (?&?&?&[e1 | [x [?|?]]]);
      subst; split_all; inv1 program; subst;
      (repeat eexists;
       [ unfold kernel; aptac;
         [ eapply2 tag_red
         | eassumption
         | unfold tag, get_tag; eapply transitive_red;
           [ starstac ("y" :: "x" :: nil)
            |eapply transitive_red;
             [ ap2tac; zerotac
             | unfold tag; trtac]]]
       | program_tac
       | program_tac
       | eauto]; auto)
    ].
Qed.





Theorem meaningful_translation_from_tree_to_sf:  meaningful_translation_tree_to_sf tree_to_sf.
Proof.
  unfold meaningful_translation_tree_to_sf. repeat split.
  (* 2 *)
  intros M N r; induction r; split_all.
  (* 6 *)
  1-3: kernel_tac.
  1-2: eapply2 preserves_app_sf_red;   zerotac.
  (* 1 *)
  intros M pr;   elim(tree_to_sf_tag M); split_all; exist (tag x x0); program_tac.
Qed.



(* 10.5 Translation to Tree Calculus *)


Definition meaningful_translation_sf_to_tree (f: SF -> Tree) :=
  (forall M N, sf_red1 M N -> t_red (f M) (f N)) /\ (* strong version *) 
  (forall M N, f(App M N) = Rewriting_partI.App (f M) (f N)) /\  (* applications *) 
  (forall i, f (Ref i) = Rewriting_partI.Ref i) /\              (* variables *) 
  (forall M, program M -> exists M', t_red (f M) M' /\ Rewriting_partI.program M').



(* 
Partially applied operators  t are tagged by a t1 such that t1 y z has the effect of F t y z. 
Some care is required to ensure that all partially applid operators have normal forms 
without having everything grow too much.  
 *)

Require Import Reflective.Rewriting_partI.

Definition d2 y x := △ @ (△ @ x) @ y.
Definition d3 y x := d2 (d2 (K@△) (d2 (K@△) x)) y.


Definition mypair x y := d2 (d2 Id (K@x)) (K@y). 
Definition mythree w x y := d2 (d2 Id (d2 (K@w) (K@x))) (K@y). 

Definition ternary_op_aux_aux f := 
  Eval cbv in
   substitute ( \"op"
       (\"x"
          (tag (△ @ (△ @ (tag K (Ref "op")) @ (Ref "x")))
               (\"y"
                  (tag
                     (K@ (mythree (tag K (Ref "op")) (Ref "x") (Ref "y")))
                     (Ref "f" @ (Ref "x") @ (Ref "y"))
    ))))) "f" f.

Definition ternary_op_aux f := Y2 (ternary_op_aux_aux f). 
 
Definition ternary_op f := tag K (ternary_op_aux f).


Lemma ternary_op_red: forall f x y z, t_red (ternary_op f @ x @ y@ z) (f @ x @ y @ z).
Proof.
  intros; unfold ternary_op, ternary_op_aux; aptac;
    [ aptac; [ eapply2 tag_apply | zerotac | aptac; [ eapply2 Y2_red | |] ] | |]; zerotac;
      unfold ternary_op_aux_aux at 1;  trtac. 
Qed.


Definition S_t := ternary_op Sop.

Definition F_t := ternary_op getTag. 

  
Lemma S_t_program: program S_t.
Proof. program_tac. Qed.

Lemma F_t_program: program F_t.
Proof. program_tac. Qed.


Lemma getTag_Y2: forall f, t_red (getTag @ (Y2 f)) Id. 
Proof. intros; cbv; trtac. Qed.

Lemma S_t_red: forall x y z, t_red (S_t @ x @y@z) (x@z@(y@z)).
Proof.  intros; eapply transitive_red; [ eapply2 ternary_op_red; cbv; repeat eapply2 is_App |  trtac]. Qed. 
  

Lemma F_t_op_red: forall f y z,  t_red (F_t @ (ternary_op f) @ y @ z) y. 
Proof.
  intros; eapply transitive_red; [ eapply2 ternary_op_red; cbv; repeat eapply2 is_App |];
  unfold ternary_op; aptac; [ aptac; [ eapply2 getTag_tag | |] | |]; zerotac; trtac.
Qed. 

Lemma F_t_op1_red:
  forall f x y z,  t_red (F_t @ (ternary_op f @ x) @ y @ z) (z@ (ternary_op f) @ x). 
Proof.
  intros; unfold F_t;  eapply transitive_red;
    [ eapply2 ternary_op_red
    | aptac;
      [ aptac;
        [ aptac;
          [ zerotac
          | eapply2 tag_apply
          | aptac;
            [ zerotac
            | eapply2 Y2_red
            | aptac;
              [ zerotac
              | unfold ternary_op_aux_aux at 1; trtac
              | unfold getTag; trtac]]]
        | zerotac
        | trtac]
      | zerotac
      | trtac]].
Qed. 




Lemma F_t_op2_red:
  forall f w x y z, t_red (F_t @ (ternary_op f @ w @ x) @ y @ z) (z @ (ternary_op f @ w) @ x).
Proof.
  intros; unfold F_t;  eapply transitive_red;
    [ eapply2 ternary_op_red
    | aptac;
      [ aptac;
        [ aptac;
          [ zerotac
          | aptac;
            [ eapply2 tag_apply
            | zerotac
            | aptac;
              [ eapply2 Y2_red
              | zerotac
              | unfold ternary_op_aux_aux at 1; trtac]]
          | unfold getTag; trtac]
        | zerotac
        | trtac]
      | zerotac
      | replace (△ @ (△ @ (△ @ △)) @ (△ @ (△ @ Y2 (ternary_op_aux_aux f)) @ (△ @ △ @ (△ @ △)))) with 
            (ternary_op f) by auto; trtac]].
 Qed. 



Fixpoint sf_to_tree M :=
  match M with
    Divide_and_Conquer_in_SF_Calculus.Ref i => Ref i
  | Divide_and_Conquer_in_SF_Calculus.Sop => S_t
  | Divide_and_Conquer_in_SF_Calculus.Fop => F_t
  | Divide_and_Conquer_in_SF_Calculus.App M1 M2 => App (sf_to_tree M1) (sf_to_tree M2)
  end.


Lemma sf_to_tree_preserves_combinations:
  forall M, Divide_and_Conquer_in_SF_Calculus.combination M -> combination (sf_to_tree M). 
Proof.  induction M; intro c; inversion c. 1,2: cbv; auto 1000 with *. repeat eapply2 is_App. Qed.

Ltac sf2tree_tac :=  
  unfold tag in *; repeat eexists;
    [ eapply transitive_red;
      [ ap2tac; zerotac
      | eapply transitive_red;
        [unfold F_t; trtac 
        | aptac;
          [ eapply2 tag_apply
          | zerotac
          | aptac;
            [ eapply2 Y2_red
            | zerotac
            | unfold ternary_op_aux_aux; fold sf_to_tree; eapply transitive_red;
              [ trtac
              | eapply transitive_red; 
                [ ap2tac; zerotac
                | eapply transitive_red; [ap2tac; zerotac | trtac]]]]]]]
    |  inv1 program; subst; program_tac
    |  right; eauto
    ].

Ltac getTag_tac t f:=
  assert(t_red (getTag @ (△ @ (△ @ t) @ (△ @ (△ @ f) @ (△ @ △ @ (△ @ △))))) t) by eapply2 getTag_tag.
 

Lemma sf_to_tree_creates_tags:
  forall M, Divide_and_Conquer_in_SF_Calculus.program M -> exists t f, t_red (sf_to_tree M) (tag t f) /\ program (tag t f)  /\ (t = K \/ exists t1, t = K @ t1 \/ t = △ @ t1) . 
Proof.
  cut (forall k M, Divide_and_Conquer_in_SF_Calculus.term_size M < k ->
                   Divide_and_Conquer_in_SF_Calculus.program M ->
                   exists t f, t_red (sf_to_tree M) (tag t f) /\
                               program (tag t f) /\ (t = K \/ exists t1, t = K @ t1 \/ t = △ @ t1));
    [ intro c; intros; eapply2 c
    |  induction k; intros M s p; [ lia |]];
    inversion p as [| | | | | M0 N]; subst. 
  (* 6 *)
  repeat eexists; [unfold sf_to_tree, S_t; zerotac |  program_tac | tauto]. 
  (* 5 *)
  elim (IHk M0); split_all; repeat eexists;   
     [ ap2tac; zerotac; eapply transitive_red;
      [ unfold S_t; trtac
      | eapply transitive_red;
        [ eapply2 tag_apply
        | eapply transitive_red; 
           [ eapply2 Y2_red  
           | unfold ternary_op_aux_aux at 1; trtac]]]
    | unfold tag in *; inv1 program;   subst; program_tac
    | right; eauto
    |simpl in *; lia
    ].  
  (* 4 *)
  elim (IHk M0); split_all; elim (IHk N); split_all; repeat eexists;   
    [eapply transitive_red;
     [ ap2tac; zerotac
     | eapply transitive_red; 
       [unfold S_t; trtac
       | aptac;
         [ eapply2 tag_apply
         | zerotac
         | aptac;
           [ eapply2 Y2_red
           | zerotac
           | unfold ternary_op_aux_aux at 1; trtac]]]]
    | unfold tag in *; inv1 program;   subst; program_tac
    | right; eauto
    | | |]; simpl in *; lia. 
  (* 3 *)
  repeat eexists; [unfold sf_to_tree, F_t; zerotac |  program_tac | tauto]. 
  (* 2 *)
  elim (IHk M0); split_all; [  
   getTag_tac x x0 | simpl in *; lia]; 
    unfold tag in *; repeat eexists;    
    [ap2tac; zerotac;  eapply transitive_red;
      [ unfold F_t; trtac
      | eapply transitive_red;
        [ eapply2 tag_apply
        | eapply transitive_red;
          [ eapply2 Y2_red
          | eapply transitive_red; 
            [ unfold ternary_op_aux_aux at 1; trtac
            | unfold tag ; eapply transitive_red ; [ap2tac; zerotac | trtac]
      ]]]]
     |  unfold tag in *; inv1 program;  subst; program_tac
     | right; eauto].
  (* 1 *)
  elim (IHk M0); auto_t; try (simpl in *; lia); intros t0 ex; elim ex; clear ex;
    intros f0 (?&?&[? | ex0 ]); subst;
      elim (IHk N); auto_t; try (simpl in *; lia); intros t1 ex; elim ex; clear ex;
        intros f1 (?&?&[? | ex1 ]); subst;
   getTag_tac K f0; 
   [ sf2tree_tac
   | inversion ex1 as [t2 [ ?|?]]; subst; getTag_tac (K@t2) f0; getTag_tac (K@t2) f1; sf2tree_tac
   | inversion ex0 as [t2 [ ?|?]]; subst; getTag_tac (K@t2) f0; getTag_tac (△@ t2) f0; sf2tree_tac
   | getTag_tac t1 f0; getTag_tac t0 f0; inversion ex0 as [t2 [ ?|?]]; subst; sf2tree_tac].
   
 Qed.


Theorem meaningful_translation_from_sf_to_tree:
  meaningful_translation_sf_to_tree sf_to_tree. 
Proof.
  repeat split; 
 [ intros M N r; induction r; split_all;  
  [ eapply2 S_t_red
  | eapply2 F_t_op_red 
  | eapply2 F_t_op1_red
  | eapply2 F_t_op2_red; combination_tac
  | eapply2 F_t_op_red
  | eapply2 F_t_op1_red
  | eapply2 F_t_op2_red; combination_tac
  | | ]; eapply2 preserves_app_t_red; zerotac
 |  intros M p;   elim (sf_to_tree_creates_tags M); split_all; eauto
 ].
Qed.

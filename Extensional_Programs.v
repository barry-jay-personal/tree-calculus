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
(*               Chapter 4: Extensional Programs                      *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith Lia Bool List String.
Require Import Reflective.Tree_Calculus.

Set Default Proof Using "Type".


(* 4.1 Combinations versus Terms *)

Inductive combination : Tree0 -> Prop :=
| is_Node : combination △
| is_App : forall M N, combination M -> combination N -> combination (M@ N)
.
Hint Constructors combination : TreeHintDb.

Ltac combination_tac := inv1 combination; subst; repeat (apply is_App || apply is_Node). 

Lemma programs_are_combinations: forall M, program M -> combination M.
Proof.
  induction M; intro pr; inversion pr; auto_t; subst;  eapply is_App; auto; 
  apply IHM1; inversion pr; now apply pr_stem. 
Qed. 

Hint Resolve programs_are_combinations : TreeHintDb.

Fixpoint substitute M x N :=
  match M with
  | Ref y => if eqb x y then N else Ref y
  | △ => △
  | App M1 M2 => App (substitute M1 x N) (substitute M2 x N)
end. 



Lemma substitute_combination: forall M x N, combination M -> substitute M x N = M.
Proof. induction M;intros x N c; inversion c; subst; simpl; auto; rewrite IHM1; rewrite ? IHM2; auto. Qed. 


Ltac subst_tac := unfold_op;  repeat (unfold substitute; fold substitute;  unfold eqb, Ascii.eqb, Bool.eqb).


(* 4.2 Variable Binding *) 
       
Fixpoint bracket x M := 
match M with 
| Ref y =>  if eqb x y then I else (K@ (Ref y))
| △ => K@ △ 
| App M1 M2 => d (bracket x M2) @ (bracket x M1)
end
.

(* never used, just for show *) 
Theorem bracket_beta: forall M x N, (bracket x M) @ N === substitute M x N.
Proof.  induction M; intros; unfold eq_q; simpl; [ caseEq (x=?s) | | 
        rewrite <- IHM1; rewrite <- IHM2]; tree_eq. Qed.



Fixpoint occurs x M :=
  match M with
  | Ref y => eqb x y 
  | △ => false
  | M1 @ M2 => (occurs x M1) || (occurs x M2)
  end.

Lemma occurs_combination: forall M x,  combination M -> occurs x M = false.
Proof. induction M; intros x c; inversion c; subst; simpl; auto; rewrite IHM1; rewrite ? IHM2; auto. Qed. 


Lemma substitute_occurs_false: forall M x N, occurs x M = false -> substitute M x N = M. 
Proof.
  induction M; intros x N occ; simpl in *; auto;
    [ rewrite occ; auto
    | rewrite orb_false_iff in *; inversion occ; rewrite IHM1; rewrite ? IHM2; auto]. 
Qed.


Fixpoint star x M :=
  match M with
  | Ref y =>  if eqb x y then I else (K@ (Ref y))
  | △ => K@ △ 
  | App M1 (Ref y) => if eqb x y
                      then if occurs x M1
                           then d I @ (star x M1)
                           else M1
                      else  if occurs x M1
                           then d (K@ (Ref y)) @ (star x M1)
                            else K@ (M1 @ (Ref y))
  | App M1 M2 => if occurs x (M1 @ M2)
                 then Node @ (Node @ (star x M2)) @ (star x M1)
                 else K@ (M1 @ M2)
  end. 

Notation "\" := star : tree_scope.

Lemma star_id: forall x, \x (Ref x) = I.
Proof. intro; unfold star, occurs; rewrite eqb_refl; auto. Qed.


Lemma eta_red: forall M x, occurs x M = false -> \x (M@ (Ref x)) = M.
Proof. intros M x occ; unfold star; fold star; rewrite eqb_refl; rewrite occ; auto. Qed.


Lemma star_occurs_false: forall M x, occurs x M = false -> \x M = K@ M. 
Proof.
  induction M; intros x occ; auto; 
    [ simpl in *;  rewrite occ; auto
    | unfold star; fold star; rewrite occ; simpl in occ;
    rewrite orb_false_iff in occ;  elim occ; intros occ1 occ2;  
    caseEq M2; intros; subst; simpl in *; auto;  rewrite ? occ1; rewrite occ2; auto]. 
Qed.


Lemma star_occurs_true:
  forall M1 M2 x, occurs x (M1@ M2) = true -> M2 <> Ref x ->
                  \x (M1@ M2) = △@ (△@ (\x M2))@ (\x M1).
Proof.
  intros M1 M2 x occ ne; unfold star at 1; fold star;
    rewrite occ; simpl in occ; rewrite orb_true_iff in occ; elim occ; intro occ1; 
      caseEq M2; intros; subst; auto; 
  match goal with
  | H: Ref ?s1 <> Ref ?x1 |- _ => assert(ne1: x1=?s1 = false) by (apply eqb_neq; congruence)
  end; 
  simpl in *; rewrite ne1 in *; auto;  rewrite ? occ1; auto; discriminate.   
Qed.


Lemma star_occurs_twice:
  forall M1 x, occurs x M1 = true -> \x (M1@ (Ref x)) = △@ (△@ I)@ (\x M1).
Proof. intros M1 x occ; unfold star; fold star; rewrite eqb_refl; rewrite occ; auto. Qed.

Ltac occurstac :=
  unfold_op; unfold occurs; fold occurs; rewrite ? orb_true_r;
  rewrite ? occurs_combination; auto; cbv; auto 1000 with *; fail. 

Ltac startac_true x :=
  rewrite (star_occurs_true _ _ x);
  [
  | occurstac
  | ( (intro; subst; inv1 combination; fail) || (cbv; discriminate))
  ]. 

Ltac startac_twice x := rewrite (star_occurs_twice _ x); [| occurstac ]. 
Ltac startac_false x :=  rewrite (star_occurs_false _ x); [ | occurstac].
Ltac startac_eta x := rewrite eta_red; [| occurstac ].
Ltac startac x :=
  repeat (startac_false x || startac_true x || startac_twice x || startac_eta x || rewrite star_id).
Ltac starstac1 xs :=
  match xs with
  | nil => eqtac
  | ?x :: ?xs1 => startac x; starstac1 xs1
  end.
Ltac starstac xs := repeat (starstac1 xs).


Lemma star_app_red : forall M N x P, \x (M@N) @ P === \x M @ P @ (\x N @ P).
Proof.
  intros M N x P; unfold star at 1; fold star; caseEq N; intros; unfold d, eq_q; subst; [ 
  
  caseEq (x=? s); intro b; [  
        caseEq (occurs x M); intros; simpl; qtac b; qtac star_occurs_false;  eqtac
      | caseEq (occurs x M); intros; eqtac; [ 
          qtac (star_occurs_false (Ref s) x)
        | qtac (star_occurs_false M x); simpl; qtac b
        ]
      ]
      |   caseEq (occurs x (M@△)); intros; eqtac; qtac star_occurs_false;
          simpl in *; rewrite orb_false_r in *; auto
                                                  
      | caseEq (occurs x (M@(t@t0))); intro occ; eqtac;
        simpl in occ; rewrite  orb_false_iff in occ; elim occ;  intros; qtac star_occurs_false 
      ]. 
Qed.


Lemma star_to_bracket : forall M N x, \x M @ N === bracket x M @ N .
Proof.  induction M; intros;  qtac star_app_red; eqtac; qtac IHM1; qtac IHM2; tree_eq. Qed. 

(* never used, just for show *)

Theorem star_beta: forall M x N, App (\x M) N === substitute M x N.
Proof. intros; unfold eq_q; rewrite star_to_bracket; now apply bracket_beta. Qed. 



(* 4.3 Fixpoints *) 


Definition ω := Eval cbv in \"w" (\"f" ((Ref "f")@ ((Ref "w")@ (Ref "w")@ (Ref "f")))).
Definition Y :=  ω @ ω. 


Lemma y_red: forall f, Y@f === (f@ (Y@f)).
Proof.  intros; unfold Y, eq_q; unfold ω at 1; eqtac; auto. Qed.


(* 4.4 Waiting *) 



Definition W_0 := \"x" (\"y" (\"z" ((Ref "x") @ (Ref "y") @ (Ref "z")))).
Definition W := \"x" (\"y" (bracket "z" ((Ref "x") @ (Ref "y") @ (Ref "z")))).


Definition wait M N := d I @ (d (K@ N) @ (K@ M)).
Definition wait1 M :=
  d
    (d (K @ (K @ M))
       @ (d (d K @ (K @ △)) @ (K @ △))
    )
    @ (K @ (d (△ @ K @ K))).

Lemma wait_red: forall M N P, (wait M N) @ P === M@N@P.
Proof. tree_eq. Qed. 

Lemma wait1_red: forall M N, (wait1 M) @ N  === wait M N. 
Proof. tree_eq. Qed. 

Lemma w_red1 : forall M N, W@M@N === (wait M N).
Proof.   tree_eq. Qed.    

Lemma w_red : forall M N P, W@M@N@P === (M@N@P).
Proof.  tree_eq. Qed.


(* 4.5: Fixpoint Functions *)

Definition self_apply := Eval cbv in (\"x" (Ref "x" @ (Ref "x"))). 

Definition Z f := wait self_apply (d (wait1 self_apply) @ (K@f)). 


Lemma Z_program: forall f, program f -> program (Z f). 
Proof. intros; program_tac. Qed.


Lemma Z_red : forall f x, Z f @ x === f@ (Z f) @ x.
Proof. tree_eq. Qed.


Definition swap f := d (K @ f) @ (d (d K @ (K @ △)) @ (K @ △)).

Lemma swap_red: forall f x y, swap f @ x @ y === f @ y @ x.
Proof. tree_eq. Qed.

Definition Y2 f := Z (swap f).

Theorem fixpoint_function : forall f x, Y2 f @ x === f @ x @ Y2 f.
Proof. intros; unfold Y2; qtac Z_red; qtac swap_red. Qed.

Definition Y2_red := fixpoint_function.

Lemma Y2_program : forall f, program f -> program (Y2 f).
Proof. intros; program_tac. Qed. 

(* 4.6: Arithmetic *)
 

Definition plus :=
  Y2 (\"m"
           (\"p"
                 (△@ (Ref "m") @ I @
                   (K@ (\"m1" (\"n" (K@ ((Ref "p") @ (Ref "m1") @ (Ref "n"))))))
           ))).


Lemma plus_zero: forall n, plus @ zero @ n === n.
Proof. tree_eq. Qed.


Lemma plus_successor:
  forall m n,  plus @ (successor @ m) @ n === successor @ (plus @ m @ n).
Proof. tree_eq. Qed.



(* mu-recursive functions *) 

Inductive recfun : Set :=
| Zero_fn : recfun
| Succ_fn : recfun 
| Proj_fn: nat -> nat -> recfun 
| Compose_fn : recfun -> list recfun -> recfun
| Primrec : recfun -> recfun -> recfun
| Minrec : recfun -> recfun
.

Fixpoint rf_size f :=
  match f with
| Zero_fn => 1 
| Succ_fn => 1 
| Proj_fn _ _ => 1 
| Compose_fn g hs => fold_left (fun n h => n + rf_size h) hs (S (rf_size g))
| Primrec g h => rf_size g + rf_size h 
| Minrec g => S (rf_size g)
end.
    
Lemma rf_size_positive: forall f, rf_size f > 0.
Proof.
  induction f; simpl; auto; try lia. 
  assert(p: forall l n, fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l n >= n ). clear. 
  induction l; intro n; simpl; auto; try lia. 
  match goal with | r: recfun |- _ =>  elim(IHl (n + rf_size r)); auto; lia end. 
  assert(fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l (S (rf_size f)) >= S (rf_size f))
    by apply p;  lia.
Qed. 


Definition zero_t := △ .
Definition succ_t := K.



Definition first_c := \"x" (△ @ (Ref "x") @ △ @ K).
Definition second_c := \"x" (△ @ (Ref "x") @ △ @ KI).
Fixpoint proj i :=
  match i with
  | 0 => first_c
  | S i => △ @ (△ @ second_c) @ (K@(proj i))
  end.


Definition rf_primrec_aux := (* use Ref's for g and h to avoid capture by \ *) 
  Eval cbv in
    \"xs"
     (\"f"
       (△
          @ (Ref "xs")
          @ zero_t
          @ (\"x0"
              (\"xs1"
                (△
                   @ (Ref "x0")
                   @ (Ref "g"@ (Ref "xs1"))
                   @ (K@
                       (\"x1"
                         (Ref "h"
                              @ (△
                                   @ ((Ref "f") @ (△ @ (Ref "x1") @ (Ref "xs1")))
                                   @ (△ @ (Ref "x1") @ (Ref "xs1"))
     ))))))))).

Set Printing Depth 1000.

Print rf_primrec_aux.

Definition rf_primrec g h :=
  Y2 (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ △ @ △)) @ △)) @ (△ @ △ @ (△ @ △)))) @
(△ @ △ @
 (△ @
  (△ @
   (△ @
    (△ @
     (△ @
      (△ @
       (△ @
        (△ @
         (△ @
          (△ @
           (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ △)))) @
            (△ @
             (△ @
              (△ @
               (△ @
                (△ @
                 (△ @
                  (△ @ (△ @ (△ @ △ @ (△ @ △ @ △))) @
                   (△ @
                    (△ @
                     (△ @
                      (△ @
                       (△ @ (△ @ (△ @ △ @ (△ @ △ @ △))) @
                        (△ @
                         (△ @
                          (△ @
                           (△ @
                            (△ @
                             (△ @
                              (△ @ △ @
                               (△ @
                                (△ @
                                 (△ @
                                  (△ @
                                   (△ @ (△ @ (△ @ △ @ △)) @
                                    (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @
                                  (△ @ △ @ △))) @ (△ @ △ @ △)))) @
                             (△ @
                              (△ @
                               (△ @
                                (△ @
                                 (△ @
                                  (△ @
                                   (△ @ (△ @ (△ @ △ @ (△ @ △ @ △))) @
                                    (△ @
                                     (△ @
                                      (△ @
                                       (△ @
                                        (△ @ (△ @ (△ @ △ @ (△ @ △ @ △))) @
                                         (△ @
                                          (△ @
                                           (△ @
                                            (△ @
                                             (△ @
                                              (△ @
                                               (△ @ △ @
                                                (△ @
                                                 (△ @
                                                  (△ @
                                                   (△ @
                                                    (△ @ (△ @ (△ @ △ @ △)) @
                                                     (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ △))) @
                                                      (△ @ △ @ △)))) @ 
                                                   (△ @ △ @ △))) @ (△ @ △ @ △)))) @
                                              (△ @
                                               (△ @
                                                (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ (△ @ △)))) @
                                                 (△ @ △ @ △))) @ (△ @ △ @ △)))) @ 
                                            (△ @ △ @ △))) @ (△ @ △ @ △)))) @ 
                                       (△ @ △ @ △))) @ (△ @ △ @ △)))) @
                                  (△ @ △ @ (△ @ (△ @ (△ @ △ @ (△ @ △ @ △))))))) @ 
                                (△ @ △ @ △))) @ (△ @ △ @ △)))) @ (△ @ △ @ △))) @ 
                         (△ @ △ @ △)))) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @
                 (△ @ △ @ (△ @ (△ @ (△ @ △ @ (△ @ △ @ h))))))) @ 
               (△ @ △ @ △))) @ (△ @ △ @ △)))) @ (△ @ △ @ △))) @ (△ @ △ @ △))) @ 
      (△ @ △ @ (△ @ △)))) @
    (△ @ △ @
     (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ △) @ (△ @ △ @ (△ @ △)))) @ (△ @ △ @ (△ @ (△ @ g)))))))))))
     ).




Lemma rf_primrec_combination: forall g h, combination g -> combination h -> combination (rf_primrec g h).
Proof.   intros; cbv; now combination_tac. Qed.

Definition minrec_aux  :=
  Eval cbv in
    \"args"
         (\"f"
            (Ref "isLeaf"
               @ (Ref "g" @ (Ref "args"))
               @ (first (Ref "args"))
               @ (△
                    @ (Ref "args")
                    @ zero_t
                    @ (\"arg0" (\"xs1" ((Ref "f") @ (△ @ (K@ (Ref "arg0")) @ (Ref "xs1")))))
                    ))).

Print minrec_aux.

Definition minrec g :=
△ @
(△ @
 (△ @
  (△ @
   (△ @ (△ @ (△ @ (△ @ (△ @ △ @ (△ @ △))) @ (△ @ (△ @ (△ @ △ @ △)) @ △))) @
    (△ @ (△ @ g) @ (△ @ △ @ isLeaf)))) @ (△ @ △ @ (△ @ △)))) @
(△ @
 (△ @
  (△ @
   (△ @
    (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ △ @ △)) @ △)) @ (△ @ △ @ (△ @ △)))) @
     (△ @ △ @
      (△ @
       (△ @
        (△ @
         (△ @
          (△ @ △ @
           (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ △))) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @
         (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ (△ @ △)))) @ (△ @ △ @ △))) @
          (△ @ △ @ △)))))))) @ (△ @ △ @ △))) @ (△ @ △ @ △))
.


Definition list_to_p_list gs :=  \"x" (fold_right (fun g f => △ @ (g @ (Ref "x")) @ f) △ gs). 

Lemma list_to_p_list_cons:
  forall g gs x,  combination g ->
                  list_to_p_list (g::gs) @ x === Node @ (g @ x) @ (list_to_p_list gs @ x). 
Proof.
  intros; unfold list_to_p_list; fold list_to_p_list. unfold fold_right; fold fold_right.
  rewrite star_occurs_true.   2: simpl; rewrite orb_true_r; auto. 2: caseEq gs; discriminate.
  qtac s_eq. 
  rewrite star_occurs_true.   2: simpl; rewrite orb_true_r; auto. 2: discriminate.  qtac s_eq. 
  unfold star at 1; qtac k_eq. 
  rewrite eta_red; auto. apply occurs_combination; auto.
Qed. 

Definition rf_compose f gs :=  d (list_to_p_list gs) @ (K @ f).

Lemma rf_compose_cons :
  forall f g gs z, combination f -> combination g -> combination z -> 
                   rf_compose f (g :: gs) @ z
                              === rf_compose (\"rest"(f @ ((Node @ (g @ z) @ Ref "rest")))) gs @ z. 
Proof.
  intros. unfold rf_compose, d. qtac s_eq.   qtac list_to_p_list_cons. 
  rewrite star_occurs_true. 2: simpl; rewrite ! orb_true_r; auto. 2: discriminate. 
  qtac s_eq. rewrite star_occurs_false.  2: apply occurs_combination; auto.
  qtac k_eq.   rewrite eta_red; auto. apply occurs_combination; auto. combination_tac; auto.
Qed.

  
Fixpoint rf_to_tree rf :=
  match rf with
  | Zero_fn => K@ zero_t (* zero discards its tuple of arguments *) 
  | Succ_fn =>  △ @ (△ @ first_c) @ (K@ succ_t) (* succ acts on the first argument *) 
  | Proj_fn i _ =>  proj i (* proj i gets the ith argument *) 
  | Compose_fn f gs => rf_compose (rf_to_tree f) (map rf_to_tree gs) 
  | Primrec g h => rf_primrec (rf_to_tree g) (rf_to_tree h)
  | Minrec g => Y2 (minrec (rf_to_tree g))       
  end.


Lemma rf_combination0:
  forall k,
  (forall fs,  fold_left (fun n h => n + rf_size h) fs 0  < k -> 
                combination (star "x" (fold_right (fun (g : recfun) (f0 : Tree0) =>
                                                 △ @ (rf_to_tree g @ Ref "x") @ f0) △ fs))) /\
  (forall f, rf_size f < S k -> combination (rf_to_tree f)). 
Proof.
  induction k; split. 
  (* 4 *)
  intros; lia. 
  (* 3 *)
  intro f; assert(rf_size f >0) by apply rf_size_positive; lia.  
  (* 2 *)
  intro fs; caseEq fs; intros; subst; auto.
  (* 3 *)
  simpl;  cbv; now combination_tac. 
  (* 2 *)
  assert(fp: forall l n, fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l n =
                     n + fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l 0).
   clear.
   induction l; intros; simpl; auto. rewrite IHl.
   match goal with r: recfun |- _ => rewrite (IHl (rf_size r)); lia end. 
   (* 2 *)
   unfold fold_right; fold fold_right.  
   rewrite star_occurs_true; [ | simpl; rewrite orb_true_r; auto | caseEq l; intros; discriminate]. 
   combination_tac; auto. apply IHk. rewrite fp in *.   simpl in *. rewrite fp in *.
   match goal with | rf : recfun |- _ => assert(rf_size rf >0) by apply rf_size_positive end;  lia.
   assert(combination(rf_to_tree r)). apply IHk.    simpl in *. rewrite fp in *. lia. 
   unfold star; fold star; simpl. rewrite occurs_combination; auto. simpl; combination_tac; auto.   
   (* 1 *)
   assert(aux1: forall l m1 m2, m1<= m2 -> fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l m1 <=
                                  fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l m2).
  clear;   induction l; intros; simpl; try lia.  eapply IHl; lia. 
    assert(aux2: forall l m,  m <=  fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l m).
  clear;   induction l; intros; simpl; try lia.  elim IHl; intros; lia. 


  assert(occ: forall n x, occurs x (Nat.iter n (fun z : Tree0 => second z) (Ref x)) = true). 
    clear.
    induction n; intros; simpl; auto. apply eqb_refl. now (rewrite IHn).
    intros f r.
    assert(fp: forall l n, fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l n =
                           n + fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l 0).
   clear.
   induction l; intros; simpl; auto. rewrite IHl.
   match goal with | r: recfun |- _ => rewrite (IHl (rf_size r)); lia end.
   caseEq f; intros; subst. 
   (* 6 *)
   1,2: cbv; combination_tac.
   (* 4 *)
   clear; simpl. induction n; intros; simpl; now combination_tac. 
   (* 3 *)
   simpl. unfold rf_compose, d; combination_tac.
   induction l; intros; subst. simpl. combination_tac.
   simpl. unfold list_to_p_list; fold list_to_p_list. 
   unfold fold_right; fold fold_right.  rewrite star_occurs_true.
   2: simpl; rewrite orb_true_r; auto. 2: caseEq l; intros; subst; discriminate.
   combination_tac. apply IHl.
   simpl in *.
   assert(fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l (S (rf_size r0)) <=
         fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l (S (rf_size r0 + rf_size a))).
  apply aux1. lia. lia. 
   unfold star; fold star; simpl. rewrite occurs_combination; auto. simpl; combination_tac; auto.   
   apply IHk. simpl in r.
   assert(S(rf_size r0 + rf_size a) <= fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l (S (rf_size r0 + rf_size a)) ) by eapply aux2; auto. 
   lia.
   apply IHk. simpl in r.
   assert(S(rf_size r0 + rf_size a) <= fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l (S (rf_size r0 + rf_size a)) ) by eapply aux2; auto. 
   lia.
   apply IHk. simpl in r.
   assert(S(rf_size r0 + rf_size r0) <= fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l (S (rf_size r0 + rf_size r0)) ) by eapply aux2; auto. 
   simpl in r. 
 assert(S(rf_size r0) <= fold_left (fun (n : nat) (h : recfun) => n + rf_size h) l (S (rf_size r0)) ) by eapply aux2; auto. 
lia.
   (* 2 *)
subst. unfold rf_to_tree; fold rf_to_tree. unfold rf_primrec. combination_tac.
eapply IHk. simpl in r. assert(rf_size r0 >0) by apply rf_size_positive. lia.   
 eapply IHk. simpl in r.
assert(rf_size r1 >0) by apply rf_size_positive. lia.   
(* 1 *)
   unfold rf_to_tree; fold rf_to_tree; unfold minrec_aux; combination_tac.
   eapply IHk. simpl in r. lia.
Qed.

Lemma rf_combination: forall f, combination (rf_to_tree f).
Proof.  intros. eapply rf_combination0; auto. Qed.

Hint Resolve rf_combination : TreeHintDb. 


Inductive pr_eval : recfun -> recfun -> Prop :=
| p_pr : forall xs1 x xs2, pr_eval (Compose_fn (Proj_fn (List.length xs1) (List.length xs2))
                                                  (xs1 ++ (x:: xs2))) x
| c_pr : forall f gs xs, pr_eval (Compose_fn (Compose_fn f gs) xs)
                                     (Compose_fn f (map (fun g => Compose_fn g xs) gs))
| prec_pr_z : forall g h xs,  pr_eval (Compose_fn (Primrec g h) (Zero_fn :: xs))
                                      (Compose_fn g xs)
| prec_pr_s : forall g h x xs,  pr_eval (Compose_fn (Primrec g h) ((Compose_fn Succ_fn (x:: nil)) :: xs))
                                         (Compose_fn h ((Compose_fn (Primrec g h) (x::xs)) :: 
                                                     (x:: xs)))
| min_pr_z : forall g x xs, pr_eval (Compose_fn g (x::xs)) Zero_fn ->
                            pr_eval (Compose_fn (Minrec g) (x::xs)) x 
| min_pr_s: forall g x xs y, pr_eval (Compose_fn g (x::xs)) (Compose_fn Succ_fn (y:: nil)) ->
                             pr_eval (Compose_fn (Minrec g) (x::xs))
                                     (Compose_fn (Minrec g) ((Compose_fn Succ_fn (x:: nil)) :: xs)).


Lemma aux: forall n f (x:Tree0), Nat.iter (S n) f x = f (Nat.iter n f x).
Proof.  induction n; intros; simpl; auto. Qed.

Lemma proj_program: forall i, program (proj i).
Proof.  induction i; intros; program_tac.  Qed.

  
Lemma aux2:  forall xs z, substitute (fold_right  (fun (g : recfun) (f : Tree0) => △ @ (rf_to_tree g @ (Ref "x")) @ f) △ xs) "x" z =  fold_right  (fun (g : recfun) (f : Tree0) => △ @ (rf_to_tree g @ z) @ f) △ xs.
Proof.
  induction xs; intros; simpl; auto; rewrite ! (substitute_combination (rf_to_tree _)); rewrite ? IHxs; auto_t.
  Qed. 



Lemma minrec_red:
  forall g x xs z, combination z -> 
    rf_to_tree (Compose_fn (Minrec g) (x :: xs)) @ z === 
       (isLeaf @ (rf_to_tree (Compose_fn g (x :: xs)) @ z) @ (rf_to_tree x @ z) @
               (rf_to_tree (Compose_fn (Minrec g) (Compose_fn Succ_fn (x :: nil) :: xs)) @ z)).
Proof. 
  intros.  unfold rf_to_tree; fold rf_to_tree.
  unfold map; fold map. replace (fix map (l : list recfun) : list Tree0 :=
           match l with
           | nil => nil
           | a :: t => rf_to_tree a :: map t
           end) with (map rf_to_tree) by auto.  
  unfold rf_compose, d. qtac s_eq. rewrite Y2_red. 
  unfold fold_right; fold fold_right.  qtac list_to_p_list_cons. 
  unfold minrec at 1. qtac s_eq. f_equal_q.  f_equal_q.  f_equal_q. f_equal_q.
  simpl.  unquotient_tac. qtac s_eq. unfold list_to_p_list, fold_right.
  rewrite star_occurs_true.   2: simpl; rewrite orb_true_r; auto. 2: discriminate. qtac s_eq.
  rewrite star_occurs_true. 2: simpl; rewrite orb_true_r; auto. 2: discriminate. qtac s_eq.
  unfold star at 1. qtac k_eq. rewrite eta_red; auto.
  apply occurs_combination; auto. apply rf_combination; auto.
Qed.



Theorem rf_to_tree_preserves_eval:
  forall x y, pr_eval x y ->
              forall z, combination z -> rf_to_tree x @ z === rf_to_tree y @z.
Proof.
  intros x y e; induction e; intros z c.
  (* 6 *)
  unfold rf_to_tree; fold rf_to_tree. unfold d, eq_q.
  induction xs1; intros. unfold Datatypes.length, proj, first_c. 
  unfold app, fold_right. rewrite star_occurs_true. 2: unfold occurs; rewrite orb_true_r; auto.
  2: discriminate.
  rewrite star_occurs_false; auto. rewrite star_occurs_true. 2: simpl; auto. 2: discriminate. 
  rewrite star_occurs_false; auto. rewrite eta_red; auto.
  unfold rf_compose, d. qtac s_eq. unfold map; fold map. unfold fold_right; fold fold_right.
  qtac list_to_p_list_cons. 
  (* 6 *) 
  replace (Datatypes.length (a :: xs1)) with (S (Datatypes.length xs1)) by auto. 
  unfold proj; fold proj. unfold second_c.
  rewrite star_occurs_true; auto. 2: discriminate. rewrite star_occurs_false; auto.
  rewrite star_occurs_true; auto. 2: discriminate. rewrite eta_red; auto.
  rewrite star_occurs_false; auto. rewrite <- IHxs1. 
  unfold app; fold app. unfold rf_compose, map, fold_right.
  unfold d;   qtac list_to_p_list_cons.  qtac list_to_p_list_cons. unfold KI, I, K. qtac k_eq.
  (* 5 *)
  unfold rf_to_tree; fold rf_to_tree. 
  unfold rf_compose, d. qtac s_eq. f_equal_q. rewrite map_map.
  induction gs; intros; unfold map; fold map. unfold list_to_p_list; fold list_to_p_list.
  unfold fold_right; fold fold_right.
  unfold star at 1 3.   qtac k_eq.
  unfold rf_to_tree; fold rf_to_tree. 
  qtac list_to_p_list_cons. unfold rf_compose.  unfold d; qtac s_eq. f_equal_q. qtac IHgs.
  unfold rf_compose; combination_tac.
  clear; induction xs; combination_tac; simpl. unfold list_to_p_list; fold list_to_p_list.
  unfold fold_right; fold fold_right.   rewrite star_occurs_true.
  2: simpl; rewrite orb_true_r; auto. combination_tac. 
  unfold list_to_p_list in IHxs; auto. rewrite star_occurs_true.
  2: simpl; rewrite orb_true_r; auto. rewrite eta_red.
  2: apply occurs_combination; auto; apply rf_combination. 
  2: discriminate.   2: caseEq xs; discriminate. simpl. combination_tac. apply rf_combination.
  apply rf_combination.
  (* 4 *)
  unfold rf_to_tree; fold rf_to_tree. unfold rf_compose, d.  qtac s_eq. 
  unfold rf_primrec, eq_q; eqtac.  rewrite Y2_red. qtac s_eq.
  unfold map; fold map.  qtac list_to_p_list_cons.
  unfold rf_to_tree at 1. qtac k_eq. 
  (* 3 *)
  unfold rf_to_tree; fold rf_to_tree.
  unfold rf_compose, d. qtac s_eq. 
  unfold rf_primrec. qtac Y2_red. fold rf_primrec. 
  unfold map; fold map.   qtac list_to_p_list_cons.
  unfold rf_to_tree at 1; fold rf_to_tree.
  replace (fix map (l : list recfun) : list Tree0 :=
             match l with
             | nil => nil
             | a :: t => rf_to_tree a :: map t
             end) with (map rf_to_tree) by auto.
  unfold map at 1.
  unfold rf_compose at 1. unfold d; qtac s_eq.
  qtac list_to_p_list_cons. unfold list_to_p_list at 1. unfold fold_right.
  unfold star at 1. qtac k_eq.   unfold succ_t; qtac k_eq.
  unfold first_c. 
  rewrite star_occurs_true. unfold star at 1. qtac k_eq.
  rewrite star_occurs_true. unfold star at 1. qtac s_eq.
  unfold K. unfold occurs at 1. unfold orb. qtac f_eq. f_equal_q. f_equal_q. f_equal_q.
  apply eq_q_sym. unfold rf_to_tree; fold rf_to_tree. unfold rf_compose, d. qtac s_eq.
  unfold rf_primrec. f_equal_q.
  unfold map; fold map.   qtac list_to_p_list_cons. 
  auto. 
  discriminate.   
  auto.
  discriminate.
  (* 2 *)
  unfold eq_q.   rewrite minrec_red. 
  qtac IHe.
  eqtac.   unfold rf_to_tree. eqtac.  auto. 
  (* 1 *)
 unfold eq_q.   rewrite minrec_red; auto. 
 qtac IHe; auto.  unfold rf_to_tree; fold rf_to_tree; unfold succ_t, first_c; eqtac.
 rewrite star_occurs_true; auto; try discriminate. 
 rewrite star_occurs_false; auto.
 rewrite star_occurs_true; auto; try discriminate. 
 rewrite star_occurs_false; auto.
 rewrite eta_red; auto. 
 unfold rf_compose, d; qtac s_eq. 
Qed.


(* 4.7: Lists and Strings *)


Definition t_nil := △. 
Definition t_cons h t := △@ h@ t.
Definition t_head := \"xs" (App (App (△@ (Ref "xs")) (K@ I)) K).
Definition t_tail := \"xs" (App (App (△@ (Ref "xs")) (K@ I)) (K@ I)).


Lemma head_red: forall h t, App t_head (t_cons h t) === h.
Proof. tree_eq. Qed. 
Lemma tail_red: forall h t, App t_tail (t_cons h t) === t.
Proof. tree_eq. Qed. 


(* 4.8: Mapping and Folding *)

Definition list_map_swap :=
  (* the list argument xs then the recursion argument map and finally the function f, to  exploit Y2 *) 
  Eval cbv in
    \"xs"
     (Node @ Ref "xs"
           @ (K @ (K @ t_nil))
           @ (\"h"
               (\"t"
                 (\"map"
                   (\"f"
                     (t_cons
                        (Ref "f" @ Ref "h") 
                        (Ref "map" @ Ref "t" @ Ref "f")
          )))))).

Definition list_map := swap (Y2 list_map_swap). 


Lemma map_nil: forall f, list_map @ f @ t_nil === t_nil.
Proof.  tree_eq. Qed. 

Lemma map_cons :
  forall f h t, list_map @ f @ (t_cons h t) === t_cons (f @ h) (list_map @ f@ t).
Proof. tree_eq. Qed. 


Definition list_foldleft_aux := 
  Eval cbv in
    \"ys"
     ( Node @ Ref "ys" @ (K @ (K @ I))
            @ (\"h"
                (\"t"
                  (\"fold" 
                    (\"f"
                      (\"x"
                        (Ref "fold" @ Ref "t" @ Ref "f" @ (Ref "f" @ Ref "h" @ Ref "x"))
     )))))).

Definition list_foldleft_re_order :=
  Eval cbv in \"f" (\"x" (\"ys" (Ref "fold" @ Ref "ys" @ Ref "f" @ Ref "x"))).

Print list_foldleft_re_order.

Definition list_foldleft :=
  △ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @
(△ @
 (△ @
  (△ @
   (△ @
    (△ @
     (△ @
      (△ @ (△ @ (△ @ △ @ Y2 list_foldleft_aux)) @
       (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @ 
     (△ @ △ @ (△ @ △)))) @ (△ @ △ @ △))) @ (△ @ △ @ △)). 

Lemma list_foldleft_nil:
  forall f x, list_foldleft @ f @ x @ t_nil === x. 
Proof. intros; unfold list_foldleft; eqtac; qtac Y2_red; unfold list_foldleft_aux at 1; qtac s_eq.
Qed.

Lemma list_foldleft_cons:
  forall f x h t, list_foldleft @ f @ x @ (t_cons h t) === list_foldleft @ f @ (f @ h @ x) @ t. 
Proof.
  intros; unfold list_foldleft at 1; eqtac; qtac Y2_red; unfold t_cons, list_foldleft_aux at 1; eqtac; 
  unfold list_foldleft; eqtac. 
Qed.


Definition list_foldright_aux := 
  Eval cbv in
    \"ys"
     (Node @ Ref "ys" @ (K @ (K @ I))
           @ (\"h"
                (\"t"
                  (\"fold" 
                    (\"f"
                      (\"x"
                        (Ref "f" @ Ref "h" @ (Ref "fold" @ Ref "t" @ Ref "f" @ Ref "x"))
     )))))).

Definition list_foldright_re_order :=
  Eval cbv in \"f" (\"x" (\"ys" (Ref "fold" @ Ref "ys" @ Ref "f" @ Ref "x"))).

Print list_foldright_re_order.

Definition list_foldright :=
  △ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @
(△ @
 (△ @
  (△ @
   (△ @
    (△ @
     (△ @
      (△ @ (△ @ (△ @ △ @ Y2 list_foldright_aux)) @
       (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @ 
     (△ @ △ @ (△ @ △)))) @ (△ @ △ @ △))) @ (△ @ △ @ △))
.


Lemma list_foldright_nil:  forall f x, list_foldright @ f @ x@ t_nil === x.
Proof. intros; unfold list_foldright; eqtac; qtac Y2_red; unfold list_foldright_aux at 1; eqtac. Qed. 

Lemma list_foldright_cons:
  forall f x h t, list_foldright @ f @ x @ (t_cons h t) === f @ h @ (list_foldright @ f@ x @ t). 
Proof.
  intros; unfold list_foldright at 1; eqtac; qtac Y2_red; unfold t_cons, list_foldright_aux at 1; eqtac;
    unfold list_foldright; eqtac. 
Qed. 


Definition list_append xs ys :=
  list_foldright @ (\"h" (\"t" (t_cons (Ref "h") (Ref "t")))) @ ys @ xs.


Lemma append_nil_r: forall xs, list_append t_nil xs === xs.
Proof. apply list_foldright_nil. Qed.



(* Exercises *)


(* 2 *)

Lemma substitute_by_omega:
  substitute (\"f" (Ref "f" @ (Ref "z" @ Ref "z" @ Ref "f"))) "z" ω 
             === \"f" (Ref "f" @ ( ω @  ω @ Ref "f")).
Proof. cbv; auto. Qed. 

(* 3 *)

Compute W.

(* 4 *) 
Definition omega' := bracket "x" (bracket "f" (Ref "f" @ (Ref "x" @ Ref "x" @ Ref "f"))).

Lemma omega'_red: forall x f, omega' @ x @ f ===  ω @ x @ f.
Proof. tree_eq. Qed. 
  
(* 5 *) 

Definition times_aux :=
  Eval cbv in
    \"m"
     (\"times"
       (\"n"
         (App (App (△@ (Ref "n")) △)
              (K@ (\"x" (App (App (Ref "plus") (Ref "m"))
                             (App (App (Ref "times") (Ref "m")) (Ref "x")))))
     ))).

Print times_aux.

Definition times := Y2 (
                        △ @
(△ @
 (△ @ (△ @ (△ @ △ @ (△ @ △ @ △))) @
  (△ @
   (△ @
    (△ @
     (△ @
      (△ @ (△ @ (△ @ △ @ (△ @ △ @ △))) @
       (△ @
        (△ @
         (△ @
          (△ @
           (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ △)))) @
            (△ @
             (△ @
              (△ @
               (△ @
                (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ △)))) @
                 (△ @
                  (△ @
                   (△ @
                    (△ @
                     (△ @
                      (△ @
                       (△ @ (△ @ (△ @ △ @ (△ @ △ @ △))) @
                        (△ @
                         (△ @
                          (△ @
                           (△ @
                            (△ @ (△ @ (△ @ △ @ (△ @ △ @ △))) @
                             (△ @
                              (△ @
                               (△ @
                                (△ @
                                 (△ @ (△ @ (△ @ △ @ (△ @ (△ @ △) @ (△ @ △)))) @
                                  (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @
                                (△ @ △ @ △))) @ (△ @ △ @ △)))) @ (△ @ △ @ △))) @ 
                         (△ @ △ @ △)))) @
                      (△ @
                       (△ @
                        (△ @
                         (△ @
                          (△ @ (△ @ (△ @ (△ @ plus) @ (△ @ △ @ (△ @ △)))) @
                           (△ @ △ @ (△ @ △)))) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @ 
                    (△ @ △ @ △))) @ (△ @ △ @ △)))) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @ 
          (△ @ △ @ △))) @ (△ @ △ @ △)))) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @
(△ @ △ @ (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ △)) @ △)))))
).

Lemma times_zero: forall m, App (App times m) zero === zero.
Proof. tree_eq. Qed.


Lemma times_successor:
  forall m n,  App (App times m) (App successor n) ===
                      (App (App plus m) (App (App times m) n)).
Proof.   intros; unfold times at 1; qtac Y2_red; fold times;  unfold successor; eqtac. Qed. 

(* 6 *)

Definition minus := 
  Y2 (\"m"
           (\"minus"
                 (\"n"
                       (App (App (△@ (Ref "n")) (Ref "m"))
                            (K@ (App (Ref "minus") (App predecessor (Ref "m")))))
                  ))).


(* 7 *)

Lemma mu_succ_program : program (rf_to_tree (Minrec Succ_fn)).
Proof.  simpl. apply Y2_program. program_tac. Qed.

(* Minrec Succ_fn looks for the minimum solution to succ x === 0 but none such exists *) 


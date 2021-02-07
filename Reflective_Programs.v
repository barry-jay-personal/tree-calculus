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
(*                Chapter 6: Reflective Programs                      *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Bool List String.
Require Import Reflective.Tree_Calculus.
Require Import Reflective.Extensional_Programs.
Require Import Reflective.Intensional_Programs.

Set Default Proof Using "Type".


(* Branch-first evaluation *)

Inductive branch_first_eval: Tree -> Tree -> Tree -> Prop :=
| e_leaf : forall x, branch_first_eval △ x (△ @ x)
| e_stem : forall x y, branch_first_eval (△ @ x) y (△ @ x@ y)
| e_fork_leaf: forall y z, branch_first_eval (△ @ △@ y) z y
| e_fork_stem: forall x y z yz xz v,
    branch_first_eval y z yz -> branch_first_eval x z xz -> branch_first_eval yz xz v ->
    branch_first_eval (△ @ (△ @ x)@ y) z v
| e_fork_fork : forall w x y z zw v, branch_first_eval z w zw -> branch_first_eval zw x v ->
                                     branch_first_eval (△ @ (△ @ w@ x) @y) z v
.
              
Hint Constructors branch_first_eval : TreeHintDb.

Lemma branch_first_eval_program :
  forall M N P, branch_first_eval M N P -> program M -> program N -> program P.
Proof.  intros M N P ev; induction ev; intros; inv1 program; program_tac. Qed. 
  

Lemma branch_first_eval_program_red:
  forall M N, program (M@ N) -> branch_first_eval M N (M@ N).
Proof. intros M N p; inv1 program; subst; auto_t. Qed.


    
Definition Db x := D @ (D @ (K @ x) @ Id) @ (K @ D).


Definition bfforkleaf := Eval cbv in \"y" (K @ (K @ (Ref "y"))).

Definition bfforkfork :=
  Eval cbv in 
    \"wf"
      (\"xf"
         (K
            @ (D
                 @ (d K
                      @ (D @ (D @ (K @ Ref "wf")) @ (K@D))
                   )
                 @ (K @ (D @ (K @ Ref "xf")))
      ))). 


Definition bfforkstem e  :=
  Eval cbv in 
    substitute
      (\"xs"
         (\"ys"
            (D @ (d (K@(K@ Ref "e")) @ (Db (Ref "xs")))
               @ (D @ (d K @ (Db (Ref "ys")))
                    @ (K @ D)
      ))))
      "e" e. 
      


(* onFork Node = K Node since it will be applied to an evaluator *) 

Definition onFork tr :=
  Eval cbv in
    substitute
      (\"t"
         (△
            @ (isFork2 @ Ref "t")
            @ (△ @ (Ref "t") @ △ @ Ref "triage")
            @ (K @ (K @ (K@ Ref "t")))
      ))
      "triage" tr.

Lemma onFork_leaf: forall tr, onFork tr @ Node === K@ Node.
Proof. tree_eq. Qed.
Lemma onFork_stem : forall tr x, onFork tr @ (Node @ x) === K @ (Node @ x).
Proof. tree_eq. Qed.
Lemma onFork_fork : forall tr x y, onFork tr @ (Node @ x @ y) === tr @ x @ y. 
Proof. tree_eq. Qed.

  
Definition bf :=  Y2s (onFork (triage bfforkleaf (bfforkstem eager) bfforkfork)). 



Lemma program_bf : program bf.
Proof. program_tac. Qed.

(* 
Compute(term_size bf). 514. 
*) 


Lemma bf_leaf: bf @ △ === △.  
Proof. tree_eq. Qed.


Lemma bf_stem: forall x, bf @ (△ @ x) === △ @ x.  
Proof. tree_eq. Qed.

Lemma bf_fork:
  forall x y, bf @ (△ @ x @ y) === (triage bfforkleaf (bfforkstem eager) bfforkfork) @ x @ y @ bf.  
Proof. tree_eq. Qed.

Lemma bf_fork_leaf:  forall y z, bf @ (△@△@y) @ z === y.
Proof.  tree_eq. Qed. 


Lemma bf_fork_stem:
  forall x y z, bf @ (△@(△@x) @y) @ z === eager @ (bf @ x @ z) @ (bf @ (bf @ y @ z)). 
Proof. 
  intros; unfold eq_q; rewrite quotient_app; rewrite bf_fork.
  rewrite quotient_app.  rewrite quotient_app.   rewrite triage_stem; unfold bfforkstem, Db, eager; eqtac;   
    starstac ("f" :: "z" :: nil); auto. 
Qed. 

Lemma bf_fork_fork:
  forall w x y z, bf @ (△@(△@w@x) @y) @ z === bf @ (bf @ z @ w) @x.
Proof.
  intros; unfold eq_q; rewrite quotient_app; rewrite bf_fork; rewrite quotient_app; rewrite quotient_app; rewrite triage_fork; unfold bfforkfork, d;
    starstac ("xf"  :: "wf"  :: nil); auto.  
Qed. 

(* 
Compute (term_size bf).
*) 

Theorem branch_first_eval_to_bf:
  forall M N P, program M -> program N -> branch_first_eval M N P -> bf@M@N === P. 
Proof.
  intros M N P prM prN ev; induction ev; intros; simpl; subst; inv1 program; subst; unfold eq_q.   
  rewrite quotient_app;  rewrite bf_leaf ; auto.
  rewrite quotient_app; rewrite bf_stem ; auto. 
   rewrite bf_fork_leaf ; auto. 
   rewrite bf_fork_stem. rewrite quotient_app. rewrite quotient_app. rewrite IHev2; auto.
   rewrite quotient_app;  rewrite IHev1; auto. 
   rewrite <- quotient_app. rewrite <- quotient_app. rewrite <- quotient_app.
   rewrite eager_of_factorable.  apply IHev3; auto.  
    eapply branch_first_eval_program; eauto . 
    eapply branch_first_eval_program; eauto . 
    apply programs_are_factorable.     eapply branch_first_eval_program; eauto . 
    rewrite bf_fork_fork. rewrite quotient_app. rewrite quotient_app. rewrite IHev1; auto.
    rewrite <- quotient_app. rewrite <- quotient_app. rewrite IHev2; auto;
    eapply branch_first_eval_program; eauto .
Qed.

Lemma bf_identity: forall z, bf @ Id @ z === z.
Proof.
  intros; unfold_op; unfold eq_q.  rewrite bf_fork_stem. rewrite quotient_app.
  rewrite quotient_app.  rewrite quotient_app.
  rewrite bf_leaf. rewrite quotient_app. rewrite quotient_app.  rewrite bf_stem.
  repeat rewrite <- quotient_app.
  rewrite eager_of_factorable; auto_t; rewrite bf_fork_leaf; auto. 
Qed.   


  
(* Quotation *)

Fixpoint meta_quote M :=
 match M with
 | M1@ M2 => △ @ (meta_quote M1) @ (meta_quote M2)
 | _ => M
 end.

Lemma meta_quote_preserves_combinations:
  forall M, combination M -> combination (meta_quote M).
Proof. induction M; simpl; auto; intro c; combination_tac; auto. Qed. 

Definition quote :=
  Y2
    (\"q"
       (\"x"
          (isStem
             @ (Ref "x")
             @ (△
                  @ ((Ref "x") @ △)
                  @ △
                  @ (\"x1" (K@ (K @ ((Ref "q") @ (Ref "x1")))))
               )
             @ (△
                  @ (Ref "x")
                  @ △
                  @ (\"x1"
                       (\"x2"
                          (△
                             @ (K@((Ref "q") @ (Ref "x1")))
                             @ ((Ref "q") @ (Ref "x2"))
    ))))))).

Ltac quote_tac :=
  unfold quote, eq_q; rewrite Y2_red; fold quote; starstac ("x2" :: "x1" :: "x" :: "q" :: nil);
  unfold d; eqtac.

Lemma quote_red: forall M, program M -> App quote M === meta_quote M.
Proof.
  intros M prM; induction prM; intros; [
    tree_eq |
    quote_tac; rewrite <- quotient_app;  rewrite IHprM; auto |
    quote_tac; rewrite <- quotient_app; rewrite <- quotient_app;
    rewrite IHprM1; rewrite IHprM2; auto
    ].  
Qed.




(* Root evaluation acts on meta_quotes *) 

Inductive root_eval: Tree -> Tree -> Prop :=
| sh_leaf : root_eval △ △
| sh_fork_leaf : forall f z, root_eval f △ -> root_eval (△ @ f @ z) (△ @ z)
| sh_fork_stem: forall f z t, root_eval f (△ @ t) ->
                          root_eval(△ @ f @ z) (△ @ t @ z)
| sh_fork_fork_fork_leaf : forall f z t y v,
    root_eval f (△ @ t @ y) -> root_eval t △ -> root_eval y v -> 
    root_eval(△ @ f @ z) v
| sh_fork_fork_fork_stem: forall f z t y x v,
    root_eval f (△ @ t @ y) -> root_eval t (△ @ x) ->
    root_eval (△ @ (△ @ y @ z) @ (△ @ x @ z)) v -> 
    root_eval(△ @ f @ z) v
| sh_fork_fork_fork_fork: forall f z t y w x v, 
    root_eval f (△ @ t @ y) -> root_eval t (△ @ w @ x) ->
    root_eval (△ @ (△ @ z @ w) @ x) v -> 
    root_eval(△ @ f @ z) v
.
              
Hint Constructors root_eval : TreeHintDb.



(* The Representation *)

Definition rootl := \"r" (\"y" (\"z" (Ref "r" @ Ref "y"))). 
Definition roots :=
  Eval cbv in
    \"x" (\"r" (\"y" (\"z" (Ref "r" @ (△ @ (△ @ Ref "y" @ Ref "z") @ (△ @ Ref "x" @ Ref "z")))))).

Definition rootf :=
  Eval cbv in
  \"w"(\"x" (\"r" (\"y" (\"z" (Ref "r" @ (△ @ (△ @ Ref "z" @ Ref "w") @ Ref "x")))))). 

Definition root1 :=
  Eval cbv in
  \"t" (\"y" (\"r1" (triage rootl roots rootf @ (Ref "r1" @ Ref "t") @ (Ref "r1") @ (Ref "y")))).

Definition root :=
  Y2 (\"r"(\"a" (△ @ Ref "a" @ △ @ (\"f" (onFork root1 @ (Ref "r" @ Ref "f") @ (Ref "r")))))).

(* 
Compute (term_size root). 
*)

Lemma root_program: program root.
Proof. program_tac. Qed.

Lemma root_eval_combination:
  forall M N, root_eval M N -> combination M -> combination N.
Proof.
  intros M N e; induction e; intro c; inv1 combination; subst; auto_t; apply IHe3; auto; 
    assert(combination (△ @ t @ y)) by (now apply IHe1); combination_tac; auto;    
      [ assert(combination (Node @ x)) by (now apply IHe2)
      | assert(combination (Node @ w @ x)) by (now apply IHe2)
      | assert(combination (Node @ w @ x)) by (now apply IHe2)];
      combination_tac; auto.
Qed.

       
Theorem root_eval_to_root: forall M P, root_eval M P -> root @ M === P.
Proof.
  intros M P ev; induction ev; intros;
    unfold root, eq_q; rewrite Y2_red; fold root; unfold onFork, d;  starstac ("f" :: "a" :: "r" :: nil);  
      eqtac; auto; rewrite ? IHev; eqtac; auto;
  rewrite <- quotient_app; rewrite ? IHev; eqtac; auto;
  rewrite <- quotient_app;   rewrite IHev1; eqtac; auto;
  unfold root1; eqtac; rewrite <- quotient_app; rewrite IHev2; unfold triage, rootf; eqtac; auto. 


Qed.

(* 
Compute(term_size root). 
*) 

(* Root-and-Branch Evaluation *)

Inductive rb_eval : Tree -> Tree -> Prop :=
| rsh_leaf : forall x, root_eval x △ -> rb_eval x △
| rb_stem : forall x y v, root_eval x (△ @ y) -> rb_eval y v -> rb_eval x (△ @ v)
| rb_fork : forall x y z v w, root_eval x (△ @ y@ z) -> rb_eval y v -> rb_eval z w ->
                                    rb_eval x (△ @ v @w)
.                                                                               


          
Definition rb :=
  Y2 (\"r" (\"x" (triage
                    △
                    (\"y" (△ @ ((Ref "r") @ (Ref "y"))))
                    (\"y" (\"z" (△ @ ((Ref "r") @ (Ref "y")) @ ((Ref "r") @ (Ref "z")))))
                    @ (root @ (Ref "x"))
     ))).



  
Lemma rb_eval_implies_rb :
  forall M P, rb_eval M P -> combination M -> rb @ M === P. 
Proof.
  intros M P e; induction e as [x | x y | x y z]; intro c; subst; unfold eq_q; [ 
     assert(re: root @ x === △) by now apply root_eval_to_root 
    | assert(re:root @ x === △@ y) by now apply root_eval_to_root 
    | assert(re: root @ x === △@ y@z) by (apply root_eval_to_root; auto)
    ]; 
  unfold rb; rewrite Y2_red; fold rb;
  unfold triage; starstac ("z" :: "y" :: "x" :: "r" :: nil); 
    rewrite <- quotient_app.
  rewrite re;   eqtac; auto.  
 assert(combination (△ @ y)) by (eapply root_eval_combination; eauto); inv1 combination;
  rewrite re;   eqtac; auto; rewrite <- quotient_app; rewrite IHe; auto.
 assert(combination (△ @ y@z)) by (eapply root_eval_combination; eauto);inv1 combination; subst; 
  rewrite re; eqtac; auto; rewrite <- quotient_app; rewrite IHe1; auto;   
  rewrite <- quotient_app; rewrite IHe2; auto. 
Qed.

(* Root-First Evaluation *)

Definition rf_eval M N P := rb_eval (meta_quote (M@ N)) P. 


Definition rf :=
  wait(\"q" (\"f" (\"z" (rb @ (△ @ ((Ref "q") @ (Ref "f")) @ ((Ref "q") @ (Ref "z"))))))) quote.

(* waiting saves a copy of quote which saves 400 nodes *) 


  
Theorem root_first_eval_to_rf:
  forall M N P, rf_eval M N P -> program M -> program N -> rf @M@N  === P .
Proof.
  (intros M N P r ? ?; unfold rf;
  assert(combination M) by now apply programs_are_combinations;
  assert(combination N) by now apply programs_are_combinations;
  assert(combination rb) by (apply programs_are_combinations; program_tac)).  
  unfold wait, d, eq_q; starstac ("z" :: "f" :: "q" :: nil).
  rewrite <- quotient_app; rewrite ! quote_red; auto.
  rewrite <- quotient_app; rewrite ! quote_red; auto.  
  replace Noq with (quotient Node) by auto. repeat rewrite <- quotient_app. 
  replace (△ @ (meta_quote M) @ (meta_quote N)) with (meta_quote (M@ N)) by auto.
  unfold rf_eval in *; apply rb_eval_implies_rb; auto;
  apply meta_quote_preserves_combinations; auto_t. 
Qed.

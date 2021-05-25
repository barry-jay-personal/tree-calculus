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
(*               Chapter 5: Intensional Programs                      *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith Lia Bool List String.
Require Import Reflective.Tree_Calculus.
Require Import Reflective.Extensional_Programs.

Set Default Proof Using "Type".

(* 5.2: Size *)


Definition size_aux :=
  Eval cbv in 
    \"x"
       (isStem
             @ (Ref "x")
             @ (\"s"
                 (△
                  @ (Ref "x" @ △)
                  @ zero
                  @ (\"x1" (K @ (successor @ ((Ref "s") @ (Ref "x1")))))
               ))
             @ (△
                  @ (Ref "x")
                  @ (K @ (successor @ zero))
                  @ (\"x1"
                       (\"x2"
                          (\"s"
                            (successor
                               @ (Ref "plus"
                                      @ ((Ref "s") @ (Ref "x1"))
                                      @ ((Ref "s") @ (Ref "x2"))
       ))))))).

Set Printing Depth 1000.
Print size_aux.


Definition size := Y2 (△ @
(△ @
 (△ @
  (△ @
   (△ @ △ @
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
                       (△ @ (△ @ (△ @ △ @ (△ @ (△ @ △) @ (△ @ △)))) @
                        (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @ 
                      (△ @ △ @ △))) @ (△ @ △ @ △)))) @
                 (△ @
                  (△ @
                   (△ @
                    (△ @
                     (△ @
                      (△ @
                       (△ @ (△ @ (△ @ △ @ (△ @ △ @ plus))) @
                        (△ @
                         (△ @
                          (△ @
                           (△ @
                            (△ @ (△ @ (△ @ △ @ (△ @ (△ @ △) @ (△ @ △)))) @
                             (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @
                           (△ @ △ @ △))) @ (△ @ △ @ △)))) @ (△ @ △ @ (△ @ △)))) @ 
                    (△ @ △ @ △))) @ (△ @ △ @ △)))) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @ 
          (△ @ △ @ △))) @ (△ @ △ @ △)))) @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ △))))))))) @
  (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ △ @ △)))) @ △))) @
(△ @
 (△ @
  (△ @
   (△ @
    (△ @
     (△ @
      (△ @ (△ @ (△ @ △ @ △)) @
       (△ @ (△ @ (△ @ (△ @ (△ @ △ @ △)) @ (△ @ (△ @ △) @ (△ @ △)))) @ (△ @ △ @ △)))) @
     (△ @ △ @ (△ @ △)))) @
   (△ @ △ @
    (△ @
     (△ @
      (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ △)))) @
       (△ @
        (△ @
         (△ @ (△ @ (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ △)))) @ (△ @ (△ @ △) @ (△ @ △ @ △)))) @
          (△ @ △ @ △))) @ (△ @ △ @ △)))))))) @
 (△ @ (△ @ (△ @ △ @ (△ @ △))) @
  (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ (△ @ △) @ (△ @ △))))) @
   (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ △ @ (△ @ △ @ (△ @ △ @ (△ @ △ @ (△ @ (△ @ △) @ (△ @ △))))))))) @
    (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ △ @ (△ @ △ @ (△ @ (△ @ △) @ (△ @ △))))))) @ △)))))
                      ).


Lemma size_program: program size.
Proof. program_tac. Qed. 

Ltac sizetac :=
  intros; unfold size, eq_q; rewrite Y2_red; fold size; unfold size_aux; eqtac; auto.

Lemma size_leaf: size @ △ === successor @ zero. 
Proof. sizetac. Qed. 


Lemma size_fork:
  forall M N, size @ (△@ M@N) === successor @(plus @ (size @ M) @ (size @ N)).
Proof. sizetac. Qed. 

Lemma size_stem: forall M, size @ (△@ M) === successor @ (size @ M).
Proof. sizetac. Qed. 


(* 5.3: Equality *)


Definition equal_aux := 
  Eval cbv in 
    \"x"
     (isStem
        @ (Ref "x")
        @ (\"e" (\"y" (isStem
                         @ (Ref "y")
                         @ ((Ref "e")
                              @ (△ @ ((Ref "x") @ △) @ △ @ K)
                              @ (△ @ ((Ref "y") @ △) @ △ @ K)
                           )
                         @ KI
                      )))
        @ (△
             @ (Ref "x")
             @ (\"e" (\"y" (isLeaf @ (Ref "y"))))
             @ (\"x1"
                 (\"x2"
                   (\"e"
                     (\"y" (isFork
                              @ (Ref "y")
                              @ (△
                                   @ (Ref "y")
                                   @ △
                                   @ (\"y1"
                                       (\"y2"
                                         ((Ref "e")
                                            @ (Ref "x1")
                                            @ (Ref "y1")
                                            @ ((Ref "e")
                                                 @ (Ref "x2")
                                                 @ (Ref "y2")
                                              )
                                            @ KI
                                ))))
                              @ KI
     ))))))).

Definition equal := Y2 equal_aux.

(* Compute (term_size equal). 1145 *) 

Lemma equal_program: program equal.
Proof. program_tac. Qed.

Ltac equaltac :=
  unfold eq_q, equal at 1; rewrite quotient_app; rewrite Y2_red; fold equal;
  unfold equal_aux; eqtac; auto.


Theorem equal_programs: forall M,  program M -> equal @ M @ M === K. 
Proof.
  intros M prM; induction prM; intros; equaltac. qtac IHprM1; qtac IHprM2. 
Qed.

Theorem unequal_programs:
  forall M,  program M -> forall N, program N -> M<> N -> equal @ M @ N === KI. 
Proof.
  intros M prM; induction prM; intros P prP neq; inversion prP; intros; subst;
    try congruence; equaltac. (* slow *) 
  apply IHprM; congruence.
  assert(d: M = M0 \/ M<> M0) by repeat decide equality;   inversion d; subst ;[   
    qtac equal_programs;  qtac IHprM2;    congruence |
    qtac IHprM1; eqtac
    ]. 
Qed.



(* 5.4: Tagging *)

Definition tag t f := Eval cbv in d t @ (d f @ (K@ K)).
Definition getTag := Eval cbv in \"p" (first ((first (Ref "p")) @ △)).
Definition untag := Eval cbv in \"x" (first ((first (second (Ref "x"))) @ △)). 



Lemma tag_apply : forall t f x, (tag t f) @ x === (f@x).
Proof.  tree_eq. Qed. 

Lemma getTag_tag : forall t f, getTag @ (tag t f) === t .
Proof.  tree_eq. Qed. 

Lemma untag_tag: forall t f, untag @ (tag t f) === f. 
Proof.  tree_eq. Qed. 


Theorem tree_calculus_support_tagging :
  exists tag getTag, (forall t f x, (tag t f) @ x === (f@ x)) /\
                      (forall t f,  getTag @ (tag t f) === t).
Proof. exists tag, getTag;  split; tree_eq. Qed.

(* tagging of fixpoint functions *)


Definition tag_wait t :=
  Eval cbv in
    substitute (\"g" (tag (Ref "t") (wait self_apply (Ref "g")))) "t" t.



Definition Y2_t t f := tag t (wait self_apply (d (tag_wait t) @ (K@ (swap f)))). 


Lemma Y2_t_program: forall t f, program t -> program f -> program (Y2_t t f). 
Proof. intros; program_tac. Qed.


Theorem fixpoint_function : forall t f x, Y2_t t f @ x === f@ x @ (Y2_t t f).
Proof. tree_eq. Qed.

Theorem getTag_Y2_t: forall t f, getTag @ (Y2_t t f) === t.
Proof. tree_eq. Qed. 




(* 5.5: Simple Types *)
(* leaf = error, stem = base type, fork = function type *) 

Definition error_ty := △.
Definition Bool_ty := △@ △.
Definition Nat_ty := △@ (△@ △).
Definition Fun_ty U T := △@ U @ T.


Definition typed T t := tag T t.

Definition type_check_aux := (* maps U -> T and V to T or error *) 
  Eval cbv in
    \"x"
     (isFork @(Ref "x")
             @ (△@(Ref "x") @△
                 @ (\"u" (\"t" (\"v" (Ref "equal" @ (Ref "u") @ (Ref "v") @ (Ref "t") @ error_ty))))
               )
             @ error_ty
       ).

Print type_check_aux.

Definition type_check :=
  △ @ (△ @ (△ @ △ @ △)) @
(△ @
 (△ @
  (△ @
   (△ @
    (△ @ △ @
     (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ △)))))) @
      (△ @
       (△ @
        (△ @
         (△ @
          (△ @ (△ @ (△ @ △ @ (△ @ (△ @ (△ @ (△ @ (△ @ △)) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @
           (△ @ (△ @ (△ @ (△ @ (△ @ (△ @ equal) @ (△ @ △ @ (△ @ △)))) @ (△ @ △ @ △))) @
            (△ @ △ @ △)))) @ (△ @ △ @ △))) @ (△ @ △ @ △))))) @ (△ @ (△ @ (△ @ △ @ △)) @ △))) @
 (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ (△ @ △) @ (△ @ △))))) @
  (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ (△ @ △) @ (△ @ △))))) @
   (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ △ @ (△ @ △ @ (△ @ △ @ (△ @ △))))))) @
    (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ △ @ (△ @ △ @ (△ @ (△ @ △) @ (△ @ △))))))) @ △)))))
.
  
Lemma type_check_red: forall U T, program U -> type_check @ (Fun_ty U T) @ U === T.
Proof. intros; unfold type_check, Fun_ty; eqtac; qtac equal_programs. Qed. 
  
Definition typed_app_aux :=
  Eval cbv in
    \"f"
       (\"x"
             (tag (Ref "type_check" @ (Ref "getTag" @ (Ref "f")) @ (Ref "getTag" @ (Ref "x")))
                  (untag @ (Ref "f") @  (untag @ (Ref "x")))
       )).

Print typed_app_aux.

Definition typed_app :=
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
           (△ @
            (△ @ (△ @ (△ @ (△ @ (△ @ getTag) @ (△ @ △ @ type_check))) @ (△ @ △ @ (△ @ △)))) @
            (△ @ △ @ (△ @ (△ @ getTag))))) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @ 
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
                  (△ @
                   (△ @
                    (△ @ (△ @ (△ @ △ @ (△ @ △))) @
                     (△ @ (△ @ (△ @ △ @ △)) @
                      (△ @
                       (△ @
                        (△ @ (△ @ (△ @ △ @ △)) @
                         (△ @ (△ @ (△ @ △ @ (△ @ △))) @
                          (△ @ (△ @ (△ @ △ @ △)) @
                           (△ @
                            (△ @
                             (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ (△ @ △) @ (△ @ △))))) @
                              (△ @ (△ @ (△ @ △ @ △)) @ △))) @ (△ @ △ @ △)))))) @ 
                       (△ @ △ @ △))))) @ (△ @ △ @ (△ @ △)))) @
                 (△ @ △ @
                  (△ @
                   (△ @
                    (△ @ (△ @ (△ @ △ @ (△ @ △))) @
                     (△ @ (△ @ (△ @ △ @ △)) @
                      (△ @
                       (△ @
                        (△ @ (△ @ (△ @ △ @ △)) @
                         (△ @ (△ @ (△ @ △ @ (△ @ △))) @
                          (△ @ (△ @ (△ @ △ @ △)) @
                           (△ @
                            (△ @
                             (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ (△ @ △) @ (△ @ △))))) @
                              (△ @ (△ @ (△ @ △ @ △)) @ △))) @ (△ @ △ @ △)))))) @ 
                       (△ @ △ @ △))))))))) @ (△ @ △ @ △))) @ (△ @ △ @ △)))) @ 
          (△ @ △ @ △))) @ (△ @ △ @ △)))) @ (△ @ △ @ (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ △)))))))) @
   (△ @ △ @ △))) @ (△ @ △ @ △))
.

Lemma typed_app_red:
  forall U T f u, program U -> typed_app @ (tag (Fun_ty U T) f) @ (tag U u) === tag T (f @ u).
Proof.  intros; unfold typed_app; eqtac; qtac getTag_tag; qtac type_check_red; tree_eq. Qed. 


  

(* 5.6: More Queries *)


Definition isStem2 :=  \"a" (△ @ (Ref "a") @ △ @ (K@(K@ △))).

Lemma isStem2_leaf: isStem2 @ △ === △.
Proof. tree_eq. Qed. 

Lemma isStem2_fork: forall w x, isStem2 @ (△@w@x) === △.
Proof. tree_eq. Qed. 

Lemma isStem2_stem: (* produces a fork *) 
  forall x, isStem2 @ (△ @ x) ===  △ @ (△ @ △ @ (△ @ △ @ △)) @ (x @ (△ @ △ @ (△ @ △ @ △))).
Proof. tree_eq. Qed. 



Definition isFork2 := \"z" (△ @ (Ref "z") @ (K@K) @ (K@(K@ △))).

Lemma isFork2_leaf: isFork2 @ △ === K@K.
Proof. tree_eq. Qed.

Lemma isFork2_stem: forall x, isFork2 @ (△@x) === K@(x@(K@(K@△))).
Proof. tree_eq.  Qed.

Lemma isFork2_fork: forall x y, isFork2 @ (△@ x@ y) === △. 
Proof. tree_eq.  Qed.



(* 5.7: Triage *)

Definition triage_comb :=
  \"m0"
       (\"m1"
             (\"m2"
                   (\"x"
                         (isStem @
                                 (Ref "x") @
                                 (△@((Ref "x") @△)@△ @ (\"y" (K@ ((Ref "m1") @ (Ref "y"))))) @
                                 (△@ (Ref "x") @ (Ref "m0") @ (Ref "m2"))
       )))).


Definition triage f0 f1 f2  :=
  (* 
  star
    "a"
    (△ 
       @ (isStem2 @ (Ref "a"))
       @ (△ @ (Ref "a") @ (Ref "f0") @ (Ref "f2"))
       @ (K@(K@ (△ @ (Ref "a" @ △) @ △ @ (\"x" ((K @ ((Ref "f1") @ (Ref "x"))))))))
    ).
   *)
  △ @
       (△ @
        (△ @
         (△ @
          (△ @
           (△ @
            (△ @ (△ @ (△ @ △ @ (△ @ (△ @ f1) @ (△ @ △ @ (△ @ △))))) @
             (△ @ (△ @ (△ @ △ @ △)) @
              (△ @ (△ @ (△ @ (△ @ (△ @ △ @ △)) @ (△ @ (△ @ △) @ (△ @ △)))) @ (△ @ △ @ △))))) @
           (△ @ △ @ (△ @ △)))) @ (△ @ △ @ (△ @ △)))) @
       (△ @ (△ @ (△ @ (△ @ (△ @ △ @ f2)) @ (△ @ (△ @ (△ @ △ @ f0)) @ △))) @
        (△ @ (△ @ (△ @ (△ @ (△ @ △ @ (△ @ △ @ (△ @ △ @ △)))) @ (△ @ (△ @ (△ @ △ @ △)) @ △))) @
         (△ @ △ @ △))). 


Lemma triage_leaf: forall M0 M1 M2, triage M0 M1 M2 @ △ === M0.
  Proof. tree_eq. Qed. 

Lemma triage_stem: forall M0 M1 M2 P, triage M0 M1 M2 @ (△@ P) === M1 @ P.
Proof. tree_eq. Qed. 

Lemma triage_fork: forall M0 M1 M2 P Q, triage M0 M1 M2 @ (△@ P@Q) === M2 @ P @Q.
Proof. tree_eq. Qed. 


Definition size_variant :=
  Y2
    (triage
          (K @ (K@ △))
          (\"y" (\"s" (K@ (Ref "s" @ Ref "y"))))
          (\"y" (\"z" (\"s" (K@ (plus@ (Ref "s" @ Ref "y") @ (Ref "s" @ Ref "z"))))))
    ).

Definition equal_variant :=
  Y2
    (triage
       (\"e" (triage K KI KI))
         (\"y" (\"e" (triage KI (Ref "e" @ Ref "y") (K@(K@KI)))))
          (\"y1"
             (\"y2"
                (\"e"
                  (triage
                     KI
                     (K@KI)
                     (\"z"
                       (\"z2"
                         (Ref "e"
                              @ Ref "y1"
                              @ Ref "z1"
                              @ (Ref "e" @ Ref "y2" @ Ref "z2")
                              @ KI
    )))))))).


(* 5.8: Pattern Matching *)



Definition leaf_case s :=
  Eval cbv in 
    substitute (\"r" (\"x" (isLeaf @ (Ref "x") @ (Ref "s") @ ((Ref "r" @ (Ref "x")))))) "s" s.


Definition stem_case f :=
  Eval cbv in 
    substitute
      (\"r"
         (\"x"
            (isStem
               @ (Ref "x") 
               @ (△
                    @ ((Ref "x") @△)
                    @ △
                    @ (\"y"
                         (K@
                           (Ref "f" 
                              @ (\"z" ((Ref "r") @ (△ @ (Ref "z"))))
                              @ (Ref "y")
                 )))) 
               @ ((Ref "r") @ (Ref "x"))
      )))
      "f" f.


Definition fork_case_r1 :=
    Eval cbv in 
    \"x1" (\"x2" (\"r1" (Ref "r1" @ (△ @ (Ref "x1") @ (Ref "x2"))))). 

Definition fork_case_r2 p1 :=
    Eval cbv in 
    substitute (\"x2" (\"r2" ((Ref "r2") @(△ @ Ref "p1" @ (Ref "x2"))))) "p1" p1.



Definition fork_case f :=
  Eval cbv in 
    substitute
      (\"r"
         (\"x"
             (isFork
                @ (Ref "x")
                @ (△
                     @ (Ref "x")
                     @△
                     @ (\"x1"
                          (\"x2"
                             (wait (Ref "f") fork_case_r1
                                   @ (Ref "x1")
                                   @ (Ref "x2")
                                   @ (Ref "r") 
                  ))))
                @ ((Ref "r") @ (Ref "x"))
      )))
      "f" f.



Fixpoint tree_case p s :=
  match p with
  | Ref x => K@ (\x s)
  | △ => leaf_case s
  | △@ p => stem_case (tree_case p s)
  | △@ p @ q => fork_case (tree_case p (wait (tree_case q (K@s)) (fork_case_r2 p)))
  | _ => I
  end.
          


Definition extension p s r := wait (tree_case p s) r. 



Lemma extension_leaf : forall s r, extension △ s r @ △ === s.
Proof.  tree_eq. Qed.

Lemma extension_leaf_stem :
  forall  s r u , extension △ s r @ (△@u) === r@ (△@u). 
Proof. tree_eq. Qed.

Lemma extension_leaf_fork: forall s r t u, extension △ s r @ (△@t@u) === r@ (△@t@u). 
Proof. tree_eq. Qed.

Lemma extension_stem_leaf: forall p s r, extension (△ @ p) s r @ △ === r @ △.
Proof. tree_eq. Qed. 

Lemma extension_stem: forall p s r u,
    extension (△ @ p) s r @ (△ @ u) === extension p s (△@ K @ (K@ r)) @ u. 
Proof. tree_eq. Qed. 

Lemma extension_stem_fork: forall p s r t u,
    extension (△ @ p) s r @ (△ @ t @ u) === r@ (△ @ t @ u).
Proof. tree_eq. Qed. 

Lemma extension_fork_leaf: forall p q s r, extension (△ @ p@q) s r @ △ === r @ △.
Proof. tree_eq. Qed. 

Lemma extension_fork_stem: forall p q s r u,
    extension (△ @ p@q) s r @ (△ @ u) === r@(△ @ u).
Proof. tree_eq. Qed. 

Lemma extension_fork: forall p q s r t u,
    extension (△ @ p@q) s r @ (△ @ t @ u) === 
    extension p (extension q (K@ s) (fork_case_r2 p)) fork_case_r1 @ t @ u @ r.
Proof. 
  intros;  unfold extension; fold extension; unfold tree_case; fold tree_case;
    unfold fork_case, fork_case_r1, fork_case_r2; unfold eq_q; 
  rewrite ! wait_red;  unfold wait; unfold_op; unfold d; eqtac; f_equal.   
Qed.



Lemma case_program: forall p, program p -> forall s r, extension p s r @ p === s.
Proof.
  intros p pr; induction pr; intros; unfold eq_q;   
  [ apply extension_leaf    
  | rewrite extension_stem; rewrite IHpr; auto | 
  rewrite extension_fork; qtac IHpr1; qtac IHpr2
    ]. 
Qed.

Ltac extensiontac :=
  repeat ((rewrite extension_fork || rewrite extension_stem || rewrite extension_leaf); eqtac). 

Ltac rule_tac :=
  unfold quotient; fold quotient; repeat (rewrite ? s_eq; rewrite ? k_eq; rewrite ? f_eq).

Lemma pattern_matching_example:
  extension (Y2 (Ref "xe")) (Ref "xe") I @ (Y2 K) === K.
Proof.
  unfold Y2, Z, wait, wait1, self_apply, d;  starstac ("x":: nil);  extensiontac. 
  unfold extension at 1; qtac wait_red; unfold tree_case.
  unfold stem_case; rule_tac.
  unfold fork_case; rule_tac.
  unfold leaf_case; rule_tac.
  unfold wait; unfold_op; rule_tac.
  unfold extension at 1; qtac wait_red; unfold tree_case.
  unfold wait; unfold_op; rule_tac.
  unfold fork_case; rule_tac.
  unfold stem_case; rule_tac.
  tree_eq.
Qed.


(* Exercises *)

(* 1 *)

Lemma size_succ: forall M,  size @ (K@ M) === K@(K@ (size @ M)).
Proof.
  intros; unfold_op; unfold eq_q; rewrite size_fork;
    do 3 rewrite quotient_app; rewrite size_leaf;
      do 2  rewrite <- quotient_app; rewrite plus_successor;
        rewrite quotient_app; rewrite plus_zero; auto.
Qed.

Fixpoint nat_to_tree n :=
  match n with
  | 0 => △
  | S n1 => K@ (nat_to_tree n1)
  end. 

Lemma size_nat: forall n, size @ (nat_to_tree n) === nat_to_tree (S(2*n)).
Proof.
  induction n; intros; simpl; unfold eq_q; [
    rewrite size_leaf; auto |
    rewrite size_succ; do 2 rewrite quotient_app; rewrite IHn; unquotient_tac; eqtac;
    repeat f_equal; lia
    ]. 
Qed.


(* 2 *)

Fixpoint tree_to_nat M :=
  match M with
  | △ => (0, △)
  | △ @ △ @ M1 =>
    match tree_to_nat M1 with (k,N) => (S k, N) end
  | _ => (0,M)
  end.


Lemma nat_to_nat : forall n, tree_to_nat (nat_to_tree n) = (n,Node).
Proof. induction n; intros; simpl; auto. rewrite IHn; auto. Qed.



Lemma plus_nat: forall m n, plus @ (nat_to_tree m) @ (nat_to_tree n) === nat_to_tree (m+ n).
Proof.
  induction m; intros; simpl; unfold eq_q;
    [rewrite plus_zero; auto |
     rewrite plus_successor; rewrite quotient_app; rewrite IHm; auto
    ].
Qed. 

Lemma size_of_program: forall p, program p -> size @ p === nat_to_tree (term_size p).
Proof.
  intros p pr; induction pr; intros; unfold eq_q, term_size; fold term_size; [
  rewrite size_leaf; auto | 
  rewrite size_stem; rewrite quotient_app; rewrite IHpr; simpl; auto |
  rewrite size_fork; do 3 rewrite quotient_app; rewrite IHpr1; rewrite IHpr2;
  unquotient_tac; rewrite quotient_app; rewrite plus_nat; simpl; auto
  ].
Qed.


Lemma size_W: size @ W === nat_to_tree 57. 
Proof.  unfold eq_q; rewrite size_of_program; auto; program_tac. Qed. 

 

(* 3 *)



(* Compute (term_size plus).  *) 

Lemma size_plus: size @ plus === nat_to_tree 156.
Proof.  unfold eq_q; rewrite size_of_program; auto; program_tac. Qed. 


(* Compute (term_size size).  *) 

Lemma size_size: size @ size === nat_to_tree 510.
Proof.  unfold eq_q; rewrite size_of_program; auto; program_tac. Qed. 


(* 4 *)

Lemma not_equal_K_KN: equal @ K @ (K @ Node) === KI.
Proof. apply unequal_programs; try discriminate; program_tac.  Qed.

(* 5 *)

Lemma equal_equal_equal: equal @ equal @ equal === K. 
Proof. apply equal_programs; program_tac.  Qed.


(* 6 *)
(* see the lemmas above *)

(* 7 *)


Definition typed_true := tag Bool_ty K.
Definition typed_false := tag Bool_ty KI.
Definition typed_conjunction :=
  tag (Fun_ty Bool_ty (Fun_ty Bool_ty Bool_ty)) (Node @ (Node @ (K @ KI))).

Lemma type_check_and_true_false :
  getTag @ (typed_app @ (typed_app @typed_conjunction @ typed_true) @ typed_false) === Bool_ty.
Proof.
  unfold typed_conjunction, typed_true, typed_false. repeat qtac typed_app_red; try (program_tac; fail).
  qtac getTag_tag.
Qed.


(* 8 *) 


Lemma size_variant_K: size_variant @ K === K @ (K @ Node).
Proof. unfold size_variant, K; qtac Y2_red; qtac triage_stem; tree_eq. Qed. 
  
(* 9 *)


Lemma equal_variant_K_KN: equal_variant @ K @ (K @ Node) === KI. 
Proof. unfold equal_variant, K; qtac Y2_red; qtac triage_stem;  tree_eq. Qed. 

(* 10 *) 

Definition size_pm :=
  Y2 (extension
        (Node @ Ref "x" @ Ref "y") (\"s" (K @ (Ref "plus" @ (Ref "s" @ Ref "x") @ (Ref "s" @ Ref "y"))))
        (extension
           (Node @ Ref "x") (\"s" (K @ (Ref "s" @ Ref "x")))
           (\"x" (\"s" (K @ Node)))
        )).

Lemma size_pm_K : size_pm @ K === K @ (K @ Node).
Proof.
  unfold size_pm. qtac Y2_red. unfold K. qtac extension_fork_stem. 
  qtac extension_stem. unfold extension at 1. qtac wait_red.
  unfold tree_case. qtac k_eq. rewrite (star_occurs_true _ _ "s"); auto; try discriminate.
 rewrite (star_occurs_true _ _ "s"); auto; try discriminate.
 rewrite (star_occurs_false _ "s"); auto; try discriminate.
 rewrite star_occurs_true; auto; try discriminate. qtac s_eq. 
 rewrite star_occurs_true; auto; try discriminate. qtac s_eq. 
 unfold star at 1; qtac k_eq.
 rewrite star_occurs_true; auto; try discriminate. qtac s_eq. 
 unfold star at 1; qtac k_eq.
 rewrite (star_occurs_false _ "s"); auto; try discriminate.
 rewrite (star_occurs_false _ "x"); auto; try discriminate.
 repeat qtac k_eq.
 rewrite star_occurs_true; auto; try discriminate. qtac s_eq.
 rewrite star_occurs_true; auto; try discriminate. qtac s_eq. 
 rewrite star_occurs_true; auto; try discriminate. qtac s_eq. 
 rewrite (star_occurs_false _ "x"); auto; try discriminate.
 repeat qtac k_eq.
 rewrite star_id.
 rewrite (star_occurs_false _ "x"); auto; try discriminate.
 repeat qtac k_eq.
 unfold I; qtac s_eq. qtac Y2_red. qtac extension_fork_leaf. qtac extension_stem_leaf.
 rewrite (star_occurs_false _ "s"); auto; try discriminate.
 rewrite (star_occurs_false _ "x"); auto; try discriminate.
 repeat qtac k_eq.
Qed.

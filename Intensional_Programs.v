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


Definition size:=
  Y2
    (\"s"
       (\"x"
          (isStem
             @ (Ref "x")
             @ (△
                  @ (Ref "x" @ △)
                  @ zero
                  @ (\"x1" (K @ (successor @ ((Ref "s") @ (Ref "x1")))))
               )
             @ (△
                  @ (Ref "x")
                  @ (successor @ zero)
                  @ (\"x1"
                       (\"x2"
                          (successor
                             @ (plus
                                  @ ((Ref "s") @ (Ref "x1"))
                                  @ ((Ref "s") @ (Ref "x2"))
    )))))))).


Lemma size_program: program size.
Proof. cbv; program_tac. Qed. 

Ltac sizetac :=
  intros; unfold size; rewrite Y2_red; fold size;
  starstac ("x2" :: "x1" :: "x" :: "s" :: nil);  unfold d; eqtac; auto.

Lemma size_leaf: size @ △ = successor @ zero. 
Proof. sizetac. Qed. 


Lemma size_fork:
  forall M N, size @ (△@ M@N) = successor @(plus @ (size @ M) @ (size @ N)).
Proof. sizetac. Qed. 

Lemma size_stem: forall M, size @ (△@ M) = successor @ (size @ M).
Proof. sizetac. Qed. 


(* 5.3: Equality *)

Definition equal_aux := 
  Eval cbv in 
  \"e"
       (\"x"
          (\"y"
             (isStem
                @ (Ref "x")
                @ (isStem
                     @ (Ref "y")
                     @ ((Ref "e")
                          @ (△ @ ((Ref "x") @ △) @ △ @ K)
                          @ (△ @ ((Ref "y") @ △) @ △ @ K)
                       )
                     @ KI
                  )
                @ (△
                     @ (Ref "x")
                     @ (isLeaf @ (Ref "y"))
                     @ (\"x1"
                          (\"x2"
                             (isFork
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

Definition equal := Y3 equal_aux. 

Lemma equal_program: program equal.
Proof. program_tac. Qed.

Ltac equaltac :=  unfold equal; rewrite Y3_red; fold equal; eqtac; unfold equal_aux; eqtac; auto.


Theorem equal_programs: forall M,  program M -> equal @ M @ M = K. 
Proof. intros M prM; induction prM; intros; equaltac; rewrite IHprM1; rewrite IHprM2; eqtac; auto. Qed.

Theorem unequal_programs:
  forall M,  program M -> forall N, program N -> M<> N -> equal @ M @ N = KI. 
Proof.
  intros M prM; induction prM; intros P prP neq; inversion prP; intros; subst;
    try congruence; equaltac. 
  apply IHprM; congruence.
  assert(d: M = M0 \/ M<> M0) by repeat decide equality;   inversion d; subst;
    [rewrite equal_programs; auto; eqtac; apply IHprM2; congruence
    | rewrite IHprM1; auto; eqtac; auto]. 
Qed.



(* 5.4: Tagging *)

Definition tag t f := Eval cbv in d t @ (d f @ (K@ K)).
Definition getTag := Eval cbv in \"p" (first ((first (Ref "p")) @ △)).
Definition untag := Eval cbv in \"x" (first ((first (second (Ref "x"))) @ △)). 



Lemma tag_apply : forall t f x, (tag t f) @ x = (f@x).
Proof.  tree_eq. Qed. 

Lemma getTag_tag : forall t f, getTag @ (tag t f) = t .
Proof.  tree_eq. Qed. 

Lemma untag_tag: forall t f, untag @ (tag t f) = f. 
Proof.  tree_eq. Qed. 


Theorem tree_calculus_support_tagging :
  exists tag getTag, (forall t f x, (tag t f) @ x = (f@ x)) /\
                      (forall t f,  getTag @ (tag t f) = t).
Proof. exists tag, getTag;  split; tree_eq. Qed.

(* tagging of fixpoint functions *)


Definition tag_wait t :=
  Eval cbv in
    substitute (\"g" (tag (Ref "t") (wait self_apply (Ref "g")))) "t" t.



Definition Y2_t t f := tag t (wait self_apply (d (tag_wait t) @ (K@f))). 


Lemma Y2_t_program: forall t f, program t -> program f -> program (Y2_t t f). 
Proof. intros; program_tac. Qed.


Theorem fixpoint_function : forall t f x, Y2_t t f @ x = f@ (Y2_t t f) @ x.
Proof. tree_eq. Qed.

Theorem getTag_Y2_t: forall t f, getTag @ (Y2_t t f) = t.
Proof. tree_eq. Qed. 




(* 5.5: Simple Types *)
(* leaf = error, stem = base type, fork = function type *) 

Definition error_ty := △.
Definition Bool_ty := △@ △.
Definition Nat_ty := △@ (△@ △).
Definition Fun_ty U T := △@ U @ T.


Definition typed T t := tag T t.

Definition type_check := (* maps U -> T and V to T or error *) 
  \"x"
       (\"v"
             (isFork @(Ref "x") @
                     (△@(Ref "x") @△@
                       (\"u" (\"t" (equal @ (Ref "u") @ (Ref "v")@ error_ty @ (Ref "t"))))
                       @ error_ty
       ))).

Definition typed_app :=
  \"f"
       (\"x"
             (tag (type_check @ (getTag @ (Ref "f")) @ (getTag @ (Ref "x")))
                  (untag @ (Ref "f") @  untag @ (Ref "x"))
       )).

(* 5.6: More Queries *)


Definition isStem2 :=  \"a" (△ @ (Ref "a") @ △ @ (K@(K@ △))).

Lemma isStem2_leaf: isStem2 @ △ = △.
Proof. tree_eq. Qed. 

Lemma isStem2_fork: forall w x, isStem2 @ (△@w@x) = △.
Proof. tree_eq. Qed. 

Lemma isStem2_stem: (* produces a fork *) 
  forall x, isStem2 @ (△ @ x) =  △ @ (△ @ △ @ (△ @ △ @ △)) @ (x @ (△ @ △ @ (△ @ △ @ △))).
Proof. tree_eq. Qed. 



Definition isFork2 := \"z" (△ @ (Ref "z") @ (K@K) @ (K@(K@ △))).

Lemma isFork2_leaf: isFork2 @ △ = K@K.
Proof. tree_eq. Qed.

Lemma isFork2_stem: forall x, isFork2 @ (△@x) = K@(x@(K@(K@△))).
Proof. tree_eq.  Qed.

Lemma isFork2_fork: forall x y, isFork2 @ (△@ x@ y) = △. 
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


Lemma triage_leaf: forall M0 M1 M2, triage M0 M1 M2 @ △ = M0.
  Proof. tree_eq. Qed. 

Lemma triage_stem: forall M0 M1 M2 P, triage M0 M1 M2 @ (△@ P) = M1 @ P.
Proof. tree_eq. Qed. 

Lemma triage_fork: forall M0 M1 M2 P Q, triage M0 M1 M2 @ (△@ P@Q) = M2 @ P @Q.
Proof. tree_eq. Qed. 


Definition size_variant :=
  Y2
    (\"s"
       (triage
          (K@ △)
          (\"y" (K@ (Ref "s" @ Ref "y")))
          (\"y" (\"z" (K@ (plus@ (Ref "s" @ Ref "y") @ (Ref "s" @ Ref "z")))))
    )).


Definition equal_variant :=
  Y3
    (\"e"
       (triage
          (triage K KI KI)
          (\"y" (triage KI (Ref "e" @ Ref "y") (K@(K@KI))))
          (\"y1"
             (\"y2"
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
  | _ => Id
  end.
          


Definition extension p s r := wait (tree_case p s) r. 



Lemma extension_leaf : forall s r, extension △ s r @ △ = s.
Proof.  tree_eq. Qed.

Lemma extension_leaf_stem :
  forall  s r u , extension △ s r @ (△@u) = r@ (△@u). 
Proof. tree_eq. Qed.

Lemma extension_leaf_fork: forall s r t u, extension △ s r @ (△@t@u) = r@ (△@t@u). 
Proof. tree_eq. Qed.

Lemma extension_stem_leaf: forall p s r, extension (△ @ p) s r @ △ = r @ △.
Proof. tree_eq. Qed. 

Lemma extension_stem: forall p s r u,
    extension (△ @ p) s r @ (△ @ u) = extension p s (△@ K @ (K@ r)) @ u. 
Proof. tree_eq. Qed. 

Lemma extension_stem_fork: forall p s r t u,
    extension (△ @ p) s r @ (△ @ t @ u) = r@ (△ @ t @ u).
Proof. tree_eq. Qed. 

Lemma extension_fork_leaf: forall p q s r, extension (△ @ p@q) s r @ △ = r @ △.
Proof. tree_eq. Qed. 

Lemma extension_fork_stem: forall p q s r u,
    extension (△ @ p@q) s r @ (△ @ u) = r@(△ @ u).
Proof. tree_eq. Qed. 

Lemma extension_fork: forall p q s r t u,
    extension (△ @ p@q) s r @ (△ @ t @ u) = 
    extension p (extension q (K@ s) (fork_case_r2 p)) fork_case_r1 @ t @ u @ r.
Proof. 
  intros;  unfold extension; fold extension; unfold tree_case; fold tree_case;
    unfold fork_case, fork_case_r1, fork_case_r2;
  rewrite ! wait_red;  unfold wait; unfold_op;
  starstac ("r1" :: "r2" :: "x2" :: "x1" :: "x" :: "r" :: nil); unfold d;  subst_tac; eqtac; f_equal.   
Qed.



Lemma case_program: forall p, program p -> forall s r, extension p s r @ p = s.
Proof.
  intros p pr; induction pr; intros;  
  [ apply extension_leaf    
  | rewrite extension_stem; rewrite IHpr; auto
  | rewrite extension_fork; rewrite IHpr1; rewrite IHpr2; tree_eq]. 
Qed.

Ltac extensiontac :=
  repeat ((rewrite extension_fork || rewrite extension_stem || rewrite extension_leaf); eqtac). 


Lemma pattern_matching_example:
  extension (Y2 (Ref "xe")) (Ref "xe") Id @ (Y2 K) = K.
Proof. 
  unfold Y2, wait, wait1, self_apply, d;  starstac ("x":: nil);  extensiontac;
  unfold extension at 1; rewrite wait_red; unfold tree_case; eqtac;  tree_eq. (* slow *) 
Qed.

(* 5.9 Eager Function Application *) 


Inductive factorable: Tree -> Prop :=
| factorable_leaf : factorable △
| factorable_stem: forall M, factorable (△@ M)
| factorable_fork: forall M N, factorable (△@ M @ N)
.

Hint Constructors factorable :TreeHintDb. 

Lemma programs_are_factorable: forall p, program p -> factorable p.
Proof. intros p pr; inversion pr; auto_t. Qed. 



Definition eager := \"z" (\"f" (△ @ (Ref "z") @ Id @ (K@KI) @ Id @ (Ref "f") @ (Ref "z"))). 


Lemma eager_of_factorable : forall M N, factorable M -> eager @ M @ N = N @ M.
Proof.   intros M N fac; inversion fac; cbv; eqtac; auto. Qed.


(* Exercises *)

(* 1 *)

Lemma size_succ: forall M,  size @ (K@ M) = K@(K@ (size @ M)).
Proof.
  intros; unfold_op; rewrite size_fork; rewrite size_leaf; rewrite plus_successor; rewrite plus_zero; auto.
Qed.

Fixpoint nat_to_tree n :=
  match n with
  | 0 => △
  | S n1 => K@ (nat_to_tree n1)
  end. 

Lemma size_nat: forall n, size @ (nat_to_tree n) = nat_to_tree (S(2*n)).
Proof.
  induction n; intros; simpl; [ rewrite size_leaf; auto | rewrite size_succ; rewrite IHn; repeat f_equal; lia].
Qed.


(* 2 *)

Fixpoint tree_to_nat M :=
  match M with
  | △ => (0, △)
  | △ @ △ @ M1 =>
    match tree_to_nat M1 with (k,N) => (S k, N) end
  | _ => (0,M)
  end.



Lemma size_W: tree_to_nat(size @ W) = (57,△). 
Proof.
  unfold W, bracket, d; subst_tac;  starstac ("y" :: "x" :: nil); 
  repeat (rewrite size_fork || rewrite size_stem || rewrite size_leaf);  
  repeat (  rewrite plus_successor || rewrite plus_zero); 
  cbv; auto. 
Qed. 

(* 3 *)

Lemma compare_succs: forall m n, m=n -> K@m = K@n.
Proof. intros; subst; auto. Qed. 

Ltac size_tac :=
  unfold_op; unfold nat_to_tree; 
  repeat (rewrite size_fork || rewrite size_stem || rewrite size_leaf);
  repeat ((rewrite plus_successor || rewrite plus_zero); try apply compare_succs);  auto. 

Lemma succ_nat: forall n, successor @ (nat_to_tree n) = nat_to_tree (S n).
Proof. auto. Qed. 

Lemma succ_nat2: forall n k, plus @ (nat_to_tree n) @ (successor @ k) = plus @ (nat_to_tree (S n)) @ k.
Proof.
  induction n; intros; simpl; 
  [ rewrite plus_zero;  rewrite plus_successor; rewrite plus_zero; auto
  | rewrite plus_successor; rewrite IHn; rewrite plus_successor; auto]. 
Qed. 

Lemma plus_nat: forall m n, plus @ (nat_to_tree m) @ (nat_to_tree n) = nat_to_tree (m+ n).
Proof. induction m; intros; simpl; [rewrite plus_zero; auto | rewrite plus_successor; rewrite IHm; auto]. Qed. 

(*
Compute (term_size plus).  *) 

Lemma size_plus: size @ plus = nat_to_tree 212.
Proof.
  unfold plus, Y3, self_apply, wait2, wait2_1, d; unfold_op;
  starstac ("x" :: "m1" :: "n" :: "m" :: "p" :: "f" :: "w" :: nil);  subst_tac; size_tac. 
Qed. 

(*
Compute (term_size size).  *) 

Lemma size_size: size @ size = nat_to_tree 560.
Proof.
  unfold size at 2. unfold Y2, wait, wait1, self_apply, d, zero; unfold_op; unfold d.
  starstac ("x2" :: "x1" :: "x" :: "s" :: "w" :: nil); subst_tac; size_tac. 
  rewrite size_plus. replace zero with (nat_to_tree 0) by auto.
  rewrite ! succ_nat. 
   assert (ss: size @ successor = nat_to_tree 2).
  unfold successor; unfold_op. rewrite size_stem; rewrite ! size_leaf; auto. rewrite ss.
  rewrite ! plus_nat.   rewrite ! succ_nat2.
  assert (s1: size @ (successor @ △) = nat_to_tree 3) . unfold successor, K.
  (rewrite size_fork; rewrite ! size_leaf). rewrite ! plus_successor. rewrite plus_zero. auto.
  rewrite s1. rewrite ! plus_nat. rewrite ! succ_nat2.  rewrite ! plus_nat. auto.
  Qed. 

(* 6 *)
(* see the lemmas above *)

(* 7 *)
 (* see the definitions above *) 

(* 8 *) 


Definition size_aux:=
  Y3 (\"s"
           (\"x"
                 (isStem
                    @ (Ref "x")
                    @ (△
                         @ ((Ref "x") @ △)
                         @ △
                         @ (\"x1" (K @ (Ref "s" @ (successor @ Ref "x") @ (Ref "x1"))))
                      )
                    @ (△ 
                         @ (Ref "y")
                         @ (successor @ Ref "x")
                         @ (\"y1" (Ref "s" @ (Ref "s" @ (Ref "x") @ (Ref "y1"))))
     )))).

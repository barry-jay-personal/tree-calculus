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
(*                    Chapter 7: Rewriting (theorems)                 *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)

Require Import Lia Bool List String.
Require Import Reflective.Rewriting_partI.


Set Default Proof Using "Type".

Open Scope string_scope.


(* new theorems that require rewriting *)


(* Confluence *)

(* Simultaneous Reduction *) 


Inductive s_red1 : Tree -> Tree -> Prop :=
| ref_sred : forall i, s_red1 (Ref i) (Ref i)
| node_sred : s_red1 △ △
| k_sred : forall M M' N, s_red1 M M' -> s_red1 (△@△@M@N) M' 
| s_sred: forall (M M' N N' P P': Tree), s_red1 M M' -> s_red1 N N' -> s_red1 P P' ->
                                         s_red1 (△@(△@P)@M@N) (M'@N'@(P'@N'))
| f_sred : forall (P P' Q Q' M N N': Tree), s_red1 P P' -> s_red1 Q Q' -> s_red1 N N' ->
                                            s_red1 (△@(△@P@Q)@M@N) (N'@P'@Q')
| app_sred : forall M M' N N', s_red1 M M' -> s_red1 N N' -> s_red1 (M@N) (M'@N')  
.
Hint Constructors s_red1 : TreeHintDb. 

Lemma s_red_refl: forall M, s_red1 M M.
Proof. induction M; intros; auto with TreeHintDb. Qed. 

Hint Resolve s_red_refl: TreeHintDb. 
     
Definition s_red := multi_step s_red1.

Lemma preserves_appl_s_red : preserves_appl s_red.
Proof. apply preserves_appl_multi_step. red; auto with *. Qed.

Lemma preserves_appr_s_red : preserves_appr s_red.
Proof. apply preserves_appr_multi_step. red; auto with *. Qed.

Lemma preserves_app_s_red : preserves_app s_red.
Proof. apply preserves_app_multi_step;  red; auto with *. Qed.


Definition implies_red (red1 red2: Tree-> Tree-> Prop) := forall M N, red1 M N -> red2 M N. 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (multi_step red1) (multi_step red2).
Proof. red. intros red1 red2 IR M N R; induction R; split_all; apply transitive_red with N; auto. Qed. 

Definition diamond (red1 red2 : Tree -> Tree -> Prop) := 
forall M N, red1 M N -> forall P, red2 M P -> exists Q, red2 N Q /\ red1 P Q. 

Lemma diamond_flip: forall red1 red2, diamond red1 red2 -> diamond red2 red1. 
Proof.  unfold diamond; intros red1 red2 d M N r1 P r2; elim (d M P r2 N r1); intros x ?; exist x. Qed.

Lemma diamond_strip : 
forall red1 red2, diamond red1 red2 -> diamond red1 (multi_step red2). 
Proof.
  intros red1 red2 d;  apply diamond_flip; 
    intros M N r; induction r; intros P0 r0; auto_t; 
      elim (d M P0 r0 N); auto; intros x (?&?); elim(IHr d x); split_all. 
Qed. 


Definition diamond_star (red1 red2: Tree -> Tree -> Prop) := forall  M N, red1 M N -> forall P, red2 M P -> 
  exists Q, red1 P Q /\ multi_step red2 N Q. 

Lemma diamond_star_strip: forall red1 red2, diamond_star red1 red2 -> diamond (multi_step red2) red1 .
Proof. 
  intros red1 red2 d M N r; induction r; intros P0 r0; auto_t;
    elim(d M P0 r0 N); auto; intros x (?&?);  
      elim(IHr d x); auto; intros x0 (?&?); exist x0; eapply2 transitive_red.
Qed. 

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.  induction n; split_all. Qed. 


Lemma diamond_tiling : 
forall red1 red2, diamond red1 red2 -> diamond (multi_step red1) (multi_step red2).
Proof. 
  intros red1 red2 d M N r; induction r as [ | red1 P P1 Q H]; intros P0 ?; auto_t;
    elim(diamond_strip red1 red2 d P P1 H P0); auto; intros x (?&?);
      elim(IHr d x); auto; intros x0 (?&?); exist x0.
Qed. 

Hint Resolve diamond_tiling: TreeHintDb. 






Theorem diamond_s_red1_s_red1 : diamond s_red1 s_red1. 
Proof.  
red; intros M N OR; induction OR; intros R s0; inv s_red1; auto_t.
(* 9 *)
match goal with | sM: s_red1 M ?M0 |- _ =>  
elim(IHOR M0); auto; intros M1 (r1&r2); exist M1 end. 
match goal with | sM: s_red1 M ?M0 , sN: s_red1 N ?N0,  sP: s_red1 P ?P0 |- _ =>  
elim(IHOR1 M0); auto; intros M1 (?&?);
  elim(IHOR2 N0); auto; intros N1 (?&?);
    elim(IHOR3 P0); auto; intros P1 (?&?); exist (M1 @ N1 @ (P1 @ N1)) end.
match goal with | sM: s_red1 M ?M0 , sN: s_red1 N ?N0,  sP: s_red1 P ?P0 |- _ =>  
elim(IHOR1 M0); auto; intros M1 (?&?);
  elim(IHOR2 N0); auto; intros N1 (?&?);
    elim(IHOR3 P0); auto; intros P1 (?&?);  exist (M1 @ N1 @ (P1 @ N1)) end.
match goal with | sP: s_red1 P ?P0 , sQ: s_red1 Q ?Q0,  sN: s_red1 N ?N0 |- _ =>  
elim(IHOR1 P0); auto; intros P1 (?&?);
  elim(IHOR2 Q0); auto; intros Q1 (?&?);
    elim(IHOR3 N0); auto; intros N1 (?&?); exist (N1 @ P1 @ Q1) end.
match goal with | sP: s_red1 P ?P0 , sQ: s_red1 Q ?Q0 , sN: s_red1 N ?N0 |- _ =>  
elim(IHOR1 P0); auto; intros P1 (?&?);
  elim(IHOR2 Q0); auto; intros Q1 (?&?);
    elim(IHOR3 N0); auto; intros N1 (?&?); exist (N1 @ P1 @ Q1) end.
inv s_red1; elim(IHOR1 (△ @ △ @ R)); auto with TreeHintDb; intros R1 (?&?); inv s_red1; inv s_red1;
  repeat eexists; [| eassumption]; eapply k_sred;  congruence.
match goal with
  | s0 : s_red1 (△ @ (△ @ ?P) @ ?M2) ?M', sP: s_red1 P ?P0, sM: s_red1 ?M2 ?M0, sN: s_red1 N ?N0 |- _ => 
    elim(IHOR1 (△ @ (△ @ P0) @ M0)); auto_t; intros R1 (?&?);  
      elim(IHOR2 N0);  auto_t; intros N1 (?&?); inv s_red1; inv s_red1; 
  repeat eexists; [| repeat apply app_sred; eauto]; auto_t end. 
match goal with
  | s0 : s_red1 (△ @ (△ @ ?P @ ?Q) @ ?M2) ?M', sP: s_red1 P ?P0, sQ: s_red1 Q ?Q0, sN: s_red1 N ?N0 |- _ => 
    elim(IHOR1 (△ @ (△ @ P0 @ Q0) @ M0)); auto_t; intros R1 (?&?);  
      elim(IHOR2 N0);  auto_t; intros N1 (?&?); inv s_red1; inv s_red1; 
  repeat eexists; [| repeat apply app_sred; eauto]; auto_t end. 
match goal with | sM: s_red1 M ?M0 , sN: s_red1 N ?N0 |- _ =>  
                  elim(IHOR1 M0); auto; intros M1 (?&?); elim(IHOR2 N0); auto; intros N1 (?&?); intros;
                    exist(M1 @ N1) end.
Qed.

  
Hint Resolve diamond_s_red1_s_red1: TreeHintDb.

Lemma diamond_s_red1_s_red : diamond s_red1 s_red.
Proof. apply diamond_strip; auto_t. Qed. 

Lemma diamond_s_red : diamond s_red s_red.
Proof.  apply diamond_tiling; auto_t. Qed. 
Hint Resolve diamond_s_red: TreeHintDb.



Lemma t_red1_to_s_red1 : implies_red t_red1 s_red1. 
Proof.  intros M N R; induction R; split_all. Qed. 


Lemma t_red_to_s_red: implies_red t_red s_red. 
Proof. 
apply implies_red_multi_step; red; intros; eapply succ_red; [eapply2 t_red1_to_s_red1 | zerotac].  
Qed. 

Lemma to_t_red_multi_step: forall red, implies_red red t_red -> implies_red (multi_step red) t_red. 
Proof. 
intros red B M N R; induction R; intros; [ zerotac |];
assert(t_red M N) by (apply B; auto); apply transitive_red with N; [ | apply IHR] ; auto. 
Qed. 


Lemma s_red1_to_t_red: implies_red s_red1 t_red .
Proof. 
  intros M N OR; induction OR; intros; zerotac;
    try (apply preserves_app_t_red; auto; fail); 
    eapply2 succ_red; 
    repeat apply preserves_app_t_red; auto. 
Qed.


Hint Resolve s_red1_to_t_red: TreeHintDb.

Lemma s_red_to_t_red: implies_red s_red t_red. 
Proof. eapply2 to_t_red_multi_step. Qed.


Lemma diamond_t_red: diamond t_red t_red. 
Proof. 
red; intros. 
assert(rMN: s_red M N) by (apply t_red_to_s_red; auto_t).  
assert(s_red M P) by (apply t_red_to_s_red; auto_t).  
elim(diamond_s_red M N rMN P); auto;  intros x (?&?); exist x; eapply2 s_red_to_t_red.
Qed. 
Hint Resolve diamond_t_red: TreeHintDb.



(* Confluence *)

Definition confluence (A : Set) (R : A -> A -> Prop) :=
  forall x y : A,
  R x y -> forall z : A, R x z -> exists u : A, R y u /\ R z u.

Theorem confluence_tree_calculus: confluence Tree t_red. 
Proof. apply diamond_t_red.  Qed.




Lemma programs_are_stable: forall M, program M -> forall N, s_red1 M N -> N = M.
Proof. intros M n; induction n; intros; inv s_red1; repeat f_equal; auto. Qed.


Lemma programs_are_stable2: forall M N, s_red M N -> program M -> N = M.
Proof.
  cut(forall red M N, multi_step red M N -> red = s_red1 -> program M -> N = M).
  intro c; intros; eapply c; eauto.  
  intros red M N r; induction r; intros; subst; zerotac. 
  assert(N = M) by (eapply programs_are_stable; eauto); subst; auto. 
  Qed.
  
Lemma t_red_preserves_stems:
  forall M N, t_red M N -> forall M0, M = △ @ M0 -> exists N0, N = △ @ N0 /\ t_red M0 N0.
Proof.
  cut (forall red M N, multi_step red M N -> red = t_red1 ->
                       forall M0, M = △ @ M0 -> exists N0, N = △ @ N0 /\ t_red M0 N0).
  intro H; intros; eapply H; eauto. 
  intros red M N r; induction r; intros e M0 eM; subst. 
  exist M0; zerotac. 
  inv t_red1. assert(H: exists N0, P = △ @ N0 /\ t_red N' N0) by (eapply IHr; eauto).
  elim H; clear H; intros ? (?&?); subst; eexists; split; [eauto | eapply2 succ_red].
Qed.

Lemma t_red_preserves_forks:
  forall M N, t_red M N -> forall M0 M1, M = △ @ M0 @ M1 ->
                                         exists N0 N1, N = △ @ N0 @ N1 /\ t_red M0 N0 /\ t_red M1 N1.
Proof.
  cut (forall red M N, multi_step red M N -> red = t_red1 ->
                       forall M0 M1, M = △ @ M0 @ M1 ->
                                     exists N0 N1, N = △ @ N0 @ N1 /\ t_red M0 N0 /\ t_red M1 N1).
  intro H; intros; eapply H; eauto. 
  intros red M N r; induction r; intros e M0 M1 eM; subst. 
  exists M0, M1; split_all; zerotac.
  { assert (e: t_red1 = t_red1) by reflexivity;  inv t_red1. 
  match goal with | r1: t_red1 M0 ?M2 |- _ =>  elim (IHr e M2 M1); auto end;
    intros Q ex; elim ex; intros Q1 ([=] & r1 & r2); subst; 
      exists Q, Q1; repeat split; zerotac;   succtac; zerotac.
  match goal with | r1: t_red1 M1 ?M2 |- _ =>  elim (IHr e M0 M2); auto end; 
    intros Q ex; elim ex; intros Q1 ([=] & r1 & r2); subst; 
      exists Q, Q1; repeat split; zerotac;   succtac; zerotac.
  }
Qed.


Lemma t_red_preserves_factorable: forall M N, t_red M N -> factorable M -> factorable N.
Proof.
  intros M N r fac; inversion fac; subst.
  {
  assert(N = △)  by (apply programs_are_stable2; [  apply t_red_to_s_red | apply pr_leaf]; auto);
    subst; auto. 
  }{
  assert(ex: exists Q, N = △ @ Q /\ t_red M0 Q) by (eapply t_red_preserves_stems; eauto);
    elim ex; intros Q (?&?); subst; auto_t. 
  }{
  assert(ex: exists Q1 Q2, N = △ @ Q1 @ Q2 /\ t_red M0 Q1 /\ t_red N0 Q2)
    by (eapply t_red_preserves_forks; eauto); 
    elim ex; split_all; subst; split_all.
  }
Qed.  


(* Counting reduction steps *) 


Inductive multi_ranked : (Tree -> Tree -> Prop) -> (nat -> Tree -> Tree -> Prop) :=
| zero_ranked : forall red M, multi_ranked red 0 M M
| succ_ranked : forall (red: Tree -> Tree -> Prop) M N n P,
    red M N -> multi_ranked red n N P -> multi_ranked red (S n) M P
. 

Hint Constructors multi_ranked : TreeHintDb.

Lemma multi_ranked_trans:
  forall red n M N, multi_ranked red n M N -> forall p P, multi_ranked red p N P -> multi_ranked red (n+p) M P. 
Proof.  induction n; intros M N rN p P rP; intros; inversion rN; subst; eauto; eapply2 succ_ranked. Qed. 


  
Lemma multi_ranked_iff_multi_red :
  forall (red : Tree -> Tree -> Prop) M N, multi_step red M N <-> exists n, multi_ranked red n M N.
Proof.
  intros red M N; split; intro r. 
  induction r. exist 0.
  elim IHr; intro k; exists (S k); eapply2 succ_ranked. 
  elim r; intros k r1.    generalize M N r1; clear.
  induction k ; intros; inversion r1; subst;  zerotac;   eapply2 succ_red.
Qed.


Lemma diamond_multi_ranked:
  forall red1 red2, diamond red1 red2 -> forall n, diamond (multi_ranked red1 n) red2.
Proof.
  intros red1 red2 d; induction n as [| n']; red; intros M N r P rP; inversion r; subst.
  exists P; auto_t.
  match goal with | Hr : red1 M ?N0 |- _ => elim (d M N0 Hr P rP); auto; intros x (Hx & ?); intros end.  
  match goal with
  | Hr : multi_ranked red1 n' ?N0 N, Hx : red2 ?N0 _ |- _ =>
    elim(IHn' _ _ Hr  _ Hx); auto; intro x1; intros (?&?)
  end. 
  exist x1; eapply2 succ_ranked. 
Qed.

Lemma diamond_multi_ranked2:
  forall red1 red2, diamond red1 red2 -> forall m n, diamond (multi_ranked red1 m) (multi_ranked red2 n).
Proof. intros; repeat (apply diamond_multi_ranked; apply diamond_flip); auto_t. Qed.


  



(* Halting Problem *)

Definition valuable M := exists P, t_red M P /\ program P.

Definition omega := △ @ (△ @ I) @ I.

Ltac stable_tac := inv1 program; match goal with | H : s_red1 ?Q ?R |- _ =>   assert(R=Q) by 
                                (apply programs_are_stable; cbv; program_tac); clear H end.

Lemma omega_omega_doesn't_halt:
  forall n h M, h < n -> multi_ranked s_red1 h (omega@ omega) M -> factorable M -> False.
Proof.
  induction n as [| n0]; intros h M hn r fac.  lia.
  inversion r; clear r; subst.
  unfold omega at 1 in fac; inv1 factorable. 
  match goal with | H : s_red1 (omega@omega) _ |- _ =>   unfold omega at 1 in H; inv s_red1 end.
  repeat stable_tac; subst. auto. 
  assert(r1: exists Q, s_red M Q /\ multi_ranked s_red1 n (omega@omega) Q). 
  eapply2 diamond_multi_ranked. eapply2 diamond_strip. 
  apply t_red_to_s_red;  trtac. elim r1;  intros Q (r2 & r3).   
  eapply2 (IHn0 n Q); eapply t_red_preserves_factorable; [  eapply2 s_red_to_t_red | auto].  
  {
  repeat stable_tac; subst.
  assert(r1: exists Q, s_red M Q /\ multi_ranked s_red1 n (omega@omega) Q). 
  eapply2 diamond_multi_ranked. eapply2 diamond_strip. eauto. 
  eapply t_red_to_s_red; trtac.
 elim r1;  intros Q (r2 & r3).   
 eapply2 (IHn0 n Q); eapply t_red_preserves_factorable; [eapply2 s_red_to_t_red | auto].
 }
Qed.



Lemma omega_omega_has_no_value: ~(valuable (omega @ omega)).
Proof.
  unfold valuable; intro v; elim v; clear v; intro P; intros (?&?).
  assert(ex:exists n, multi_ranked s_red1 n (omega @ omega) P). 
  apply multi_ranked_iff_multi_red; auto.   apply t_red_to_s_red; auto.
  elim ex; intros n r.   eapply omega_omega_doesn't_halt; eauto. apply programs_are_factorable; auto.
Qed.


Definition halting h :=
  forall M, (t_red (h @ M) K /\ valuable M) \/ (t_red (h @ M) KI /\ ~ (valuable M)).  

Definition self_negation :=  \"h" (\"f" ((Ref "h")@ ((Ref "f") @ (Ref "f")) @ (omega@omega) @ K)).  


Theorem halting_problem_insoluble : forall h, ~(halting h).
Proof.
  unfold halting; intro h; intro halt.
  assert(h1: t_red (h @ K) K /\ valuable K \/ t_red (h @ K) KI /\ ~ valuable K) by   apply halt. 
  inversion h1 as [ (r&v) | (r &nv) ]; clear h1.
  2: apply nv; unfold valuable; exists K; split; [zerotac | program_tac].

  assert(h2: t_red (h @ (omega @ omega)) K
             /\ valuable (omega @ omega) \/ t_red (h @ (omega @ omega)) KI
                                            /\ ~ valuable (omega @ omega)) by   apply halt. 
  inversion h2 as [ (r2&v2) | (r2 &nv2) ]; clear h2; intros. 
  apply  omega_omega_has_no_value; auto.

  assert (h3: (t_red (h @ (self_negation @ h @ (self_negation @ h))) K /\ valuable (self_negation @ h @ (self_negation @ h))) \/ (t_red (h @ (self_negation @ h @ (self_negation @ h))) KI /\ ~ (valuable (self_negation @ h @ (self_negation @ h))))) by 
  apply halt. 
  inversion h3 as [ (r3&v3) | (r3 &nv3) ]; clear h3; intros. 
  assert(h4: t_red ((self_negation @ h @ (self_negation @ h))) (omega@omega)).
  unfold self_negation at 1. starstac ("f" :: "h" :: nil). 
  ap2tac; zerotac; trtac.
  assert(t_red (h @  (self_negation @ h @ (self_negation @ h))) KI). 
  ap2tac; zerotac; trtac. auto. 
  assert(h5: exists Q, t_red K Q /\ t_red KI Q) by eapply2 diamond_t_red.
  elim h5; clear h5; intros Q (?&?). 
  assert(Q = K).  apply programs_are_stable2.  apply t_red_to_s_red; auto. program_tac. 
  assert(Q = KI).  apply programs_are_stable2.  apply t_red_to_s_red; auto. program_tac. 
  subst; discriminate. 
 
  assert( t_red ((self_negation @ h @ (self_negation @ h))) K).
  unfold self_negation at 1. starstac ("f" :: "h" :: nil). 
  ap2tac; zerotac; trtac.
  assert(t_red (h @  (self_negation @ h @ (self_negation @ h))) K). 
  ap2tac; zerotac; trtac. 
  assert(h5: exists Q, t_red K Q /\ t_red KI Q) by eapply2 diamond_t_red.
  elim h5; intros Q (?&?). 
  assert(Q = K) .  apply programs_are_stable2.  eapply2 t_red_to_s_red. program_tac. 
  assert(Q = KI) .  apply programs_are_stable2.  eapply2 t_red_to_s_red. program_tac. 
  subst; discriminate. 
Qed.



(* Standard Reduction *)



Fixpoint redexes M  :=
  (* counts the number of redexes currently available *) 
  match M with
  | Ref _ => 0
  | △ => 0
  | △ @ △ @ M @ N =>  S (redexes M + redexes N)
  | △ @ (△ @ P) @ M @ N =>  S (redexes P + redexes M + redexes N)
  | △ @ (△ @ P @ Q) @ M @ N => S (redexes P + redexes Q + redexes M + redexes N)
  | M @ N => redexes M + redexes N
  end.


Lemma applications_add_redexes: forall M N, redexes (M@N) >= redexes M + redexes N.
Proof.
  induction M as [ ? |  | M1 ]; intro N; simpl; auto;
  caseEq M1; [split_all | split_all | intros t t0; split_all];
  caseEq t; split_all;
  caseEq t0; [split_all | split_all | intros t1 ?; split_all]; 
  caseEq t1; [split_all | split_all | intros t3 ?; split_all]; 
  caseEq t3; split_all.  
Qed.


Definition irreducible M := forall N, t_red1 M N -> False.

Lemma programs_are_irreducible: forall M, program M -> irreducible M.
Proof. intros M prM; induction prM; intro; intro; auto; inv t_red1.  Qed. 

Lemma irreducible_no_redexes: forall N, irreducible N -> redexes N = 0.
Proof.
  induction N; intro irr; subst; simpl; auto;  caseEq N1.  
  { intros; subst; apply IHN2; intro; intro; eapply2 irr. }
  { intros [=]; simpl; apply IHN2; intro; intro; eapply2 irr. }
  {  intros t t0 [=]; subst;  caseEq t.
    1,2: intros; subst; auto; simpl in *; 
  rewrite IHN1; auto; [rewrite IHN2; auto |]; intro; intro; eapply2 irr.
   intros t1 t2 e; subst; rewrite IHN1; [ | intro; intro; eapply2 irr].
  assert(d: t1 = △ \/ t1 <> △) by repeat decide equality. 
  inversion d; subst; 
  [ | replace (match t1 with
  | △ =>
      match t2 with
      | △ => S (redexes t0 + redexes N2)
      | △ @ Q => S (redexes Q + redexes t0 + redexes N2)
      | △ @ P @ Q => S (redexes P + redexes Q + redexes t0 + redexes N2)
      | _ => 0 + redexes N2
      end
  | _ => 0 + redexes N2
           end)
    with (0 + redexes N2)
         by (caseEq t1; split_all); 
  rewrite IHN2; auto; intro; intro; eapply2 irr].

  Ltac aux H irr t := caseEq t; intros; subst;
    [ apply H; intro; intro; eapply2 irr | assert False by eapply2 irr; lia |  ]. 

  aux IHN2 irr t2; aux IHN2 irr t; aux IHN2 irr t2; rewrite IHN2; auto_t; intro; split_all. 
}Qed.

Lemma program_no_redexes: forall N, program N -> redexes N = 0.
Proof. intros; apply irreducible_no_redexes; apply programs_are_irreducible; auto. Qed. 


Lemma quaternary_redexes:
  forall M, combination M -> forall N P Q R, M = N @ P @ Q @ R -> redexes  M >0.
Proof.
  cut (forall p M, term_size M < p -> combination M ->
                   forall N P Q R, M = N@P@Q@R -> redexes  M >0).
  intro H; intros; eapply H; eauto. 
  induction p; intros M s c N P Q R e; subst. lia. 
  assert(cN:combination N) by (inv1 combination).
  inversion cN as [ | P1 Q1 d1 d2]; subst.
 (* 2 *)
  assert(cP: combination P) by (inv1 combination).
  inversion cP as [| M0 N0 c1 c2]; subst; auto. simpl; lia.
  inversion c1 as [ | M1 N1 c3 c4]; subst; auto. simpl; lia. 
  inversion c3 as [ | M2 N2]; subst; auto. simpl; lia.
  assert(redexes (M2 @ N2 @ N1 @ N0) >0) by ( eapply IHp; eauto; simpl in *; lia).
  simpl in *; lia.
  (* 1 *)
  assert(redexes (P1 @ Q1 @ P @ Q @ R) >= redexes (P1 @ Q1 @ P @ Q) + redexes R)
    by (eapply applications_add_redexes; eauto). 
   assert(term_size R >0) by apply size_positive.
  assert(redexes (P1 @ Q1 @ P @ Q) > 0) .  eapply IHp; auto_t.  simpl in *; lia. 
  combination_tac; inv1 combination.  
  lia.
Qed. 


Lemma no_redexes_program: forall N, redexes N = 0 -> combination N -> program N. 
Proof.
  induction N; intros; subst; auto; subst.
  (* 3 *)
  inv1 combination. 
  apply pr_leaf.
  (* 1 *)
  assert(cN1: combination N1) by inv1 combination.
  inversion cN1 as [| M0 N0 c1 c2]; subst. apply pr_stem. apply IHN2. simpl in *; lia.   inv1 combination.
  (* 1 *)
  inversion c1 as [| M1 N1 c3 c4]; subst. apply pr_fork. 
  assert(program (△ @ N0)). apply IHN1. simpl in *; lia. eauto.  inv1 program.
  apply IHN2. simpl in *; lia. inv1 combination. 
  assert(redexes (M1 @ N1 @ N0 @ N2) >0) . eapply quaternary_redexes; eauto. lia. 
Qed.

(* ready combinations *)

(* The proof of standardisation is adapted from the work of Ryo Kashima on lambda-calculus. *)

Inductive ready : Tree -> Prop :=
| kernelready: forall M, ready (△ @ △ @ M)
| stem_ready : forall M N, ready (△ @ (△ @ M) @ N)
| fork_ready : forall M N P, ready (△ @ (△ @ M @ N) @ P)
.

Hint Constructors ready :TreeHintDb.


Lemma ready_or_not: forall M, ready M \/ ~(ready M).
Proof.
  induction M; intros; subst; auto; try (right; intro H; inversion H; fail); subst. 
  inversion IHM1. right; intro. inv1 ready; subst; inv1 ready. 
  (* 1 *)
  case M1; intros; try (right; intro; inv1 ready; fail). 
  case t; intros; try (right; intro; inv1 ready; fail). 
  case t0; intros; try (right; intro; inv1 ready; fail). left; auto_t. 
  case t1; intros; try (right; intro; inv1 ready; fail). left; auto_t. 
  case t3; intros; try (right; intro; inv1 ready; fail). left; auto_t. 
Qed.


(* t_nred1 tags reductions with the number of overlooked reductions on the left *) 
  
Inductive t_nred1 : nat -> Tree -> Tree -> Prop :=
| kernel_nred : forall M N, t_nred1 0 (△ @ △ @ M @ N) M
| stem_nred : forall M N P,  t_nred1 0 (△ @ (△ @ P) @ M @ N) (M@N @ (P @ N))
| fork_nred : forall M N P Q,  t_nred1 0 (△ @ (△ @ P @ Q)@ M@ N) (N@P@ Q) 
| not_factorable_nred:forall M M' N P, ~(factorable M) -> t_nred1 0 M M' ->
                                       t_nred1 0 (△ @ M @ N@ P) (△ @ M' @ N@ P)
| appl_unready : forall n M M1 N, t_nred1 n M M1 -> ~(ready M) -> t_nred1 n     (M@N) (M1 @ N)
| appl_ready : forall n M M1 N, t_nred1 n M M1 -> ready M -> t_nred1 (S n)  (M@N) (M1 @ N)
| appr_unready : forall n M N N1, t_nred1 n N N1 -> ~(ready M) -> t_nred1 (n + redexes M)     (M@N) (M@N1)
| appr_ready   : forall n M N N1, t_nred1 n N N1 ->   ready M  -> t_nred1 (S (n+redexes M)) (M@N) (M@N1)
.

Lemma t_nred1_to_t_red1: forall n M N, t_nred1 n M N -> t_red1 M N.
Proof.  intros n M N r; induction r; split_all. Qed. 
  

(* l_red is leftmost reduction (since nothing has been overlooked) *) 

Inductive seq_red : nat -> Tree -> Tree -> Prop :=
| zero_seq_red : forall m M, m<= redexes M -> seq_red m M M
| succ_seq_red: forall n n1 M N P,  n <= n1 -> t_nred1 n M N -> seq_red n1 N P -> seq_red n1 M P
.

Definition l_red := seq_red 0.

Hint Constructors ready t_nred1 seq_red :TreeHintDb.

Lemma seq_red_to_t_red : forall n M N, seq_red n M N -> t_red M N.
Proof.
  intros n M N r; induction r; intros; zerotac. 
  eapply succ_red; eauto. eapply t_nred1_to_t_red1; eauto.
Qed. 

Theorem l_red_to_t_red: forall M N, l_red M N -> t_red M N.
Proof. apply seq_red_to_t_red. Qed. 
  
Lemma l_red_transitive: forall M N, l_red M N -> forall P, l_red N P -> l_red M P.
Proof.
  cut (forall n M N, seq_red n M N -> n = 0 -> forall P, l_red N P -> l_red M P).
  intro H; intros; auto. eapply H; eauto. 
  intros n M N r; induction r; intros; subst; auto.  
  eapply2 succ_seq_red; eapply2 IHr.
Qed.

  

(* basic properties *)

Lemma seq_red_redexes: forall n M N, seq_red n M N -> n <= redexes N.
Proof.  intros n M N r; induction r; auto. Qed.


Lemma seq_red_preserves_ready: forall n M N, seq_red n M N -> ready M -> ready N.
Proof.
  intros n M N r; induction r as [r1 | ? ? ? ? ? ? tr]; intro rdy; auto. apply IHr.  clear - rdy tr.
  (* now the result for t_nred1 *)
  inversion rdy; subst; inv (t_nred1 n); inv1 ready; inv (t_nred1 n1); inv1 ready. 
Qed.



Lemma seq_red_app:
  forall M M1, seq_red (redexes M1) M M1 ->
               forall N N1, seq_red (redexes N1) N N1 ->
                            seq_red (redexes (M1 @ N1)) (M@N) (M1 @ N1).
Proof.
  intros M M1 s; induction s as [| n1 n2 M N P lt r1 s0];  intros N0 N1 s1; subst; auto.
  (* 2 *)
  induction s1 as [| n0 n1 N P Q]; subst; auto_t.
  assert(rM: ready M \/ ~(ready M)) by apply ready_or_not. 
  assert(rQ: n1 <= redexes Q). eapply seq_red_redexes. eauto. 
  inversion rM as [rM1 | rm2]; subst.
  (* 3 *) 
  eapply succ_seq_red; [| |eauto]; [| eapply2 appr_ready];  inversion rM1; subst; simpl; lia.
  (* 2 *) 
  eapply succ_seq_red; [| | eauto]; [| eapply2 appr_unready].
  caseEq M; intros t; intros; subst; simpl; auto; try lia. 
  caseEq t; intros t1; subst; simpl; auto; try lia.  intros r0 e. 
  caseEq t1; intros t2; subst; simpl; auto; try lia. 
  caseEq r0; intros t; subst; simpl; auto; try lia. intros t1 [=].
  caseEq t; intros t2; subst; simpl; auto; try lia. intros t3 [=]. 
  caseEq t2; intros; subst; simpl; auto; try lia. 
  (* 1 *)
  assert(rM: ready M \/ ~(ready M)) by eapply ready_or_not.   
  inversion rM.
  all: cycle 1. 
  (* 2 *)
  eapply succ_seq_red; [ | eapply appl_unready; eassumption | auto]. 
  assert(n2 <= redexes P) by (eapply seq_red_redexes; eauto);
  assert(redexes (P @ N1) >= redexes P + redexes N1) by apply  applications_add_redexes; lia. 
  (* 1 *) 
  eapply succ_seq_red; [| | eapply IHs0; eassumption]; [ | eapply appl_ready; eauto].
  assert(rP: ready P) . eapply seq_red_preserves_ready; auto. 
  eapply succ_seq_red; eauto.  auto. 
  assert(n2 <= redexes P) by (eapply seq_red_redexes; eauto).
  inversion rP; subst; simpl in *; lia.
Qed.


(* hap performs head reduction *)

Inductive hap1 : Tree -> Tree -> Prop :=
| hap_kernel : forall M N, hap1 (△ @ △ @ M @ N) M
| hap_stem : forall P M N, hap1 (△ @ (△ @ P) @ M @ N) (M@N @ (P@ N))
| hap_fork : forall P Q M N, hap1 (△ @ (△ @ P @ Q) @ M @ N) (N@P@ Q)
| hap_app : forall M N P,  hap1 M N -> hap1 (M@ P) (N@ P)
| hap_ready: forall M M' N P, hap1 M M' -> hap1 (△ @ M @ N@ P) (△ @ M' @ N@ P)
.

Definition hap := multi_step hap1.



Lemma hap1_functional: forall M N, hap1 M N -> forall P, hap1 M P -> N=P.
Proof.
  intros M N r; induction r; intros P0 rP; inv hap1; subst; inv hap1;
    repeat f_equal; apply IHr; auto.
Qed.


(* st_red allows nested head reductions, but always moving to the right *) 

Inductive st_red : Tree -> Tree -> Prop :=
| st_ref : forall M i, hap M (Ref i) -> st_red M (Ref i)
| st_node : forall M, hap M △ -> st_red M △
| st_app : forall M N N1 P P1, hap M (N@ P) -> st_red N N1 -> st_red P P1 -> st_red M (N1 @P1)
.


Hint Constructors  hap1 st_red :TreeHintDb.

Lemma hap_preserves_appr: forall M N P, hap M N -> hap (M@ P) (N@ P).
Proof.
  cut(forall red M N P, multi_step red M N -> red = hap1 -> hap (M@ P) (N@ P));
  [split_all |
  intros red M N P r; induction r; split_all; subst;
    [ zerotac | eapply succ_red; [ eapply2 hap_app | eapply2 IHr]]].   
Qed.


Lemma hap_ready_multi:
  forall M M' N P, hap M M' -> hap (△ @ M @ N @ P) (△ @ M' @ N @ P).
Proof.
  cut (forall red M M',
          multi_step red M M' -> red = hap1 -> 
          forall N P, hap (△ @ M @ N @ P) (△ @ M' @ N @ P));
  [ split_all |
  intros red M M' r; induction r; intros; subst;
  [ zerotac  |  eapply succ_red; [ eapply2 hap_ready | eapply2 IHr]]].
Qed.


Lemma st_red_refl: forall M, st_red M M.
Proof. induction M; split_all; [ apply st_ref | apply st_node | eapply2 st_app]; zerotac. Qed.

Lemma hap_then_st_red: forall N M, hap M N -> forall P, st_red N P -> st_red M P.
Proof.
  intros M N H P st; inversion st; subst; [eapply2 st_ref | eapply2 st_node |  eapply2 st_app];
     (eapply transitive_red; [ eexact H |]; auto_t). 
Qed.


Lemma st_kernel_red :
  forall M N P,  st_red M (△ @ △ @ N @ P) -> st_red M N.
Proof.
  intros M N P st; inv st_red. 
  eapply hap_then_st_red. 2: eassumption. 
  eapply transitive_red. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr.
  eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. apply hap_ready_multi; eauto. eapply2 succ_red. 
Qed.

Lemma st_stem_red :
  forall M N P Q,  st_red M (△ @ (△ @ N) @ P @ Q) -> st_red M (P@Q @(N@Q)).
Proof.
  intros M N P Q H.  inv st_red.   eapply hap_then_st_red.
  (* 2 *)
  eapply transitive_red. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr.
  eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_ready_multi. eassumption.
  eapply transitive_red. eapply hap_ready_multi. eapply hap_preserves_appr. eassumption. 
  eapply succ_red;  auto_t.
  (* 1 *)
  eapply st_app. zerotac. eapply st_app. zerotac. auto. auto. eapply st_app. zerotac. auto. auto.
Qed.

Lemma st_fork_red :
  forall M N R P Q,  st_red M (App (App (△ @ (△ @ N @ R)) P) Q) -> st_red M (Q@N@ R).
Proof.
  intros M N R P Q H; inv st_red.   eapply hap_then_st_red.
  (* 2 *)
  eapply transitive_red. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_preserves_appr. eapply hap_preserves_appr.
  eapply hap_preserves_appr. eassumption. 
  eapply transitive_red. eapply hap_ready_multi. eassumption.
  eapply transitive_red. eapply hap_ready_multi. eapply hap_preserves_appr. eassumption.
  eapply transitive_red. eapply hap_ready_multi. eapply hap_preserves_appr. eapply hap_preserves_appr.
  eassumption.
  eapply2 succ_red.
  (* 1 *)
  eapply st_app. zerotac. eapply st_app. zerotac. all: auto. 
Qed.

(* comparing and combining the relations *) 

Lemma hap1_implies_t_nred1: forall M N, hap1 M N -> t_nred1 0 M N.
Proof.
  intros M N h; induction h; simpl; split_all.
  apply appl_unready; auto. intro r; inversion r; subst; inversion h; subst; inv hap1.
  apply appl_unready; auto. apply appl_unready; auto.
  replace 0 with (0+ (redexes △)) by auto.
  apply appr_unready; auto.
  all: intro r; inversion r; subst; inv hap1.   
Qed.

Lemma hap_implies_l_red: forall M N, hap M N -> l_red M N.
Proof.
  cut(forall red M N, multi_step red M N  -> red = hap1 -> l_red M N).
  intro H; intros; eapply H; eauto.
  intros red M N r; induction r; simpl; subst; intros; auto; subst.
  (* 2 *)
  apply zero_seq_red; lia.
  (* 1 *) 
  eapply succ_seq_red; [| eapply hap1_implies_t_nred1; eauto | eauto]; [lia | eapply2 IHr]. 
Qed.


Lemma hap_then_seq_red: forall M N,  hap M N -> forall n P, seq_red n N P -> seq_red n M P.
Proof.
  cut(forall red M N, multi_step red M N -> red = hap1 ->
                      forall n P, seq_red n N P -> seq_red n M P).

  intro H; intros; eapply H; eauto.
  intros red M N r; induction r; intros; subst; auto. 
  eapply succ_seq_red; [| | eapply2 IHr]; [| eapply2 hap1_implies_t_nred1]; lia. 
  Qed.

Lemma st_red_implies_seq_red: forall M N, st_red M N -> seq_red (redexes N) M N.
Proof.
intros M N st; induction st; intros; auto;
  try (apply hap_implies_l_red; auto; fail);
  eapply2 hap_then_seq_red; eapply2 seq_red_app.   
Qed.

Ltac inv_st_red :=
  match goal with
  | H : st_red _ Node |- _ => inversion H; clear H; subst; inv_st_red
  | H : st_red _ (Node @ _) |- _ => inversion H; clear H; subst; inv_st_red
  | H : st_red _ (Node @ _ @ _) |- _ => inversion H; clear H; subst; inv_st_red
  | H : st_red _ (_@_ @ _ @ _) |- _ => inversion H; clear H; subst; inv_st_red
  | _ => split_all
  end.

Lemma st_red_then_t_nred1: forall n N P, t_nred1 n N P -> forall M, st_red M N -> st_red M P. 
Proof.
  intros n N P r; induction r; intros ? s;
    try (inv_st_red; try inversion s; subst; eapply2 st_app; auto_t; fail); 
[eapply st_kernel_red | eapply st_stem_red | eapply st_fork_red]; auto_t.
Qed.


(* proofs below work from the other end of the reduction sequence *)

Inductive t_red_rev : Tree -> Tree -> Prop :=
| zero_t_red : forall M, t_red_rev M M
| succ_t_red : forall M N n P, t_red_rev M N -> t_nred1 n N P -> t_red_rev M P.

Hint Constructors t_red_rev :TreeHintDb.


Lemma transitive_t_red_rev :
  forall N P,  t_red_rev N P -> forall M, t_red_rev M N -> t_red_rev M P. 
Proof.
intros N P r; induction r; intros; auto. 
eapply succ_t_red. eapply IHr; auto. eauto.
Qed.

Lemma t_red1_implies_t_nred1:
  forall M N, t_red1 M N -> exists n, t_nred1 n M N.
Proof.
  induction M; intros N r; auto; inversion r; subst; auto_t. 
   (* 2 *)
  assert(ex: exists n, t_nred1 n M1 M') by (eapply IHM1; eauto). 
  inversion ex; subst. 
  assert(rM: ready M1 \/ ~(ready M1)) by apply ready_or_not.
  inversion rM; auto_t.  
  (* 1 *)
  assert(ex: exists n, t_nred1 n M2 N') by (eapply IHM2; eauto). 
  inversion ex; subst.
  match goal with | H : t_red1 (?M1 @ _) _ |- _ =>
                    assert(rM1: ready M1 \/ ~(ready M1)) by apply ready_or_not;
                      inversion rM1; auto_t
  end.
Qed.

Lemma t_red_implies_t_red_rev:
  forall M N, t_red M N -> t_red_rev M N.
Proof.
  cut (forall red M N, multi_step red M N -> red = t_red1 -> t_red_rev M N).
  intro H; intros; eapply H; auto_t.        
  intros red M N r; induction r; intros; subst; auto_t. eapply transitive_t_red_rev. 
  eapply IHr. auto. 
  assert(ex: exists n, t_nred1 n M N) by (eapply t_red1_implies_t_nred1; eauto). 
  inversion ex; auto_t.
Qed.

Lemma t_red_rev_st_red : forall M N, t_red_rev M N -> st_red M N.
Proof.
  intros M N r; induction r; intros; subst; auto. 
  (* 2 *)
  apply st_red_refl. 
  (* 1 *) 
  eapply st_red_then_t_nred1; eauto. 
Qed.

Lemma t_red_st_red : forall M N, t_red M N -> st_red M N.
Proof.  intros; apply t_red_rev_st_red;  apply t_red_implies_t_red_rev; auto. Qed.

(* the standardization theorem *)


Theorem standardization : forall M N, t_red M N -> seq_red (redexes N) M N.
Proof.  intros; apply st_red_implies_seq_red; apply t_red_st_red; auto. Qed. 


Corollary leftmost_reduction:
  forall M N, t_red M N -> program N -> l_red M N. 
Proof.
  intros M N r pr.
  assert(seq_red (redexes N) M N) by (eapply standardization; eauto).
  assert(r0: redexes N = 0) by (eapply program_no_redexes; eauto).
  rewrite r0 in *; auto. 
Qed. 

Theorem head_reduction_to_factorable_form:
  forall M N, t_red M N -> factorable N -> exists Q, hap M Q /\ factorable Q /\ t_red Q N. 
Proof.
  intros M N r fac.
  assert(st: st_red M N) by (eapply t_red_rev_st_red; eapply t_red_implies_t_red_rev; eauto). 
  inversion st; subst; inv1 factorable; subst.
  (* 2 *)
  match goal with | st: st_red _ Node |- _ =>  inversion st; subst end.
  exists (△ @P); repeat split_all.
  eapply transitive_red. eassumption. apply hap_preserves_appr; auto. 
  apply preserves_app_t_red. zerotac.
  eapply seq_red_to_t_red. apply st_red_implies_seq_red; auto_t.
  (* 1 *) 
  match goal with | st: st_red _ (Node @ _) |- _ =>  inversion st; subst end.
  match goal with | st: st_red _ Node |- _ =>  inversion st; subst end.
  match goal with | hap1: hap M (?N0 @ ?P), hap2: hap ?N0 (N@ ?P0) |- _ => exists (△ @P0@P) end.
  repeat split_all.
  eapply transitive_red. eassumption. apply hap_preserves_appr.
  eapply transitive_red. eassumption.  apply hap_preserves_appr; auto. 
  repeat apply preserves_app_t_red; eapply seq_red_to_t_red;
    apply st_red_implies_seq_red; auto_t. apply st_node; zerotac. 
Qed.



(* Lemmas for self-evaluators *) 


Ltac irrtac :=
  match goal with
  | pr: program ?M , r: t_red1 ?M _ |- _ =>
    assert False by (eapply (programs_are_irreducible M); eauto); lia
  | _ => idtac
  end. 

Ltac s_red_program_tac :=
  match goal with
    | H : program ?P, H1: s_red1 ?P ?Q |- _ => assert(Q=P) by apply programs_are_stable; clear H1; s_red_program_tac
    | H : program ?P, H1: s_red ?P ?Q |- _ => assert(Q=P) by apply programs_are_stable2; clear H1; s_red_program_tac
    | _ => idtac
  end. 
 
         
Ltac invsub := 
match goal with 
| H : _ = _ |- _ => inversion H; subst; clear H; invsub 
| _ => split_all 
end. 

Lemma program_application_t_red1 :
  forall M N, t_red1 M N ->
              forall M1 M2, M = M1 @ M2 -> program M1 -> program M2 -> hap1 M N.
Proof.
  intros M N r; induction r; intros M1 M2 e pr1 pr2; invsub; auto_t; inv t_red1; irrtac.    
Qed.

Lemma program_application2_t_red1 :
  forall M N, t_red1 M N ->
              forall M1 M2 M3, M = M1 @ M2 @ M3 -> program M1 -> program M2 -> program M3 -> hap1 M N.
Proof.
  intros M N r; induction r; intros M1 M2 M3 e pr1 pr2 pr3; invsub; inv t_red1; auto_t; irrtac. 
Qed.

Lemma program_application3_t_red1 :
  forall M N, t_red1 M N ->
              forall M1 M2 M3 M4, M = M1 @ M2 @ M3 @ M4 ->
                                  program M1 -> program M2 -> program M3 -> program M4 -> hap1 M N.
Proof.
  intros M N r; induction r; intros M1 M2 M3 M4 e pr1 pr2 pr3; invsub; inv t_red1; auto_t;
    irrtac.
Qed.

Lemma program_application_s_red1 :
  forall M N, s_red1 M N ->
              forall M1 M2, M = M1 @ M2 -> program M1 -> program M2 -> M= N \/ hap1 M N.
Proof.
  intros M N r; induction r; intros M1 M2 e pr1 pr2; invsub; auto_t; inv s_red1; inv1 program;
    subst; s_red_program_tac; subst;  auto_t;  repeat stable_tac; subst; auto_t. 
Qed.

Lemma program_application2_s_red1 :
  forall M N, s_red1 M N ->
              forall M1 M2 M3, M = M1 @ M2 @ M3 -> program M1 -> program M2 -> program M3 -> M= N \/ hap1 M N.
Proof.
  intros M N r; induction r; intros M1 M2 M3 e pr1 pr2 pr3; invsub; auto_t; inv s_red1; inv1 program; subst; s_red_program_tac; subst;  auto_t; repeat stable_tac; subst; auto_t.  
 Qed.

Lemma program_application3_s_red1 :
  forall M N, s_red1 M N ->
              forall M1 M2 M3 M4, M = M1 @ M2 @ M3 @ M4 ->
                                  program M1 -> program M2 -> program M3 -> program M4 -> M= N \/ hap1 M N.
Proof.
  intros M N r; induction r; intros M1 M2 M3 e pr1 pr2 pr3; invsub; auto_t; inv s_red1; inv1 program; subst; s_red_program_tac; subst;  auto_t; repeat stable_tac; subst; auto_t.  
 Qed.


Lemma program_application_multi :
  forall n M N, multi_ranked s_red1 (S n) M N ->
                forall M1 M2, M = M1 @ M2 -> program M1 -> program M2 ->
                              M= N \/ exists Q, hap1 M Q /\ multi_ranked s_red1 n Q N.
Proof.
  induction n; intros M N r M1 M2 e prM1 prM2; subst.
    inversion r as [ | ? ? P0 ? ? s0 s1]; clear r; inversion s1; subst; 
      elim(program_application_s_red1 _ _ s0 M1 M2); auto; intro h;  inversion h; subst; auto_t.
    inversion r as [ | ? ? P ? ? s0 s1]; clear r; subst. 
 elim(program_application_s_red1 _ _ s0 M1 M2); intros; subst; auto.
  elim(IHn _ _ s1 M1 M2);  auto_t;  intros ex.  elim ex; intros Q (?&?).
  right; exist Q; eapply2 succ_ranked.
  right; exist P.
 Qed.

Lemma program_application2_multi :
  forall n M N, multi_ranked s_red1 (S n) M N ->
                forall M1 M2 M3, M = M1 @ M2 @ M3 -> program M1 -> program M2 ->program M3 ->
                                 M= N \/ exists Q, hap1 M Q /\ multi_ranked s_red1 n Q N.
Proof.
  induction n; intros M N r M1 M2 M3 e prM1 prM2 prM3; subst.
    inversion r as [ | ? ? P0 ? ? s0 s1]; clear r; inversion s1; subst; 
      elim(program_application2_s_red1 _ _ s0 M1 M2 M3); auto; intro h;  inversion h; subst; auto_t.
    inversion r as [ | ? ? P ? ? s0 s1]; clear r; inversion s1; subst. 
    elim(program_application2_s_red1 _ _ s0 M1 M2 M3); intros; subst; auto.
  elim(IHn _ _ s1 M1 M2 M3);  auto_t.  intro ex; elim ex; intros Q (?&?).
  right; exist Q; eapply2 succ_ranked.
  right; exist P.
 Qed.

Lemma program_application3_multi :
  forall n M N, multi_ranked s_red1 (S n) M N ->
                forall M1 M2 M3 M4, M = M1 @ M2 @ M3 @ M4 ->
                                    program M1 -> program M2 ->program M3 -> program M4 -> 
                                 M= N \/ exists Q, hap1 M Q /\ multi_ranked s_red1 n Q N.
Proof.
  induction n; intros M N r M1 M2 M3 M4 e prM1 prM2 prM3 prM4; subst.
    inversion r as [ | ? ? P0 ? ? s0 s1]; clear r; inversion s1; subst; 
      elim(program_application3_s_red1 _ _ s0 M1 M2 M3 M4); auto; intro h;  inversion h; subst; auto_t.
    inversion r as [ | ? ? P ? ? s0 s1]; clear r; inversion s1; subst. 
    elim(program_application3_s_red1 _ _ s0 M1 M2 M3 M4); intros; subst; auto.
  elim(IHn _ _ s1 M1 M2 M3 M4);  auto_t.  intro ex; elim ex; intros Q (?&?).
  right; exist Q; eapply2 succ_ranked.
  right; exist P.
 Qed.


(* Identifying the needed argument *)

Lemma factorable_decidable:  forall M, factorable M \/ ~ factorable M.
Proof.
  intro; caseEq M; intros; subst; auto_t; [  right; intro; inv1 factorable |]. 
  caseEq t; intros; subst; auto_t;[  right; intro; inv1 factorable |]. 
  caseEq t1; intros; subst; auto_t; right; intro; inv1 factorable.
Qed.


Lemma substitution_preserves_s_red1:
  forall M N, s_red1 M N -> forall x U, s_red1 (substitute M x U) (substitute N x U).
Proof.  intros M N r; induction r; intros x U; intros; simpl; auto_t. Qed. 

Lemma substitution_preserves_s_red:
  forall M N, s_red M N -> forall x U, s_red (substitute M x U) (substitute N x U).
Proof.
  cut(forall n M N, multi_ranked s_red1 n M N ->
                    forall x U, multi_ranked s_red1 n (substitute M x U) (substitute N x U)).
  intro H; intros.
  assert(ex: exists n, multi_ranked s_red1 n M N) by (eapply multi_ranked_iff_multi_red; eauto).  
   elim ex; intros; eauto.  eapply multi_ranked_iff_multi_red; eauto; eapply H; eauto. 
   induction n; intros M N r; inversion r; clear r; subst; split_all.
   eapply succ_ranked; eauto. apply substitution_preserves_s_red1. auto.
Qed.

Definition reflexive (red: Tree -> Tree -> Prop) := forall M, red M M.

Lemma multi_ranked_of_reflexive:
  forall red, reflexive red ->
              forall n m, m <= n -> forall M N, multi_ranked red m M N -> multi_ranked red n M N.
Proof.
  intros red refl; induction n; intros m rel M N r; subst; inversion r; clear r; subst; auto_t.
  lia.   eapply succ_ranked; auto_t. apply IHn with 0. lia. auto_t.
   eapply succ_ranked; eauto. apply IHn with n0; auto.  lia. 
Qed. 


Inductive next : Tree -> Tree -> Prop :=
| next_arg : forall M N P , next (△ @ M @ N @ P) M
| next_app: forall R P M, next R M -> next (R@P) M
.

Inductive active : Tree -> Tree -> Prop :=
| active_one : forall M N , next M N -> active M N 
| active_succ: forall R P M,  next R P -> active P M -> active R M
.

Hint Constructors next active: TreeHintDb.

Lemma active_app: forall M N, active M N -> forall P, active (M@P) N.
Proof.
  intros M N a; induction a; intros; [ eapply active_one | eapply active_succ]; auto_t.
Qed. 
  

Lemma next_not_factorable: forall R M, next R M -> ~ factorable R.
Proof.
  intros R M nx; induction nx; intros; subst; intro; inv1 factorable; subst;
    eapply IHnx; auto_t.
Qed.

Lemma active_not_factorable: forall R M, active R M -> ~ factorable R.
Proof.
  intros R M nx; induction nx; intros; subst; intro; inv1 factorable; subst;
    eapply next_not_factorable; auto_t. 
Qed.

Ltac nnf_tac :=
  match goal with
  | H: active ?R _ |- _ => try (absurd (factorable R); auto_t;
                              apply next_not_factorable ||  clear H; nnf_tac || fail)
  | _ => idtac                                                                                                          end.

Lemma next_app3: forall R M, active R M -> forall N P Q, R = △ @ N @ P @ Q -> N=M \/ active N M.
Proof. intros R M nx; induction nx; intros R1 P1 Q1 e; invsub; inv next. Qed.


Lemma next_combination: forall R M, next R M -> combination R -> combination M. 
Proof.  intros R M nx; induction nx; intro c; inv1 combination.  Qed. 

Lemma active_combination: forall R M, active R M -> combination R -> combination M. 
Proof.
  intros R M nx; induction nx; intro c; inv1 combination. eapply next_combination; auto_t.
  apply IHnx.  eapply next_combination; eauto. 
Qed.


Lemma substitution_preserves_next:
  forall R M, next R M -> forall s U, next (substitute R s U) (substitute M s U). 
Proof. intros R M nx; induction nx; intros; simpl; auto_t. Qed. 


Lemma substitution_preserves_active:
  forall R M, active R M -> forall s U, active (substitute R s U) (substitute M s U). 
Proof.
  intros R M nx; induction nx; intros; simpl; eauto; [ eapply active_one | eapply active_succ]; eauto;
    eapply substitution_preserves_next; auto.
Qed. 


Fixpoint head_term M :=
  match M with
  | M1 @ M2 => head_term M1
  | M1 => M1
  end.

Lemma  s_red_preserves_head_ref: forall M N s, s_red M N -> head_term M = Ref s -> head_term N = Ref s.
Proof.
  cut(forall n s M N, multi_ranked s_red1 n M N -> head_term M = Ref s -> head_term N = Ref s).
  intro H; intros; eauto.
  assert(ex: exists n, multi_ranked s_red1 n M N) by (eapply multi_ranked_iff_multi_red; eauto).
  elim ex; intros; eapply H; eauto.
  induction n; intros s M N r h; inversion r; subst; eauto.
  eapply IHn; eauto. 
  match goal with
  | s1: s_red1 M ?N0 |- _ => clear - h s1; induction s1; intros; simpl in *; auto;  discriminate end.
Qed.

Lemma next_head: forall R M, next R M -> head_term R = △.
Proof.  intros R M nx; induction nx; intros; auto. Qed.   

Lemma active_head: forall R M, active R M -> head_term R = △.
Proof.  intros R M nx; induction nx; intros; eapply next_head; eauto. Qed.   


Lemma next_s_red1:
  forall R M,  next R M -> forall R1, s_red1 R R1 -> factorable M \/ exists M1, s_red1 M M1 /\ next R1 M1. 
Proof.
  intros R M nx; induction nx; intros R1 r; inversion r; clear r; subst; inv s_red1; inv next;
    auto_t; nnf_tac. 
  elim(IHnx M'); eauto; intro ex; elim ex; intros Q (?&?); right; exists Q; split; auto_t. 
Qed.

Lemma active_s_red1:
  forall R M,  active R M -> forall R1, s_red1 R R1 ->
                                        factorable M \/ exists M1, s_red1 M M1 /\ active R1 M1. 
Proof.
  intros R M nx; induction nx as [ N N0 nx0 | ]; intros R1 r.
  (* 2 *)
  inversion r as [| | | | | M0 ? ? ? s0 s1]; clear r; subst; inv s_red1; inv next; inv s_red1; auto_t;  
  eelim(next_s_red1 M0 N0); [ | | assumption | eassumption]; auto_t; 
  intro ex; elim ex; intros Q (?&?);
    right; exists Q; split; auto; eapply active_one; auto_t.
  (* 1 *)
  inversion r as [| | | | | M0 ? ? ? ? s0 s1]; clear r; subst; inv s_red1; inv next; inv s_red1; auto_t;   
  try (inversion nx; intros; subst; inv next; fail).
  (* 2 *)
  eelim IHnx; [ | |  eauto]; split_all. 
  (* 1 *)
  eelim(next_s_red1 M0 P);  [ | | assumption | eassumption]; auto_t. 
  intro; absurd(factorable P); auto; eapply2 active_not_factorable.
  intro ex; elim ex; intros M1 (?&?); elim(IHnx M1); auto;
  intro ex1; elim ex1; intros M2 (?&?);
    right; exists M2; split; auto; eapply active_app; eapply active_succ; eauto.
Qed. 
  

Lemma active_s_red_factorable:
  forall n R M Q, multi_ranked s_red1 n R Q -> active R M -> factorable Q ->
                    exists M1 , multi_ranked s_red1 n M M1 /\ factorable M1 . 
Proof.
  induction n; intros R M Q r nx fac; inversion r; clear r; subst.
  absurd (factorable Q); auto; eapply active_not_factorable; eauto. 
  assert(or1: factorable M \/ exists M1, s_red1 M M1 /\ active N M1) by (eapply active_s_red1; eauto). 
  inversion or1 as [facM | ex]; clear or1; intros.
  exists M; split; eauto; eapply succ_ranked; auto_t.
  eapply (multi_ranked_of_reflexive s_red1 s_red_refl n 0); auto_t; lia.
  elim ex; intros M0 (s&a).
  assert(ex2 : exists (M1 : Tree) , multi_ranked s_red1 n M0 M1 /\ factorable M1) by (eapply IHn; eauto).
  elim(ex2); intros M2 (s2 & facM1). 
  exists M2; split; eauto; eapply succ_ranked; eauto. 
Qed.


Definition needs R M := exists N, s_red R N /\ active N M. 

Lemma needy_not_factorable: forall R M, needs R M ->  ~ factorable R.
Proof.
  intros R M nd; intro fac; unfold needs in *; intros; elim nd; intros N (s&a);
    eapply active_not_factorable; eauto; eapply t_red_preserves_factorable; eauto;
      apply s_red_to_t_red; auto.
Qed.


Lemma needy_app: forall R M, needs R M -> forall N, needs (R@ N) M.
Proof.
  intros R M nd; induction nd as [x (s&a)]; intro N; eauto.
  exists (x@N); split; [ apply preserves_app_s_red; zerotac| apply active_app; auto]. 
Qed.   


Lemma needy_s_red_factorable:
  forall n R M Q, multi_ranked s_red1 n R Q -> factorable Q -> needs R M ->
                  exists  M1,  multi_ranked s_red1 n M M1 /\ factorable M1. 
Proof.
  intros n R M Q r fac nd; unfold needs in nd. elim nd; intros N (s&a). 
  assert(ex: exists Q1, s_red Q Q1  /\ multi_ranked s_red1 n N Q1)  by  
  (eapply diamond_multi_ranked ; eauto; eapply diamond_s_red1_s_red; eauto); intros.
  elim ex; intros Q1 (s1&s2).
  assert(ex2: exists M1, multi_ranked s_red1 n M M1 /\ factorable M1 ) 
    by (eapply active_s_red_factorable;  eauto; eapply t_red_preserves_factorable;
        [eapply s_red_to_t_red |]; eauto).
elim ex2; intros M1 (s3 & facM).    exists M1; eauto.
Qed.


Lemma triage_needy: forall f0 f1 f2 M , needs (triage f0 f1 f2 @ M) M. 
Proof. intros;  unfold triage;  repeat eexists; [ eapply t_red_to_s_red; trtac | auto_t]. Qed. 

Lemma eager_needy:  forall M N, needs (eager @ M @N) M. 
Proof. intros; cbv; repeat eexists; [ eapply t_red_to_s_red; trtac |  auto_t]. Qed. 

Lemma bf_needy:  forall M N, needs (bf @ M @ N) M. 
Proof. intros N; repeat eexists; [  cbv;  eapply t_red_to_s_red; trtac |  auto_t]. Qed. 



Theorem bf_to_branch_first_eval: 
  forall M N P, t_red (bf @ M @ N) P -> program M -> program N -> factorable P ->
                            exists Q, branch_first_eval M N Q /\ t_red P Q .
Proof.
  (* need to control the rank   *) 
  cut(forall n h M N P, multi_ranked s_red1 h (bf @ M @ N) P ->
                            program M -> program N -> factorable P -> h<n -> 
                            exists Q, branch_first_eval M N Q /\ s_red P Q) ;
  [intros ? M N P r prM prN fac;
  assert(mr1: exists n, multi_ranked s_red1 n  (bf @ M @ N) P) by 
  (apply multi_ranked_iff_multi_red; eapply2 t_red_to_s_red);
  elim mr1; intros n mr2;  assert(n < S n) by lia;  elim(H (S n) n _ _ _ mr2); auto;
  intros val (b&s); exists val; split; eauto; eapply s_red_to_t_red; eauto
  |].
 
  induction n; intros h M N P r prM prN fac hn; [lia |]. 
  inversion prM as [| | M0 M1 prM0 prM1]; clear prM.
  { (* M is a leaf *)
  assert(bf1: t_red (bf @ M @ N) (M @ N)) by (subst; aptac; [apply bf_leaf_red | zerotac | zerotac]);  
  assert(dp1: exists Q, s_red P Q /\ s_red (M @ N) Q) by
  (eapply diamond_s_red; [eapply2 multi_ranked_iff_multi_red | eapply2 t_red_to_s_red]);
  elim dp1; clear dp1; intros P1 (?&?);
    assert(P1 = M @ N) by (subst; apply programs_are_stable2; eauto; eapply pr_stem; eauto);
    subst;  exist (△ @ N).
  }{ (* M is a stem *) 
  assert(bf1: t_red (bf @ M @ N) (M @ N)) by (subst; aptac; [apply bf_stem_red | zerotac | zerotac]);   
  assert(dp1: exists Q, s_red P Q /\ s_red (△ @ M0 @ N) Q) by
  (subst; eapply diamond_s_red; [eapply2 multi_ranked_iff_multi_red | eapply2 t_red_to_s_red]);
  elim dp1; clear dp1; intros P1 (?&?);
  assert(P1 = △ @ M0 @ N) by  (apply programs_are_stable2; auto; apply pr_fork; auto); subst;
    exist (△ @ M0 @ N).
  }{ (* M is a fork, so examine its left branch *)
   caseEq h;
     [ intros [=] | intros h' [=]]; inversion r; subst; inv1 factorable; [lia | invsub].
   inversion prM0  as [| M2 prM2 | M2 M3 prM2 prM3]; clear prM0; subst; auto_t. 
  { 
  exist M1; 
  assert(dp1: exists Q, s_red P Q /\ s_red M1 Q) by 
      (eapply diamond_s_red;
       [eapply multi_ranked_iff_multi_red | eapply t_red_to_s_red; apply bf_fork_leaf_red]; eauto); 
  elim dp1; clear dp1; intros P1 (?&?);  
  assert(P1 = M1) by (apply programs_are_stable2; auto); subst; auto. 
  }
  all: cycle 1. (* do forks first *)
  { (* the upper square in Figure 7.4 *) 
  inversion r as [ | ? ? P0 ? ? s0]; clear r; subst; inv1 factorable. 
  elim(program_application2_s_red1 _ _ s0 bf (△ @ (△ @ M2 @ M3) @ M1) N); clear s0; intros; auto; subst;
  [ eapply2 IHn; program_tac | | apply program_bf | program_tac]. 
  assert(bf1: t_red (bf @ (△ @ (△@ M2@M3) @ M1) @ N) (bf@ (bf @ N@M2)@M3 )) by apply bf_fork_fork_red. 
  assert(mr1: exists n, multi_ranked t_red1 n  (bf @ (△ @ (△ @ M2 @ M3) @ M1) @ N) (bf @ (bf @ N @ M2) @ M3))
    by (eapply multi_ranked_iff_multi_red; eauto).
  elim mr1; clear mr1; intros k bfr1. 
  caseEq k;
     [ intros [=] | intros k' [=]]; subst; 
    [ inversion bfr1 | inversion bfr1 as [ | ? ? P1 ? ? s1]]; clear bfr1; subst; inv1 factorable. 
  assert(hap1 (bf @ (△ @ (△ @ M2 @ M3) @ M1) @ N) P1) by
      (eapply program_application2_t_red1; eauto; [apply program_bf | program_tac]).
  assert(P1 = P0) by (eapply hap1_functional; eauto); subst. 
  assert(dp1: exists Q, s_red P Q /\ multi_ranked s_red1 h'  (bf @ (bf @ N @ M2) @ M3) Q) . 
  eapply diamond_multi_ranked. eapply diamond_s_red1_s_red. eauto. eapply t_red_to_s_red.  
  apply multi_ranked_iff_multi_red; eauto.
  elim dp1; clear dp1; intros P1 (?&?).  
  assert(factorable P1) by  (eapply t_red_preserves_factorable; [apply s_red_to_t_red |]; eauto). 
  (* the lower square in Figure 7.4 *) 
  assert(bfr2: exists Q, multi_ranked s_red1 h' (bf @ N @ M2) Q /\ factorable Q) by
  (eapply needy_s_red_factorable; eauto; apply bf_needy).
  elim bfr2; clear bfr2; intros Q0 (?&?).
  assert(eval1: exists Q : Tree, branch_first_eval N M2 Q /\ s_red Q0 Q) by (eapply2 IHn; lia). 
  elim eval1; clear eval1; intros Q2 (?&?).
  assert(t_red (bf@N@M2) Q2) by eapply2 branch_first_eval_to_bf.
  assert(program Q2) by eapply2 branch_first_program. 
  assert(dp3: exists Q, t_red Q2 Q /\ t_red Q0 Q)
   by (eapply2 diamond_t_red; apply s_red_to_t_red; eapply2 multi_ranked_iff_multi_red).  
  elim dp3; clear dp3; intros Q (?&?).
  assert (Q = Q2) by (eapply2 programs_are_stable2; eapply2 t_red_to_s_red); subst.
  assert(dp4: exists Q, s_red P1 Q /\ multi_ranked s_red1 h'  (bf @ Q2 @ M3) Q).
  eapply diamond_multi_ranked. apply diamond_s_red1_s_red. eauto. 
  apply t_red_to_s_red;   ap2tac; zerotac.
  elim dp4; clear dp4; intros P2 (?&?). 
  (* Finally ... *) 
  assert(eval2: exists Q : Tree, branch_first_eval Q2 M3 Q /\ s_red P2 Q).  eapply2 IHn.
  eapply t_red_preserves_factorable. apply s_red_to_t_red. eauto. auto.
  elim eval2; clear eval2; intros P3 (?&?).
  exists P3; split; [eapply2 e_fork_fork | repeat eapply2 transitive_red].   
  }{ (*  stems  *)
  (* the upper square in Figure 7.5 *) 
  inversion r as [ | ? ? P0 ? ? s0]; clear r; subst; inv1 factorable. 
  elim(program_application2_s_red1 _ _ s0 bf (△ @ (△ @ M2) @ M1) N);  intros; clear s0; eauto; subst; 
    [eapply2 IHn; program_tac |  | apply program_bf | program_tac].   
  assert(bf1: t_red (bf @ (△ @ (△@ M2) @ M1) @ N) (eager @ (bf @ M2 @ N) @ (bf @ (bf @ M1 @ N))))
    by apply bf_fork_stem_red.
  assert(mr1: exists n, multi_ranked t_red1 n (bf @ (△ @ (△@ M2) @ M1) @ N) (eager @ (bf @ M2 @ N) @ (bf @ (bf @ M1 @ N))))
    by (eapply multi_ranked_iff_multi_red; eauto).
  elim mr1; clear mr1; intros k mr2. 
  caseEq k; intros; subst; [ inversion mr2 | inversion mr2 as [ | ? ? Q0 ? ? ?]]; clear mr2; subst.  
  assert(hap1 (bf @ (△ @ (△ @ M2) @ M1) @ N) Q0). eapply2 program_application2_t_red1. 
  apply program_bf. program_tac.
  assert(Q0 = P0) by eapply2 hap1_functional; subst. 
  assert(dp1: exists Q, s_red P Q /\ multi_ranked s_red1 h'  (eager @ (bf @ M2 @ N) @ (bf @ (bf @ M1 @ N))) Q). 
  eapply diamond_multi_ranked. apply diamond_s_red1_s_red. eauto. apply t_red_to_s_red.
  apply multi_ranked_iff_multi_red; eauto.
  elim dp1; clear dp1; intros P1 (?&?). 
  assert(factorable P1) by (eapply t_red_preserves_factorable; eauto; eapply2 s_red_to_t_red). 
(* the middle square in Figure 7.5 *) 
  assert(nd1: exists M3, multi_ranked s_red1 h' (bf @ M2 @ N) M3 /\ factorable M3) by
  (eapply needy_s_red_factorable;  eauto; apply eager_needy).
  elim nd1; clear nd1; intros P_MN (?&?).
  assert(eval1: exists Q : Tree, branch_first_eval M2 N Q /\ s_red P_MN Q) by (eapply2 IHn; lia). 
  elim eval1; clear eval1; intros Q2 (?&?).
  assert(t_red (bf@M2 @ N) Q2) by eapply2 branch_first_eval_to_bf.
  assert(program Q2) by eapply2 branch_first_program. 
  assert(dp2: exists Q, s_red P1 Q /\ multi_ranked s_red1 h'  (bf @ (bf @ M1 @ N) @ Q2) Q).
  eapply diamond_multi_ranked. apply diamond_s_red1_s_red. eauto. 
  apply t_red_to_s_red; ap2tac; zerotac; apply eager_of_factorable; eapply2 programs_are_factorable.  
  elim dp2; clear dp2; intros P2 (?&?). 
  assert(factorable P2) by (eapply t_red_preserves_factorable; [ apply s_red_to_t_red | ]; eauto). 
  (* the lower square in Figure 7.5  *)
  assert(nd2: exists  Q, multi_ranked s_red1 h' (bf @ M1 @ N) Q /\ factorable Q) . 
  eapply needy_s_red_factorable; eauto; apply bf_needy.
  elim nd2; clear nd2; intros Q (?&?). 
  assert(eval2: exists Q3 : Tree, branch_first_eval M1 N Q3 /\ s_red Q Q3) by (eapply2 IHn; lia). 
  elim eval2; clear eval2; intros Q3 (?&?).
  assert(t_red (bf @ M1 @ N) Q3) by (eapply branch_first_eval_to_bf; eauto).
  assert(program Q3) by (eapply branch_first_program; eauto).
  assert(dp3: exists Q, s_red P2 Q /\ multi_ranked s_red1 h'  (bf @ Q3 @ Q2) Q).
  eapply diamond_multi_ranked. apply diamond_s_red1_s_red. eauto. 
  eapply t_red_to_s_red. ap2tac; zerotac. 
  elim dp3; clear dp3; intros P3 (?&?).
  (* Finally ... *)
  assert(eval3: exists Q : Tree, branch_first_eval Q3 Q2 Q /\ s_red P3 Q)  by
  (eapply2 IHn; eapply t_red_preserves_factorable; [ eapply2 s_red_to_t_red | auto]). 
  elim eval3; clear eval3; intros val (?&?).
  exists val; split; eauto; [ eapply2 e_fork_stem | repeat eapply2 transitive_red].
  }
  }
Qed.


Corollary branch_first_eval_iff_bf :
  forall M N P, program M -> program N -> program P ->  t_red (bf @ M @ N) P <-> branch_first_eval M N P. 
Proof.
  intros M N P pM pN pP; split; intro r;
    [ assert(bfe: exists Q, branch_first_eval  M N Q /\ t_red P Q)
        by (eapply bf_to_branch_first_eval; eauto; apply programs_are_factorable; auto);   
      elim bfe; clear bfe; intros x (bf1&r1);
      assert(x=P)  by (eapply programs_are_stable2; eauto; apply t_red_to_s_red; auto);  subst; auto
      | eapply branch_first_eval_to_bf; eauto]. 
Qed.


  

(* Root evaluation *)



Lemma onFork_needy: forall f M , needs (onFork f @ M) M. 
Proof.
  intros;  unfold onFork;  repeat eexists;
    [eapply t_red_to_s_red; trtac
    | eapply active_succ; auto_t; eapply active_one; eauto].
Qed.

Ltac root1_tac :=
  replace root1
  with (\"t"(\"y"(\"r1"(triage rootl roots rootf @ (Ref "r1" @ Ref "t") @ (Ref "r1") @ (Ref "y"))))) by auto;
  starstac ("r1" :: "y" :: "t" :: nil). 


Lemma root1_needy: forall M N P, needs (root1 @ M @ N @ P) (P @M). 
Proof.
  intros M N P;
  elim(triage_needy rootl roots rootf (P@M)); intros x H;  inversion H; 
    exists (x@ P @ N);  split;
      [eapply t_red_to_s_red;   root1_tac ; 
       assert(t_red (triage rootl roots rootf @ (P @ M)) x) by eapply2 s_red_to_t_red; 
       ap2tac; zerotac |
       repeat eapply2 active_app].  
Qed.

Lemma root_needy: forall M, needs (root @ M) M. 
Proof.
  intros; repeat eexists; [
    eapply t_red_to_s_red; unfold root; eapply transitive_red;
      [ apply Y2_red
      | fold root]; unfold root_aux; trtac 
    | eapply2 active_one].
Qed.


Lemma root_aux_red :
  forall M1 M2, t_red(root_aux @ (Node @ M1 @ M2) @ root) (onFork root1 @ (root @ M1) @ root @ M2).
Proof.
  replace root_aux with  (\"a"(\"r"(△ @ Ref "a" @ △ @ (\"f"(onFork root1 @ (Ref "r" @ Ref "f") @ (Ref "r")))))) by auto.
  intros. starstac ("f" :: "r" :: "a" :: nil). 
Qed.


Theorem root_to_root_eval_factorable:
  forall M P, t_red (root @ meta_quote M) P -> combination M -> factorable P ->
                            exists Q, root_eval (meta_quote M) Q /\ t_red P Q .
Proof.
  cut(forall n h, h < n ->
                  forall M P, multi_ranked s_red1 h (root @ (meta_quote M)) P ->
                              combination M -> factorable P -> 
                              exists Q, root_eval(meta_quote M) Q /\ s_red P Q).
  intro c; intros M P r cM fac;
  assert(mr1: exists n, multi_ranked s_red1 n  (root @ meta_quote M) P) by 
  (apply multi_ranked_iff_multi_red; eapply2 t_red_to_s_red); 
  elim mr1; clear mr1; intros n mr2; 
  assert(lt: n < S n) by lia; 
  elim(c (S n) n lt _ _ mr2); auto; intros val (?&?);  exist val; eapply2 s_red_to_t_red. 
  (* 1 *) 
  induction n; intros h hn M P r c fac. lia. 
  inversion c; clear c; subst;  unfold meta_quote in *; fold meta_quote in *.
  (* 2 *)
  exist △.
  assert(root1: t_red (root @ △) △) by (eapply root_eval_to_root; auto_t).  
  assert(dp1: exists Q, s_red P Q /\ s_red △ Q) by
 (eapply diamond_s_red; [eapply multi_ranked_iff_multi_red | eapply t_red_to_s_red]; eauto).
  elim dp1.  clear dp1; intros P1 (?&?); auto_t. 
  assert(P1 = △) by (eapply programs_are_stable2; eauto; eapply pr_leaf); subst; auto. 
  (* 1 *)
  caseEq h; [intros | intros h' ?]; subst; inversion r as [ | ? ? Q0 ? ? s0]; clear r; subst; inv1 factorable.
  rewrite meta_quote_app. 
  elim(program_application_s_red1 _ _ s0 root (meta_quote (M0 @ N))); clear s0; intros; eauto; subst;
  [eapply2 IHn | | program_tac | eapply2 meta_quote_of_combination_is_program]. 
  assert(eval0: exists k, multi_ranked s_red1 k (root @ (△ @ meta_quote M0 @ meta_quote N))
                                       (onFork root1 @ (root @ meta_quote M0) @ root @ meta_quote N)) .  
    (apply multi_ranked_iff_multi_red; apply t_red_to_s_red; 
    unfold root; eapply transitive_red; [apply Y2_red | fold root]). apply root_aux_red.
    elim(eval0); clear eval0; intros k r1.
  caseEq k; [intros | intros k' ?]; subst; inversion r1 as [ | ? ? Q1 ? ? s1]; subst.
  elim(program_application_multi _ _ _ r1 root (△ @ meta_quote M0 @ meta_quote N)); clear r1;
    [ discriminate | | auto | program_tac | apply pr_fork; apply meta_quote_of_combination_is_program; auto].
  intro ex; elim ex; intros Q2 (?&?).
  assert(Q2 = Q0) by  (eapply hap1_functional; eauto);  subst.
  assert(s_red Q0 (onFork root1 @ (root @ meta_quote M0) @ root @ meta_quote N)) by 
      (eapply multi_ranked_iff_multi_red; eauto).
  assert(dp2: exists Q, s_red P Q /\
                           multi_ranked s_red1 h'
                                        (onFork root1 @ (root @ meta_quote M0) @ root @ meta_quote N) Q) by
      (eapply diamond_multi_ranked; eauto; apply diamond_s_red1_s_red).
  elim dp2; clear dp2; intros P2 (?&?).
  assert(factorable P2) by
      (eapply t_red_preserves_factorable; eauto; eapply s_red_to_t_red; auto_t).
  assert(fac1: exists M1,  multi_ranked s_red1 h' (root @ meta_quote M0) M1 /\ factorable M1).
  eapply needy_s_red_factorable; eauto. apply needy_app. apply needy_app.
  apply onFork_needy.   
  elim fac1; clear fac1; intros rM0 (s0 &facM0).
  assert(eval1: exists Q, root_eval (meta_quote M0) Q /\ s_red rM0 Q) by
      (eapply IHn; auto_t; lia).
  elim eval1; clear eval1; intros valM0 (re&?).
  elim(root_eval_produces_meta_quote _ _  re M0); auto_t. 
  (* 2 *)
  intros; subst. 
  assert(dp3: exists Q,  s_red P2 Q /\ multi_ranked s_red1 h' (△ @ meta_quote N) Q).
  eapply diamond_multi_ranked. apply diamond_s_red1_s_red. eauto. 
  eapply transitive_red. eapply preserves_app_s_red. eapply preserves_app_s_red.
  eapply transitive_red. eapply preserves_app_s_red. 
  zerotac. eapply multi_ranked_iff_multi_red. eauto.
  eapply preserves_app_s_red. zerotac. eauto. all: zerotac.
  unfold onFork.  apply preserves_app_s_red.
  eapply transitive_red. eapply preserves_app_s_red. eapply t_red_to_s_red. trtac. zerotac. 
  eapply2 succ_red. zerotac.
  elim dp3; clear dp3; intros P3 (?&?).
  assert(P3 = △ @ meta_quote N). apply programs_are_stable2. apply multi_ranked_iff_multi_red; eauto.
  apply pr_stem. apply meta_quote_of_combination_is_program; auto. subst.   
  exists (△ @ meta_quote N); split; simpl; auto_t; repeat (eapply transitive_red; eauto).
  (* 1 *)
  intros [ ex1 | ex1 ]; elim ex1.  
  intros N2 (? & cN2); subst.
  assert(dp3: exists Q,  s_red P2 Q /\ multi_ranked s_red1 h' (△ @ meta_quote N2 @ meta_quote N) Q).
  eapply diamond_multi_ranked; eauto. apply diamond_s_red1_s_red.
  eapply transitive_red. eapply preserves_app_s_red. eapply preserves_app_s_red.
  eapply transitive_red. eapply preserves_app_s_red. 
  zerotac. apply multi_ranked_iff_multi_red. eauto.
  eapply preserves_app_s_red. zerotac. eauto. all: zerotac. 
  eapply t_red_to_s_red. unfold onFork; trtac. 
  elim dp3; clear dp3; intros P4 (?&?). 
  assert(P4 = (△ @ meta_quote N2 @ meta_quote N)). eapply2 programs_are_stable2.
  apply multi_ranked_iff_multi_red; eauto.
  apply pr_fork; apply meta_quote_of_combination_is_program; auto. subst.   
  exists (△ @ meta_quote N2 @ meta_quote N); split_all.
  repeat (eapply transitive_red; eauto).
  (* 1 *)
   intros N2 ex2. elim ex2; intros N3 (e & c1 & c2); subst.
  assert(dp3: exists Q,  s_red P2 Q /\
                         multi_ranked s_red1 h' (root1 @ meta_quote N2 @ meta_quote N3 @ root @ meta_quote N) Q).
  eapply diamond_multi_ranked. apply diamond_s_red1_s_red. eauto. 
  eapply transitive_red. eapply preserves_app_s_red. eapply preserves_app_s_red.
  eapply transitive_red. eapply preserves_app_s_red. 
  zerotac. eapply transitive_red. apply multi_ranked_iff_multi_red. eauto. eauto.
  eapply t_red_to_s_red. unfold onFork. trtac. all: zerotac.
  elim dp3; clear dp3; intros P4 (?&?). 
  (* 1 *)
  assert(factorable P4) by (eapply t_red_preserves_factorable; [  apply s_red_to_t_red |]; eauto). 
  assert(fac2: exists M1,  multi_ranked s_red1 h' (root @ meta_quote N2) M1 /\ factorable M1).
  eapply needy_s_red_factorable. eauto. auto. apply needy_app. apply root1_needy.
  elim fac2; clear fac2; intros rx (?&?). 
  assert(eval2: exists Q, root_eval (meta_quote N2) Q /\ s_red rx Q) by  eapply2 IHn.
  elim eval2; clear eval2; intros valx (re6&?).
  elim(root_eval_produces_meta_quote _ _  re6 N2); auto.
  (* 2 *)
  intros; subst. 
  assert(dp3: exists Q,  s_red P4 Q /\ multi_ranked s_red1 h' (root @ meta_quote N3) Q).
  eapply diamond_multi_ranked; eauto. apply diamond_s_red1_s_red.
  eapply t_red_to_s_red. root1_tac. aptac. aptac. aptac. aptac. zerotac. apply s_red_to_t_red.
  eapply transitive_red.  eapply multi_ranked_iff_multi_red. eauto.  eassumption.
  apply triage_leaf. all: zerotac.
  unfold rootl. starstac("z" :: "y" :: "r" :: nil). 
  elim dp3; clear dp3; intros P5 (?&?).
  assert(factorable P5) by (eapply t_red_preserves_factorable; [ eapply s_red_to_t_red |]; eauto).
  assert(eval2: exists Q, root_eval (meta_quote N3) Q /\ s_red P5 Q) by  eapply2 IHn.
  elim eval2; clear eval2; intros rx0 (?&?).
  exists rx0; split; eauto; [  eapply root_fork_fork_fork_leaf; eauto | repeat (eapply transitive_red; eauto)].
  (* 1 *)
  intros [ ex3 | ex3]; elim ex3.
  (* 2 *)
  intros N4 (?&?); subst.  
  assert(dp3: exists Q,  s_red P4 Q /\
                         multi_ranked s_red1 h' (root @ (△ @ (△ @ meta_quote N3 @ meta_quote N)
                                                              @ (△ @ meta_quote N4 @ meta_quote N))) Q).
  eapply diamond_multi_ranked; eauto. apply diamond_s_red1_s_red.
  eapply t_red_to_s_red. root1_tac.   aptac. aptac. aptac. aptac. zerotac. apply s_red_to_t_red; eauto.
   eapply multi_ranked_iff_multi_red. eauto.  aptac. zerotac. eapply s_red_to_t_red; eauto. 
  eapply triage_stem. all: zerotac.
  unfold roots;trtac.
  elim dp3; clear dp3; intros P5 (?&?).
  assert(factorable P5) by (eapply t_red_preserves_factorable; [ eapply s_red_to_t_red |]; eauto).
  rewrite ! meta_quote_app in *.    
   assert(eval3: exists Q, root_eval (meta_quote (N3 @ N @ (N4 @ N))) Q /\ s_red P5 Q) by
       (eapply IHn; auto_t; lia).
  elim eval3; clear eval3; intros P6 (?&?).
  exists P6; split; eauto. eapply root_fork_fork_fork_stem; eauto. repeat (eapply transitive_red; eauto).
  (* 1 *)
  intros N4 ex4. elim ex4; intros N5 (?&?&?); subst. 
  assert(dp3: exists Q,  s_red P4 Q /\
                         multi_ranked s_red1 h' (root @ (△ @ (△ @ meta_quote N @ meta_quote N4)
                                                              @  meta_quote N5)) Q).
  eapply diamond_multi_ranked; eauto. apply diamond_s_red1_s_red.
  eapply t_red_to_s_red. root1_tac.  aptac. aptac. aptac. aptac. zerotac. apply s_red_to_t_red.
  eapply multi_ranked_iff_multi_red. eauto.  aptac. zerotac. eapply s_red_to_t_red; eauto. subst. 
  eapply triage_fork. all: zerotac.
  unfold rootf. starstac("z" :: "y" :: "r" :: "x" :: "w" :: nil). 
  elim dp3; clear dp3; intros P5 (?&?).
  assert(factorable P5) by (eapply t_red_preserves_factorable; [ eapply s_red_to_t_red | ]; eauto).
  rewrite meta_quote_app in *. 
  assert(eval3: exists Q, root_eval (meta_quote (N @ N4 @ N5)) Q /\ s_red P5 Q) by eapply2 IHn.
  elim eval3; clear eval3; intros P6 (?&?); subst.
  exists P6; split; eauto. eapply root_fork_fork_fork_fork; auto_t.
  repeat eapply2 transitive_red.
Qed. 



Theorem root_eval_iff_root :
  forall M P, combination M -> program P ->
              root_eval (meta_quote M) P <-> t_red (root @ (meta_quote M)) P.
Proof.
  intros M P prM prP; split; intro.
  apply root_eval_to_root; auto.   
  assert(eval1: exists Q, root_eval (meta_quote M) Q /\ t_red P Q) by 
      (apply root_to_root_eval_factorable; eauto; apply programs_are_factorable; eauto). 
  elim eval1; intros x (?&?).
  assert(x = P) by (eapply programs_are_stable2; eauto; apply t_red_to_s_red; eauto); subst; auto. 
Qed.


Lemma rb_program: program rb.
Proof. program_tac. Qed. 

Lemma rb_red :
  forall M, t_red (rb @ M)
                   (triage (△ @ △ @ △) (\"y" (\"r" (△ @ (Ref "r" @ Ref "y"))))
       (\"y" (\"z" (\"r" (△ @ (Ref "r" @ Ref "y") @ (Ref "r" @ Ref "z"))))) @ 
       (root @ M) @ rb).
Proof. intro M; unfold rb,Y2; eapply transitive_red; [ apply Y2_red | unfold d; trtac]. Qed.


Lemma active_trans: forall M N, active M N -> forall P, active N P -> active M P.
Proof.  intros M N a; induction a; intros;  eapply2 active_succ.  Qed. 
  
Lemma rb_needy :  forall M, needs (rb @ M) M. 
Proof.
  intro M; elim(root_needy M); intros x (?&?);
  elim(triage_needy  (△ @ △ @ △) (\"y" (\"r" (△ @ (Ref "r" @ Ref "y"))))
       (\"y" (\"z" (\"r" (△ @ (Ref "r" @ Ref "y") @ (Ref "r" @ Ref "z"))))) 
       x); intros x0 s; inversion s;  repeat eexists.
  (* 2 *)
  eapply t_red_to_s_red;  eapply transitive_red.  apply rb_red. aptac. aptac. zerotac.
  eapply2 s_red_to_t_red. eapply2 s_red_to_t_red. all: zerotac.
  (* 1 *)
  eapply active_app; eapply2 active_trans.
Qed.


Ltac program_stable_tac :=
    match goal with
    | pr: program ?M, r: s_red1 ?M ?N |- _ =>
      assert(N=M) by apply programs_are_stable; clear r; subst; program_stable_tac
    | pr: program ?M, r: s_red ?M ?N |- _ =>
      assert(N=M) by apply programs_are_stable2; clear r; subst; program_stable_tac
    | _ => idtac
    end. 


Lemma rb_to_rb_eval :
  forall n M P, t_red (rb @ meta_quote M) P -> combination M -> program P -> term_size P < n -> rb_eval (meta_quote M) P.
Proof.
  induction n; intros M P r c fac sz. lia.
  assert(dp1: exists Q, t_red P Q /\ t_red  (triage (△ @ △ @ △) (\"y" (\"r" (△ @ (Ref "r" @ Ref "y"))))
       (\"y" (\"z" (\"r" (△ @ (Ref "r" @ Ref "y") @ (Ref "r" @ Ref "z"))))) @ 
       (root @ meta_quote M) @ rb)  Q) .
  eapply diamond_t_red. eexact r. apply rb_red.
  elim dp1; clear dp1; intros P1 (?&?). 
  assert(P1 = P) by (eapply programs_are_stable2; eauto; apply t_red_to_s_red; eauto); subst.
  assert(ex: exists n, multi_ranked s_red1 n  (triage (K @ △) (\"y" (\"rs" (△ @ (Ref "rs" @ Ref "y"))))
            (\"y" (\"z" (\"rf" (△ @ (Ref "rf" @ Ref "y") @ (Ref "rf" @ Ref "z"))))) @
            (root @ meta_quote M) @ rb) P) by (eapply multi_ranked_iff_multi_red; apply t_red_to_s_red; eauto).
  elim ex; clear ex; intro k; intros.   
  assert(rM: exists M1, multi_ranked s_red1 k (root @ meta_quote M) M1 /\ factorable M1). 
  eapply needy_s_red_factorable; eauto.  apply programs_are_factorable; auto. apply needy_app. apply triage_needy.
  elim rM; clear rM; intros valM (?&?).
  (* 1 *)
  assert(ex1: exists Q : Tree, root_eval (meta_quote M) Q /\ t_red valM Q).
  eapply root_to_root_eval_factorable.
  apply s_red_to_t_red. apply multi_ranked_iff_multi_red.   eauto. auto. auto. 
  elim ex1; intros Q (?&?). 
  assert(s_red (root @ meta_quote M) Q). eapply transitive_red. apply multi_ranked_iff_multi_red; eauto.
  eapply t_red_to_s_red; auto. 
  assert(factorable Q) by (eapply t_red_preserves_factorable; eauto). 
  assert(orx: Q = △ \/
         (exists N1 : Tree, Q = △ @ meta_quote N1 /\ combination N1) \/
         (exists N1 N2 : Tree, Q = △ @ meta_quote N1 @ meta_quote N2 /\ combination N1 /\ combination N2))
    by (eapply root_eval_produces_meta_quote; eauto).
  inversion orx as [ | [ex2 | ex3] ]; clear orx; subst.
  (* 3 *) 
  assert(dp1: exists Q, t_red P Q /\ t_red △ Q) .
  eapply diamond_t_red. eapply s_red_to_t_red. apply multi_ranked_iff_multi_red; eauto.
  aptac. aptac. zerotac.
  apply s_red_to_t_red; eauto.  all: zerotac. aptac. apply triage_leaf. all: zerotac.
  trtac.  elim dp1; intros Q (?&?). 
  assert(Q = P) by (apply programs_are_stable2; eauto; apply t_red_to_s_red; eauto).
  assert(Q = △) by (apply programs_are_stable2; [apply t_red_to_s_red| apply pr_leaf]; eauto). subst. 
  apply rb_leaf; auto.
  (* 2 *)
  elim ex2; intros N1 (? & ?); subst.
  assert(ex4: exists Q, t_red P Q /\ t_red (△ @ (rb @ meta_quote N1)) Q). eapply diamond_t_red.
  apply s_red_to_t_red. apply multi_ranked_iff_multi_red; eauto.
  aptac. aptac. zerotac.   eapply2 s_red_to_t_red. 
  apply triage_stem. all: zerotac.
  starstac ("rs" :: "y" :: nil).
  elim ex4; intros Q (?&?). 
  assert(ex5: exists Q1, Q = △ @ Q1 /\ t_red (rb @ meta_quote N1) Q1) by eapply2 t_red_preserves_stems.
  assert(Q = P) .  apply programs_are_stable2. apply t_red_to_s_red; auto. auto. subst. 
      elim ex5; intros Q (?&?); subst.  inv1 program; subst; eapply rb_stem; auto_t.
      simpl in *; eapply2 IHn. 
  (* 1 *)
  elim ex3. intros N1 ex4; elim ex4; intros N2 (?&?&?); subst.
  assert(dp1: exists Q, t_red P Q /\ t_red (△ @ (rb @ meta_quote N1) @ (rb @ meta_quote N2)) Q).
  eapply diamond_t_red.  apply s_red_to_t_red. apply multi_ranked_iff_multi_red. eauto. 
  aptac. aptac. zerotac.   eapply2 s_red_to_t_red. 
  apply triage_fork. all: zerotac.
  starstac ("rf" :: "z" ::  "y" :: nil).
  elim dp1; intros Q (r4&?). 
  assert(Q = P) .  apply programs_are_stable2. apply t_red_to_s_red; auto. auto. subst. clear r4. 
  assert(ex5: exists Q R, P = △ @ Q @ R /\ t_red (rb @ meta_quote N1) Q /\
                     t_red (rb @ meta_quote N2) R) by (eapply2 t_red_preserves_forks). 
  elim ex5; intros R1 ex6; subst. elim ex6; intros R2 (?&?&?); subst. inv1 program; subst. 
   unfold term_size in *; fold term_size in *. eapply rb_fork. eassumption.
   all: eapply2 IHn. 
Qed.



Theorem rb_eval_iff_rb :
  forall M P, combination M -> program P ->  t_red (rb @ meta_quote M) P <-> rb_eval (meta_quote M) P. 
Proof.
  intros M P c pr; split; intro r.
  eapply rb_to_rb_eval; eauto. 
  eapply rb_eval_implies_rb; eauto. 
Qed.


Lemma rf_red: forall M N, program M -> program N -> t_red (rf @ M @ N) (rb @ (meta_quote (M @ N))).
Proof.
  intros M N prM prN; unfold rf, wait, d. starstac ("z" :: "f" :: "q" :: nil).
  aptac. zerotac. aptac. aptac. zerotac. apply quote_red; eauto. zerotac. eapply quote_red; auto. all: zerotac. 
Qed. 

  
Theorem rf_to_root_first_eval:
  forall M N P, program M -> program N -> program P ->  t_red (rf @ M @ N) P -> root_first_eval M N P.
Proof.
  intros M N P prM prN prP r. unfold root_first_eval.
  assert(ex: exists Q, s_red P Q /\  s_red (rb @ (meta_quote (M@N))) Q). 
  eapply diamond_s_red; eauto.   apply t_red_to_s_red; eauto. apply t_red_to_s_red. apply rf_red; auto.
  elim ex; intros Q (?&?). 
  assert(Q=P) by (eapply2 programs_are_stable2; auto). subst. 
  rewrite meta_quote_app. 
  eapply2 rb_to_rb_eval. eapply2 s_red_to_t_red. apply is_App; eapply2 programs_are_combinations. 
Qed.


Theorem root_first_eval_iff_rf:
    forall M N P, program M -> program N -> program P ->  t_red (rf @ M @ N) P <-> root_first_eval M N P.
  intros; split; intro. eapply2 rf_to_root_first_eval.  eapply2 root_first_eval_implies_rf. 
Qed.

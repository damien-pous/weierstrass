(** * Weierstrass' theorem, through Bernstein's polynomials *)

(* Author: Damien Pous,                                     *)
(* following lectures notes of Nicolas Brisebarre           *)

(*    This file is distributed under the terms of the       *)
(*      GNU General Public License Version 3.0              *)
(*      (see LICENSE file for the text of the license)      *)


From Stdlib Require Import ssreflect.                  (* for the nice rewrite tactic *)
From Stdlib Require Import Setoid Morphisms.           (* setoid rewriting *)
From Stdlib Require Import Arith Psatz.                (* arithmetic and [lia/lra] tactic *)
From Stdlib Require Import List.                       (* lists *)
Import ListNotations Nat.                              (* notations *)
From Stdlib Require Import Rbase Rfunctions Ranalysis. (* real numbers *)

(** ** factorial, binomial coefficients *)

Fixpoint fact n :=
  match n with
  | 0 => 1
  | S n' => fact n' * n
  end.

(** [fact] always returns a positive number *)
Lemma fact_neq0: forall n, fact n <> 0.
Proof. induction n; cbn; lia. Qed.

Fixpoint C n k :=
  match n,k with
  | _,0 => 1
  | 0,_ => 0
  | S n',S k' => C n' k' + C n' k
  end. 

Lemma Cn0: forall n, C n 0 = 1.
Proof. by case. Qed.

Lemma Cn1: forall n, C n 1 = n.
Proof. elim=>//=n ->. by rewrite Cn0. Qed.

Lemma Cn2: forall n, C n 2 * 2 = n * (n - 1).
Proof.
  elim=>//=n IH.
  rewrite Cn1 mul_add_distr_r {}IH.
  case: n=>/=; lia. 
Qed.

Lemma Czer': forall n k, n<k <-> C n k = 0.
Proof.
  elim=>[|n IH] [|k]/=; try lia. 
  rewrite eq_add_0 -2!IH. lia. 
Qed.
Lemma Czer: forall n k, n<k -> C n k = 0.
Proof. apply Czer'. Qed.
Lemma Cpos n k: k<=n -> 0 < C n k.
Proof. move:(Czer' n k). lia. Qed.

Lemma Cnn: forall n, C n n = 1.
Proof. elim=>//= n ->. rewrite Czer; lia. Qed.

Lemma factC: forall n k, k<=n -> fact n = C n k * fact k * fact (n - k).
Proof.
  elim=>[|n IH] [|k] H /=; try lia.
  case: (eq_nat_dec k n)=>[<-|H'].
  - rewrite Cnn Czer. lia.
    rewrite sub_diag/=. lia. 
  - transitivity (
        C n k * fact k * fact (n-k) * S k
        + C n (S k) * fact (S k) * fact (n-S k) * (n - k)
      ).
    rewrite -!IH; lia.
    replace (n-k) with (S (n-S k)) by lia.    
    cbn. ring.
Qed.

Corollary Cfact n k: k<=n -> C n k = fact n / (fact k * fact (n - k)).
Proof.
  move=>kn. rewrite (factC n k)//.
  rewrite -mul_assoc div_mul//.
  by rewrite -neq_mul_0; split; apply fact_neq0.
Qed.

Lemma Csym n k: k<=n -> C n k = C n (n - k).
Proof.
  move=>kn.
  rewrite !Cfact//. lia. 
  replace (n-(n-k)) with k by lia.
  by rewrite mul_comm. 
Qed.

Lemma Cpion n k: C (S n) (S k) * S k = C n k * S n.
Proof.
  case: (le_lt_dec k n) => [L|L].
  - apply mul_cancel_l with (fact k * fact (n - k)).
    by rewrite -neq_mul_0; split; apply fact_neq0.
    transitivity (fact (S n)).
    -- rewrite (factC (S n) (S k)) /=; lia.
    -- rewrite /= (factC n k); lia.
  - rewrite !Czer; lia.
Qed.


(** ** finite sums of real numbers *)

(* by default, notations about real numbers *)
Open Scope R_scope.

(* enable rewriting with relation [<=] on reals *)
Global Instance Rle_rw: RewriteRelation Rle := {}. 
Global Instance Rle_PreOrder: PreOrder Rle.
Proof. constructor; cbv; intros; lra. Qed.
Global Instance Rplus_Rle: Proper (Rle ==> Rle ==> Rle) Rplus.
Proof. repeat intro. lra. Qed.


(** [sum f n] computes f 0 + ... + f (n-1), for a natural number n and a function f: nat -> R *)
Fixpoint sum n f :=
  match n with
  | O => 0
  | S n => sum n f + f n
  end.                

Lemma sum0 f: sum 0 f = 0.
Proof. done. Qed. 

Lemma sum1 f: sum 1 f = f 0%nat.
Proof. cbn; ring. Qed. 

Lemma sumS_last n f: sum (S n) f = sum n f + f n.
Proof. done. Qed. 

Lemma sumS_first n f: sum (S n) f = f 0%nat + sum n (fun i => f (S i)).
Proof.
  elim:n=>[|n IH].
  - cbn; ring.
  - rewrite sumS_last IH/=. ring. 
Qed.

(* the above lemmas are nice to use when we have an explicit successor (S);
   the ones below are equivalent, and easier to use when the successor is not explicit *)
Lemma sum_last n f: (0<n)%nat -> sum n f = sum (pred n) f + f (pred n).
Proof. case:n=>//. lia. Qed. 

Lemma sum_first n f: (0<n)%nat -> sum n f = f 0%nat + sum (pred n) (fun i => f (S i)).
Proof. case:n=>[|/= n _]. lia. exact: sumS_first. Qed.

Lemma xsum n x f: x * sum n f = sum n (fun i => x * f i).
Proof. elim:n=>/= [|n <-]; ring. Qed.

Lemma sum_plus n f g: sum n (fun i => f i + g i) = sum n f + sum n g.
Proof. elim:n=>/= [|n ->]; ring. Qed.

Lemma sum_minus n f g: sum n (fun i => f i - g i) = sum n f - sum n g.
Proof. elim:n=>/= [|n ->]; ring. Qed.

Lemma sum_rev n f: sum n f = sum n (fun i => f (n-S i)%nat).
Proof.
  elim: n=>//n IH. 
  rewrite sumS_last sumS_first IH /=.
  replace (n - 0)%nat with n by lia. ring. 
Qed.

(* rewriting under sums *)
Lemma sum_eq n f g: (forall i, (i<n)%nat -> f i = g i) -> sum n f = sum n g.
Proof.
  elim:n=>//=n IH H.
  rewrite H. lia. rewrite IH//.
  move=>??; apply: H; lia.
Qed.

Lemma sum_le n f g: (forall i, (i<n)%nat -> f i <= g i) -> sum n f <= sum n g.
Proof.
  elim:n=>/=[_|n IH H]. reflexivity. 
  rewrite H. lia. rewrite IH//. 2: reflexivity. 
  move=>??; apply: H; lia.
Qed.

(* weakened versions for setoid rewriting *)
Global Instance sum_pwr_eq n: Proper (pointwise_relation nat Logic.eq ==> Logic.eq) (sum n).
Proof. intros ???. apply sum_eq. intros ? _. apply H. Qed.

Global Instance sum_pwr_le n: Proper (pointwise_relation nat Rle ==> Rle) (sum n).
Proof. intros ???. apply sum_le. intros ? _. apply H. Qed.

Lemma split_sum (p: nat -> bool) n f:
  sum n f =
  sum n (fun i => if p i then f i else 0) +
  sum n (fun i => if p i then 0 else f i).
Proof.
  elim:n=>[|n IH]/=.
  - ring. 
  - rewrite IH. case p; ring.
Qed.

Lemma Rabs_sum n f: Rabs (sum n f) <= sum n (fun i => Rabs (f i)).
Proof.
  elim:n=>[|n IH]/=.
  - split_Rabs; lra.
  - now rewrite Rabs_triang IH. 
Qed.

(* prevent [sum] from reducing, for better control about it *)
Arguments sum: simpl never.


(** ** injection of natural numbers into real numbers *)

(** a few basic lemmas about [INR] *)
Lemma INR0: INR O = 0. Proof. reflexivity. Qed.
Lemma INR1: INR 1 = 1. Proof. reflexivity. Qed.
Lemma INReq (n m: nat): n = m <-> INR n = INR m.
Proof. split; auto using INR_eq. Qed.
Lemma INRle (n m: nat): (n <= m)%nat <-> INR n <= INR m.
Proof. split; auto using INR_le, le_INR. Qed.
Lemma INRlt (n m: nat): (n < m)%nat <-> INR n < INR m.
Proof. split. rewrite /Peano.lt INRle S_INR. lra. apply INR_lt. Qed.

Lemma Rdiv0 n: 0 / n = 0.
Proof. rewrite /Rdiv. ring. Qed.

(** by defining [arith] as follows, one can use [rewrite ?arith] to simplify goals involving [INR] and basic arithmetic *)
Definition arith :=
  (INR0, INR1,S_INR,plus_INR,mult_INR,INReq,INRle,INRlt,
    Cn0, Cn1, Cnn, sum0, sum1,
    Nat.add_0_r, Nat.add_succ_r, Nat.sub_0_r, Nat.sub_diag,
    Rplus_0_l, Rplus_0_r,
    Rmult_0_l, Rmult_0_r, Rmult_1_l, Rmult_1_r, Rdiv0).

(** this one cannot be automated due to the side condition, this is why we leave it out *)
Lemma INRpred: forall n, (0<n)%nat -> INR (pred n) = INR n - 1.
Proof. case=>[|n] H. lia. rewrite S_INR/=. lra. Qed.

(* prevent reduction of [INR], for better control *)
Arguments INR: simpl never.

(** we declare [INR] as a coercion, so that it gets inserted automatically *)
Coercion INR: nat >-> R.

(** a tactic which is convenient below to discharge proof obligations from the [field] tactic *)
Ltac neq_0 := repeat split; solve [ apply not_O_INR; lia ].

(** typical example *)
Goal forall n x y, (n>0)%nat -> (x+y)/n = x/n + y/n.
Proof. intros. field. neq_0. Qed.

(** another useful lemma *)
Lemma cancel_r x y z: y-x=z-x -> y=z.
Proof. lra. Qed.

(** ** binomial equation *)

Proposition binomial x y: forall n, (x + y) ^ n = sum (S n) (fun i => C n i * x ^ i * y ^ (n - i)).
Proof.
  elim=>[|n IH].
  - by rewrite !arith. 
  - rewrite sumS_last sumS_first /= !arith.
    rewrite (Czer n (S n)). lia. 
    rewrite arith IH Rmult_plus_distr_r 2!xsum.
    rewrite sumS_last sumS_first /= !arith. 
    apply cancel_r with (x^(S n)+y^(S n)). simpl. ring_simplify.
    rewrite -sum_plus. apply sum_eq=>i Hi. 
    rewrite !arith. 
    replace (n-i)%nat with (S (n-(S i))) by lia.
    simpl. ring. 
Qed.

Corollary binomial' x n: sum (S n) (fun k => C n k * x^k * (1-x)^(n-k)) = 1.
Proof.
  rewrite -binomial.
  replace (x+(1-x)) with 1 by ring.
  exact: pow1.
Qed.

(* like before with [sum_first/last], the variant below is sometimes more convenient *)
Corollary binomial'' x n: (0<n)%nat -> sum n (fun k => C (pred n) k * x^k * (1-x)^(pred n-k)) = 1.
Proof.
  intro. replace n with (S (pred n)) by lia. apply binomial'. 
Qed.

Corollary pow2n: forall n, sum (S n) (fun i => C n i) = 2^n.
Proof.
  intro. replace 2 with (1+1) by ring.
  rewrite binomial. apply sum_eq=>i Hi. 
  rewrite 2!pow1. ring.
Qed.

Corollary powk2n: forall n, sum (S n) (fun i => i * C n i) = n * 2^(n-1).
Proof.
  intro. rewrite -pow2n. rewrite xsum.
  case:n=>//n.
  rewrite sumS_first. rewrite !arith. 
  replace (S n - 1)%nat with n by lia.
  apply sum_eq=>i Hi.
  rewrite Rmult_comm -mult_INR Cpion !arith. ring.
Qed.

(** ** polynomials, continuity *)

(** *** polynomials  *)

(** we represent polynomials by their list of coefficients
    [a;b;c] represents a+bX+cX^2
    note that we do *not* impose that the last coefficient must be non-zero.
  *)
Definition poly := list R.
Fixpoint eval (P: poly) (x: R): R :=
  match P with
  | [] => 0
  | a::Q => a + x * eval Q x
  end.

Definition pcst a: poly := [a].
Lemma eval_cst a x: eval (pcst a) x = a.
Proof. simpl. ring. Qed.

Definition pid: poly := [0;1].
Lemma eval_id x: eval pid x = x.
Proof. simpl. ring. Qed.

Fixpoint pxk (k: nat): poly :=
  match k with
  | O => [1]
  | S k => 0::pxk k
  end.
Lemma eval_xk k x: eval (pxk k) x = x^k.
Proof. elim: k=>/=[|k ->]/=; ring. Qed.

Fixpoint pplus (P Q: poly): poly :=
  match P,Q with
  | [],R | R,[] => R
  | a::P,b::Q => (a+b)::pplus P Q
  end.
Arguments pplus !P !Q /.
Lemma eval_plus: forall P Q x, eval (pplus P Q) x = eval P x + eval Q x.
Proof. elim=>/=[|a P IH] [|b Q] x /=; rewrite ?IH; ring. Qed.

Definition pscal a (P: poly): poly := List.map (Rmult a) P.
Lemma eval_scal a: forall P x, eval (pscal a P) x = a * eval P x.
Proof. elim=>/=[|b P IH] x /=; rewrite ?IH; ring. Qed.
       
Fixpoint pmult (P Q: poly): poly :=
  match P with
  | [] => []
  | a::P => pplus (pscal a Q) (0::pmult P Q)
  end.
Lemma eval_mult: forall P Q x, eval (pmult P Q) x = eval P x * eval Q x.
Proof.
  elim=>/=[|b P IH] Q x /=. ring.
  rewrite eval_plus eval_scal /= IH. ring. 
Qed.

Fixpoint pcomp (P Q: poly): poly :=
  match P with
  | [] => []
  | a::P => pplus (pcst a) (pmult (pcomp P Q) Q)
  end.
Lemma eval_comp: forall P Q x, eval (pcomp P Q) x = eval P (eval Q x).
Proof.
  elim=>/=[//|b P IH] Q x. 
  rewrite eval_plus eval_cst eval_mult IH. ring. 
Qed.


(** *** isolating polynomials amongst arbitrary functions (boilerplate) *)

Definition is_poly (f: R -> R) := exists P: poly, forall x, eval P x = f x.

Lemma is_poly_cst a: is_poly (fun _ => a).
Proof. exists (pcst a). apply eval_cst. Qed.

Lemma is_poly_id: is_poly (fun x => x).
Proof. exists pid. apply eval_id. Qed.

Lemma is_poly_xk k: is_poly (fun x => x^k).
Proof. exists (pxk k). apply eval_xk. Qed.
  
Lemma is_poly_plus f g: is_poly f -> is_poly g -> is_poly (fun x => f x + g x).
Proof.
  move=>[P Pf] [Q Qg]. exists (pplus P Q)=>x.
  by rewrite eval_plus Pf Qg.
Qed.

Lemma is_poly_scal f a: is_poly f -> is_poly (fun x => a * f x).
Proof.
  move=>[P Pf]. exists (pscal a P)=>x.
  by rewrite eval_scal Pf.
Qed.

Lemma is_poly_opp: is_poly Ropp.
Proof. exists (pscal (-1) pid)=>x/=. ring. Qed.

Lemma is_poly_mult f g: is_poly f -> is_poly g -> is_poly (fun x => f x * g x).
Proof.
  move=>[P Pf] [Q Qg]. exists (pmult P Q)=>x.
  by rewrite eval_mult Pf Qg.
Qed.

Lemma is_poly_comp f g: is_poly f -> is_poly g -> is_poly (fun x => f (g x)).
Proof.
  move=>[P Pf] [Q Qg]. exists (pcomp P Q)=>x.
  by rewrite eval_comp Pf Qg.
Qed.

(* [is_poly] is stable under pointwise equality of functions *)
Global Instance is_poly_Proper: Proper (pointwise_relation R Logic.eq ==> Basics.impl) is_poly.
Proof. intros f g H. unfold is_poly. now setoid_rewrite H. Qed.

Lemma is_poly_sum n f:
  (forall i, i<n -> is_poly (f i))%nat -> is_poly (fun x => sum n (fun i => f i x)).
Proof.
  elim:n=>[|n IH] H. 
  - setoid_rewrite sum0. exact: is_poly_cst.
  - setoid_rewrite sumS_last. apply: is_poly_plus.
    apply: IH=>i Hi. apply: H. lia.
    apply: H. lia. 
Qed.



(** *** continuity *)

Definition continuous_at f x :=
  forall e, 0<e -> exists d, 0<d /\ forall y, Rabs(y-x)<=d -> Rabs(f y-f x)<=e.

(** we prove that this definition is equivalent to the one in the
 standard library (the one above is slightly easier to work with) *)
Lemma continuous_at_standard f x:
  continuous_at f x <-> continuity_pt f x.
Proof.
  split=>H e He.
  - have [|d [D Hd]] := (H (e/2)). lra.
    exists d. split=>//y. 
    simpl dist; unfold R_dist.
    move=>[_ ?]. move: (Hd y). lra. 
  - have [//|d [D Hd]] := (H e). 
    simpl dist in Hd; unfold R_dist in Hd.
    exists (d/2). split. lra. 
    move=>y Hy. move: (Req_dec x y)=>[-> | N]. split_Rabs; lra. 
    apply: Rlt_le. apply: Hd. split. by split. lra.
Qed.

Lemma continuous_id x: continuous_at id x.
Proof. move=>e He. by exists e. Qed.

Lemma continuous_cst a x: continuous_at (fun _ => a) x.
Proof.
  move=>e He. exists 1. split. lra. 
  move=>y D. split_Rabs; lra. 
Qed.

Lemma continuous_plus f g x:
  continuous_at f x -> continuous_at g x -> continuous_at (fun y => f y + g y) x.
Proof.
  move=> F G e He.
  have [|df [Df Hdf]] := F (e/2). lra. 
  have [|dg [Dg Hdg]] := G (e/2). lra. 
  exists (Rmin df dg). split. by apply: Rmin_case.
  move=>y D. 
  pose proof (conj (Rmin_l df dg) (Rmin_r df dg)).
  replace (_-_) with ((f y-f x) + (g y-g x)) by ring.
  rewrite Rabs_triang Hdf. lra.
  rewrite Hdg; lra. 
Qed.

Lemma continuous_Rabs x: continuous_at Rabs x.
Proof. move=>e He. exists e. split=>//y D. split_Rabs; lra. Qed.

Lemma continuous_comp f g x:
  continuous_at f x -> continuous_at g (f x) -> continuous_at (fun y => g (f y)) x.
Proof.
  move=>F G e E.
  specialize (G e E) as (d&D&Hg).
  specialize (F d D) as (d'&D'&Hf). 
  exists d'. split=>// y L. apply Hg, Hf, L.
Qed.
  
Lemma x_div_1x x: 0<=x -> x/(x+1) <= 1.
Proof.
  intro. apply (Rmult_le_reg_l (x+1)). lra.
  field_simplify; lra.
Qed.

Lemma continuous_mult f g x:
  continuous_at f x -> continuous_at g x -> continuous_at (fun y => f y * g y) x.
Proof.
  move=>F G e He.
  set ef := (Rmin (e/(3*(Rabs (g x) + 1))) (sqrt (e/3))). 
  destruct (F ef) as (df&Df&Hdf).
   apply Rmin_case. apply Rdiv_lt_0_compat=>//. split_Rabs; lra.
   apply sqrt_lt_R0. apply Rdiv_lt_0_compat=>//. lra.
  set eg := (Rmin (e/(3*(Rabs (f x) + 1))) (sqrt (e/3))). 
  destruct (G eg) as (dg&Dg&Hdg).
   apply Rmin_case. apply Rdiv_lt_0_compat=>//. split_Rabs; lra.
   apply sqrt_lt_R0. apply Rdiv_lt_0_compat=>//. lra. 
  exists (Rmin df dg). split. by apply: Rmin_case.
  move=> y D. 
  pose proof (conj (Rmin_l df dg) (Rmin_r df dg)).
  replace (_-_) with ((f y-f x) * g x + (g y-g x) * f x + (f y-f x)*(g y-g x)) by ring.
  rewrite 2!Rabs_triang 3!Rabs_mult. 
  replace e with (e/3 + e/3 + e/3) by lra.
  apply Rplus_le_compat. apply Rplus_le_compat.
  - erewrite Rmult_le_compat_r. 2: apply Rabs_pos. 2: apply Hdf; lra.
    erewrite Rmult_le_compat_r. 2: apply Rabs_pos. 2: apply Rmin_l.
    transitivity ((Rabs (g x))/(Rabs (g x)+1)*(e/3)). apply Req_le. field. split_Rabs; lra.
    erewrite Rmult_le_compat_r. 2: lra. 2: apply x_div_1x. apply Req_le. ring. apply Rabs_pos. 
  - erewrite Rmult_le_compat_r. 2: apply Rabs_pos. 2: apply Hdg; lra.
    erewrite Rmult_le_compat_r. 2: apply Rabs_pos. 2: apply Rmin_l.
    transitivity ((Rabs (f x))/(Rabs (f x)+1)*(e/3)). apply Req_le. field. split_Rabs; lra.
    erewrite Rmult_le_compat_r. 2: lra. 2: apply x_div_1x. apply Req_le. ring. apply Rabs_pos. 
  - etransitivity. apply Rmult_le_compat. apply Rabs_pos. apply Rabs_pos.
    rewrite Hdf. lra. apply Rmin_r. 
    rewrite Hdg. lra. apply Rmin_r.
    apply Req_le, sqrt_sqrt. lra. 
Qed.  

Lemma poly_continuous P x: continuous_at (eval P) x.
Proof.
  elim: P=> [|a P IH]/=.
  - apply continuous_cst. 
  - apply continuous_plus. apply continuous_cst. 
    apply continuous_mult. apply continuous_id. apply IH.
Qed.


(** ** Weierstrass' theorem, via Bernstein's polynomials *)

(** *** Bernstein's polynomials *)

(** the family of Bernstein's polynomials *)
Definition b n k x := C n k * x^k * (1-x)^(n-k).

Lemma is_poly_b k n: is_poly (b n k).
Proof.
  apply is_poly_mult. apply is_poly_scal. apply is_poly_xk. 
  apply (is_poly_comp (fun x => x^(n-k))). 
  apply is_poly_xk. apply is_poly_plus. apply is_poly_cst. apply is_poly_opp.
Qed.

(** the approximant of a function [g] at order [n] *)
Definition B n g := fun x => sum (S n) (fun k => g (k / n) * b n k x).

(** our goal is to prove that the sequence [(B n g)_{n\in nat}] converges towards [g] *)

(** first we show that [B n g] is indeed a polynomial *)
Lemma is_poly_B n g: is_poly (B n g).
Proof.
  apply is_poly_sum. intros k _.
  apply is_poly_mult. apply is_poly_cst. apply is_poly_b. 
Qed.

Lemma B1 n x: B n (fun _ => 1) x = 1.
Proof.
  unfold B, b. setoid_rewrite Rmult_1_l. apply binomial'. 
Qed.

Lemma Cpion': forall n i, (0<n)%nat -> S i / n * C n (S i) = C (pred n) i.
Proof.
  (* TODO: here a mixed lia/lra tactic would help *)
  move=>[/=|n] i. lia.
  move=>_. 
  have D: INR (S n) <> 0 by neq_0.
  apply Rmult_eq_reg_r with (S n)=>//.
  rewrite -mult_INR -Cpion 4!arith. simpl; field. 
  move: D. by rewrite arith. 
Qed.

(* two tactics to rewrite under sums, with lemmas involving side conditions *)
Ltac open_sum i Hi := erewrite sum_eq; swap 1 2; [intros i Hi|].
Ltac close_sum := reflexivity. 

Lemma Bx n x: (0<n)%nat -> B n (fun x => x) x = x.
Proof.
  case:n. lia. move=>n _. unfold B, b.
  rewrite sumS_first !arith.
  open_sum k Hk.
    rewrite -2!Rmult_assoc -S_INR Cpion' /=. lia.
    transitivity (x*(C n k * x^k * (1-x)^(n-k))). ring. 
  close_sum.
  rewrite -xsum binomial'. ring.  
Qed.

Lemma Bx2 n x: (0<n)%nat -> B n (fun x => x^2) x = x/n + x^2 * (n-1)/n.
Proof.
  (* we first deal with the case n=1 *)
  move=>N'. have C: (n=1 \/ 1<n)%nat by lia.
  case: C=> [->|N] {N'}; unfold B, b.
  rewrite sumS_first sum1 Cn0 Cnn !arith. field. 
  (* then we use the following path:
     
      Bn(x^2,x) 
=     Sum k=0..n (n k)(k/n)^2       x^k     (1-x)^(n-k)
=   x Sum k=1..n (k/n)    (n-1 k-1) x^(k-1) (1-x)^(n-k)
=   x Sum k=1..n ((k-1)/n)(n-1 k-1) x^(k-1) (1-x)^(n-k)    + x/n
= (n-1)/n x^2 Sum k=2..n (n-2 k-2)  x^(k-2) (1-x)^(n-k)    + x/n
= (n-1)/n x^2                                              + x/n

 *)
  rewrite sumS_first !arith. ring_simplify.
  open_sum k Hk.
    rewrite -2!Rmult_assoc.
    replace (_^2 * _) with (S k / n * (S k / n * C n (S k))) by ring.
    rewrite Cpion'. lia.
    rewrite arith. replace (_/_) with (k/n + 1/n) by (field; neq_0).
    rewrite 3!Rmult_plus_distr_r. 
  close_sum.
  rewrite sum_plus.
  rewrite sum_first. lia. rewrite !arith.
  open_sum k Hk.
    transitivity (((n - 1) / n * x^2) * (S k / pred n * C (pred n) (S k)) * x^k * (1-x)^(pred (pred n)-k)).
    rewrite !arith INRpred. lia.
    replace (n-S(S k))%nat with (pred (pred n) - k)%nat by lia. 
    simpl. field. rewrite !arith in N. lra. 
    rewrite Cpion'. lia.
    rewrite 2!Rmult_assoc -(Rmult_assoc (C _ _)).
  close_sum.
  rewrite -xsum binomial''. lia.
  open_sum k Hk.
    transitivity (x/n * (C (pred n) k * x^k * (1-x)^(pred n-k))).
    replace (pred n-k)%nat with (n-S k)%nat by lia.
    simpl. field. neq_0.
  close_sum.
  rewrite -xsum binomial''. lia.
  field. neq_0.
Qed.


(** *** Weierstrass' theorem: polynomials are dense in C(a,b) *)

(** the following 'least natural upper bound' is more convenient to use
   than the native 'least relative upper bound *)
Definition nup (x: R) := Z.to_nat (up x).

Lemma IPR_pos p: 0<IPR p.
Proof.
  have H: forall q, 0<IPR_2 q by elim=>[q|q|]; simpl; nra.
  destruct p; unfold IPR; try specialize (H p); lra. 
Qed.

Lemma nup_above x: x < nup x.
Proof.
  rewrite /nup.
  case: (archimed x)=>H H'.
  destruct (up x) as [|z|z]; simpl in *.
  by rewrite arith.
  by rewrite INR_IPR.
  rewrite arith. unfold IZR in *. pose proof (IPR_pos z). lra. 
Qed.

(* a few other helpers *)
Lemma C_pos n k: (k <= n)%nat -> 0 < C n k.
Proof.
  move=>kn. apply Cpos, lt_INR in kn.
  by rewrite arith in kn.
Qed.

Lemma b_pos n k x: (k <= n)%nat -> 0<=x<=1 -> 0 <= b n k x.
Proof.
  move=>kn H. rewrite /b. apply Rmult_le_pos. apply Rmult_le_pos.
  apply Rlt_le, C_pos, kn.
  apply pow_le, H.
  apply pow_le. lra.
Qed.

Lemma Ikn k n: (k<=n)%nat -> (0<n)%nat -> 0<=k/n<=1.
Proof.
  move=>kn zn. pose proof (pos_INR k).
  assert(k <= n) by now apply le_INR.
  assert(0 < n) by now apply lt_0_INR.
  split; apply Rmult_le_reg_l with n=>//.
  ring_simplify. replace (_ * _) with (INR k)=>//. field. neq_0. 
  ring_simplify. replace (_ * _) with (INR k)=>//. field. neq_0. 
Qed.

Definition Rlt_bool x y := match Rlt_dec x y with left _ => true | _ => false end.

Definition norm_inf a b f g e := forall x, a<=x<=b -> Rabs (f x - g x) <= e.

Lemma Rdiv_ge0 a b: 0 <= a -> 0 < b -> 0 <= a / b.
Proof.
  intros. assert (0 < /b) by now apply Rinv_0_lt_compat. nra. 
Qed.

Lemma Weierstrass_aux1 d x y: 0 < d <= Rabs (x-y) -> 1 <= ((x-y)/d)^2.
Proof.
  move=>H. rewrite -Ratan.pow2_abs. apply pow_R1_Rle. 
  rewrite Rabs_mult. apply Rmult_le_reg_l with d. tauto.
  replace (Rabs (/d)) with (/d). 
  field_simplify. split_Rabs; lra. lra.
  symmetry; apply Rabs_pos_eq.
  apply proj1, Rinv_0_lt_compat in H. lra.
Qed.

Lemma Weierstrass_aux2 x: 0 <= x <= 1 -> x*(1-x) <= 1.
Proof.
  move=>H. transitivity (1*1). 2: lra. 
  apply Rmult_le_compat; lra. 
Qed.


(** we first prove the theorem on the interval [0;1], and we rely for
    that on Heine's theorem, which is in the standard library.
    we state it here with a form which is more convenient in the sequel. *)

(* Heine's theorem  *)
Theorem Heine01 f: 
  (forall x, 0<=x<=1 -> continuous_at f x) ->
  forall e, 0<e -> exists d, 0<d /\ forall x y, 0<=x<=1 -> 0<=y<=1 -> Rabs (x-y) <= d -> Rabs (f x - f y) <= e.
Proof.
  move=>F e E.
  have UC: uniform_continuity f (fun x => 0<=x<=1).
   apply Heine. apply compact_P3. intros. apply continuous_at_standard. exact: F.
  have [[d D] /=Hd] := UC (mkposreal _ E). 
  exists (d/2). split. lra.
  move=>x y. specialize (Hd x y). lra. 
Qed.

(** Weierstrass' theorem, first on the interval [0;1] *)

Theorem Weierstrass01 f:
  (forall x, 0<=x<=1 -> continuous_at f x) ->
  forall e, 0<e -> exists p, is_poly p /\ norm_inf 0 1 f p e.
Proof.
  move=>F e E.
  
  (* 1. f is uniformly continuous on [0;1] => pick corresponding delta, d *)
  have [| d [D Hd]] := Heine01 _ F (e/2). lra.
  
  (* 2. then we call M an upper-bound of the absolute value of f on [0;1], reached at m *)
  have [| |{F} m [Hm Im]] := continuity_ab_maj (fun x => Rabs (f x)) 0 1. lra. {
   move=>x Hx. apply continuous_at_standard.
   apply (continuous_comp f Rabs). exact: F. exact: continuous_Rabs.
  }
  set M := Rabs (f m) in Hm.
  
  (* 2'. M is non negative *)
  have M': 0<=M by apply Rabs_pos.
  
  (* 3. guess a large enough value for n *)
  set n := nup (4*M/(e*d^2)).
  (* this value is certainly positive (in R and in nat) *)
  have N: 0<n. {
   eapply Rle_lt_trans. 2: apply nup_above. 
   apply Rdiv_ge0. lra. 
   apply Rmult_lt_0_compat=>//. nra.
  }
  have N': (0<n)%nat by rewrite arith.
  
  (* 4. [B n f] is the desired approximation *)
  exists (B n f). split. apply is_poly_B. intros x Ix.
  
  (* 5. write [f x - B n f x] as [Sum k=0..n (f x - f (k/n)) b n k x] *)
  replace (f x - B n f x) with (sum (S n) (fun k => (f x - f (k/n)) * b n k x)); first last.
  { setoid_rewrite Rmult_minus_distr_r.
    rewrite sum_minus. f_equal.
    rewrite -xsum binomial'. lra. }
  
  (* 6. split the sum according to whether |x-k/n| < d or not *)
  rewrite (split_sum (fun k => Rlt_bool (Rabs (x-k/n)) d)).
  
  (* 7. use triangle inequality *)
  rewrite Rabs_triang.
  
  (* 8. split epsilon into two parts and bound the two sums (Check Rplus_le_compat) *)
  replace e with (e/2 + e/2) by field. apply Rplus_le_compat.
  
    (* for the first sum, use generalised triangle inequality,
       bound each term by [e/2 b n k] (using [sum_le]) and conclude with binomial law *)
  - rewrite Rabs_sum.
    transitivity (sum (S n) (fun k => e/2 * b n k x)). apply sum_le.
    intros k Hk. unfold Rlt_bool. case Rlt_dec.
    * intro H. rewrite Rabs_mult. apply Rmult_le_compat.
      apply Rabs_pos. apply Rabs_pos. apply Hd; trivial. apply Ikn; lia. lra.
      rewrite Rabs_pos_eq. apply b_pos=>//; lia. reflexivity. 
    * intros _. rewrite Rabs_R0. apply Rmult_le_pos. lra. apply b_pos=>//; lia.
    * rewrite -xsum binomial'. lra.
      
    (* for the second sum, use generalised triangle inequality again, 
       and bound each term by [2M ((x-k/n)/d)^2 b n k x]
     *)
  - rewrite Rabs_sum.
    transitivity (sum (S n) (fun k => 2*M*(((x-k/n)/d)^2 * b n k x))).
    -- apply sum_le. intros k Hk. unfold Rlt_bool. case Rlt_dec.
    * intros _. rewrite Rabs_R0. apply Rmult_le_pos. lra. apply Rmult_le_pos. 
      apply Ratan.pow2_ge_0. apply b_pos=>//; lia.
    * intro L. rewrite Rabs_mult -Rmult_assoc. apply Rmult_le_compat.
      apply Rabs_pos. apply Rabs_pos. rewrite Rabs_triang.
      rewrite Rabs_Ropp Hm//Hm. apply Ikn; lia. 
      erewrite <-Rmult_le_compat_l. 3: apply Weierstrass_aux1; lra. lra. lra.  
      rewrite Rabs_pos_eq. apply b_pos=>//; lia. reflexivity.
    --
      (* simplify the sum using properties B1, Bx, and Bx2 *)
      transitivity (2 * M * ((x - x^2) / (n * d^2))). apply Req_le. 
      { rewrite -xsum. f_equal. 
        open_sum k Hk.
          transitivity
            (1/d^2*(x^2*b n k x
                      + -2*x*(k/n * b n k x)
                      + (k/n)^2*b n k x)).
          field. lra. 
        close_sum.
        rewrite -xsum. 
        rewrite 2!sum_plus. 
        rewrite -2!xsum.
        rewrite binomial'. 
        setoid_rewrite Bx. 2: assumption. 
        setoid_rewrite Bx2. 2: assumption. 
        field. lra.
      }
      (* the remaining inequation is valid for large enough n; 
         go back to the def of n, fix it accordingly, and finish the proof *)
      apply Rmult_le_reg_l with (2*d^2*n). 
       apply Rmult_lt_0_compat; nra.
      field_simplify. 2: lra.
      etransitivity; swap 1 2.
       apply Rmult_le_compat_r. lra.
       apply Rmult_le_compat_l. nra.
      apply Rlt_le, nup_above.
      field_simplify. 2: lra.
      transitivity (4*M*(x*(1-x))). lra. 
      erewrite Rmult_le_compat_l. 3: now apply Weierstrass_aux2.
      lra. lra.
Qed.

(** then on an arbitrary interval [a;b] *)

Definition scale a b x := a + (b-a)*x.
Lemma scale01 a b x: a<=b -> 0<=x<=1 -> a<=scale a b x<=b.
Proof. intros. unfold scale; nra. Qed.

Definition unscale a b x := (x-a)/(b-a).
Lemma unscale01 a b x: a<b -> a<=x<=b -> 0<=unscale a b x<=1.
Proof.
  intros. unfold unscale.
  split; apply Rmult_le_reg_l with (b-a); field_simplify; lra. 
Qed.

Lemma scale_unscale a b x: a<b -> scale a b (unscale a b x) = x.
Proof. intro. unfold scale, unscale. field. lra. Qed.
       
Notation scale' f a b := (fun x => f (scale a b x)). 
Notation unscale' f a b := (fun x => f (unscale a b x)). 

Corollary Weierstrass f a b:
  (forall x, a<=x<=b -> continuous_at f x) ->
  forall e, 0<e -> exists p, is_poly p /\ norm_inf a b f p e.
Proof.
  intros C e E.
  case: (Rlt_le_dec a b)=>[AB|BA]. 
  - destruct (fun C => Weierstrass01 (scale' f a b) C e E) as (p&P&N). {
      intros x X. apply continuous_comp.
      apply continuous_plus. apply continuous_cst. apply continuous_mult. apply continuous_cst. apply continuous_id.
      apply C. apply scale01; lra.
    }
    exists (unscale' p a b). split. 
     apply is_poly_comp. assumption. apply is_poly_mult. apply is_poly_plus. apply is_poly_id. apply is_poly_cst. apply is_poly_cst.
    intros x X.
    specialize (N (unscale a b x)).
    simpl in N. rewrite scale_unscale// in N.
    apply N. by apply unscale01. 
  - exists (fun _ => f a). split. apply is_poly_cst.
    intros x X. replace x with a by lra. split_Rabs; lra. 
Qed.

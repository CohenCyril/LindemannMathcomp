(* --------------------------------------------------------------------
 * (c) Copyright 2014--2015 INRIA.
 *
 * You may distribute this file under the terms of the CeCILL-B license
 * -------------------------------------------------------------------- *)

Require Import Reals RInt Psatz.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import finfun div binomial bigop prime ssralg poly ssrnum ssrint.
Require Import ssrcomplex Rstruct Cstruct intdiv Canalysis polydiv Hierarchy.
Require Import tuple perm.

Ltac tlia := try lia.
Ltac tlra := try lra.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.
Import GRing.Theory.
Import Num.Def.
Import Num.Theory.
Import Pdiv.Ring.

Section Poly_mrootRing.

Variable R : ringType.

Lemma derivX_XsubC (c : R) n :
  (('X - c%:P) ^+ n) ^`() = ('X - c%:P) ^+ n.-1  *+ n.
Proof.
case: n; first by rewrite expr0 derivC.
elim => [| n ihn]; first by rewrite expr1 /= expr0 derivXsubC.
rewrite -addn1 exprD !derivE expr1 ihn mulr1 -pred_Sn.
by rewrite addn1 /= mulrnAl -!exprSr -mulrSr.
Qed.

Definition mroot (p : {poly R}) m x := rdvdp (('X - x%:P) ^+ m) p.

Lemma mrootP p m x :
  reflect (exists q, p = q * ('X - x%:P) ^+ m ) (mroot p m x).
Proof.
by apply:(iffP (Pdiv.RingMonic.rdvdpP _ p)); rewrite ?monic_exp ?monicXsubC.
Qed.

Lemma mrootdP p m x :
  reflect (forall i : 'I_m, mroot p^`(i) (m - i) x) (mroot p m x).
Proof.
apply:(iffP idP); last first.
  case: m.
    by move=> H; apply/mrootP; exists p; rewrite expr0 mulr1.
  by move=> n /(_ (ord0)); rewrite subn0 derivn0.
move=>  H; case; elim=> [/=  _|n IHn Hn]; first by rewrite subn0.
apply/mrootP; rewrite derivnS /=.
move/(ltn_trans(ltnSn n)):Hn =>Hn1.
move/mrootP :(IHn Hn1)=>[r /= Hr].
rewrite Hr derivM derivX_XsubC -{1}[(m -n)%N]prednK; last by rewrite subn_gt0.
exists (r^`() * ('X - x%:P) + r *+ (m-n)).
by rewrite mulrDl exprS mulrA mulrnAl subnS mulrnAr.
Qed.

Lemma mroot_root p m x :
  (0 < m)%N -> mroot p m x -> root p x.
Proof.
move=> Hle /mrootP [q Heq]; apply/factor_theorem.
exists (q * ('X - x%:P)^+ m.-1).
by rewrite Heq -{1}(prednK Hle) exprSr mulrA.
Qed.

Lemma mroot0 p x : mroot p 0 x.
Proof. by apply/mrootP; rewrite expr0; exists p; rewrite mulr1. Qed.

Lemma root_mroot p x : root p x -> mroot p 1 x.
Proof. by move=> /factor_theorem H; apply/mrootP; rewrite expr1. Qed.

End Poly_mrootRing.

Section Poly_mrootCRing.

Variable R : comRingType.

Lemma mrootM (p : {poly R}) mp q mq x :
  mroot p mp x -> mroot q mq x -> mroot (p * q) (mp + mq) x.
Proof.
move=> /mrootP [pr Hpr] /mrootP [qr Hqr]; apply/mrootP.
exists (pr * qr); rewrite Hpr Hqr.
by rewrite -!mulrA !(mulrC qr) exprD -!mulrA.
Qed.

Lemma mrootX (p : {poly R}) n x : root p x -> mroot (p ^+ n) n x.
Proof.
move=> H.
elim: n => [|n ihn]; first by apply: mroot0.
by rewrite exprS -add1n; apply: mrootM => //; apply: root_mroot.
Qed.

End Poly_mrootCRing.

Open Scope nat_scope.

(* Stolen from the development branch of math-comp: to be removed at 
   relevant release.  These two lemmas prove the infinity of prime numbers. *)
Lemma dvdn_fact m n : 0 < m <= n -> m %| n`!.
Proof.
case: m => //= m; elim: n => //= n IHn; rewrite ltnS leq_eqVlt.
by case/predU1P=> [-> | /IHn]; [apply: dvdn_mulr | apply: dvdn_mull].
Qed.

Lemma prime_above m : {p | m < p & prime p}.
Proof.
have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1 by rewrite addn1 ltnS fact_gt0.
exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m.
by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.

Section working_context.

Open Scope ring_scope.

Variable n : nat.
Hypothesis n_neq0 : n != 0%N.
Variable k : int.
Hypothesis k_neq0 : k != 0.
Variable gamma : nat -> int.
Variable c : nat.
Hypothesis c_neq0 : c != 0%N.
Variable alpha : nat -> complexR.
Hypothesis alpha_neq0 : forall (i: 'I_n), alpha i != 0.

(**** * T * ****)
Definition T := \prod_(i < n) ('X - (alpha i)%:P) *+ c.

Fact cR_neq0 : c%:R != 0%R :> complexR.
Proof. by rewrite pnatr_eq0. Qed.
Hint Resolve cR_neq0.

Lemma size_T : size T = n.+1.
Proof.
rewrite /T -scaler_nat size_scale //.
rewrite size_prod; last by move=> i _; rewrite polyXsubC_eq0.
rewrite card_ord (eq_bigr (fun=> 2)) => [|i _]; last by rewrite size_XsubC.
by rewrite sum_nat_const card_ord mulnS muln1 -addSn addnK.
Qed.

Lemma T_neq0 : T != 0.
Proof. by rewrite -size_poly_eq0 size_T -lt0n ltn0Sn. Qed.

Lemma T0_neq0 : T.[0] != 0.
Proof.
rewrite hornerMn horner_prod mulrn_eq0 negb_or c_neq0 /=.
by apply/prodf_neq0 => i _; rewrite hornerXsubC add0r oppr_eq0 alpha_neq0.
Qed.

Lemma root_T (j : nat) : (j < n)%N -> root T (alpha j).
Proof.
move=> Hle; rewrite /T /root hornerMn horner_prod mulrn_eq0 (negPf c_neq0) //.
by apply/prodf_eq0; exists (Ordinal Hle) => //=; rewrite hornerXsubC subrr.
Qed.

(**** * Variables to choose the prime number p **** *)

Lemma ex_Mc i :
 {M : R | forall x : R, 0 <= x <= 1 -> norm T.[alpha i * x%:C] < M}.
Proof.
move: (Continuity.bounded_continuity
          (fun y => (T.[(alpha i)*y%:C])) 0 1) => H.
have : forall x : R,
       and (Rle 0 x) (Rle x 1) ->
       filterlim (fun y : R => T.[alpha i * y%:C]) (locally x)
           (locally T.[alpha i * x%:C]).
  move=> x [/RleP H0 /RleP H1].
  apply: Crcontinuity_pt_filterlim.
  apply: (@Crcontinuity_pt_ext (fun y => (T \Po ((alpha i) *: 'X )).[y%:C]) ).
    by move=> z; rewrite horner_comp hornerZ hornerX.
  by apply: Crcontinuity_pt_poly.
move=> Hb; move: (H Hb) => [M M_H].
by exists M; move=> x /andP[H0 H1]; apply/RltP; apply: M_H; split; apply/RleP.
Qed.

Definition M i := sval (ex_Mc i).

Definition A i :=  norm (alpha i) * norm (exp (Rmax 0 (Re (-alpha i)))) * M i.

Definition B i :=  norm (alpha i) * M i.

Definition An := ((\max_(i : 'I_n)
 Num.bound (norm (((- gamma i)%:~C * Cexp(alpha i))%R : complexR)))
*  \max_(i : 'I_n) (Num.bound (`|A i|)))%N.

Definition Bn := \max_(i : 'I_n) (Num.bound (`|B i|)).

Open Scope nat_scope.

Definition a := c ^ n * (n * An).
Definition b := c ^ n * Bn.

Lemma p_prop2 :
  exists p : nat, prime p && (a * b ^ p.-1 < (p.-1)`!) &&  (p > `|k|) &&
      (p >  `| floorC (T.[0])|) && (p > c).
Proof.
destruct (p_prop1 a b) as [q Pq].
set q' := maxn q (maxn (maxn `|k| c) (`| floorC (T.[0])|)).
case: (prime_above q') => p Hmax isPrime.
exists p; rewrite isPrime.
move: Hmax; rewrite !gtn_max => /and3P [H1 /andP[-> ->] ->].
by rewrite Pq // -ltnS (ltn_predK H1).
Qed.

Definition p := xchoose p_prop2.

Lemma prime_p : prime p.
Proof. by move: (xchooseP p_prop2) => /andP [/andP [/andP [/andP [->]]]]. Qed.

Lemma leq_pk : p > `|k|.
Proof. by move: (xchooseP p_prop2) => /andP [/andP [/andP [H ->]]]. Qed.
Hint Resolve leq_pk.

Lemma leq_T : (p > ( `| floorC T.[0]|)).
Proof. by move: (xchooseP p_prop2) => /andP [/andP [H ->]]. Qed.

Lemma leq_c : c < p.
Proof. by move: (xchooseP p_prop2) => /andP [/andP [H H1]] ->. Qed.

Lemma majoration : a * b ^ p.-1 < (p.-1)`!.
Proof. by move:(xchooseP p_prop2) => /andP [/andP [/andP [/andP [H ->]]]]. Qed.

Lemma p_gt0 : (0 < p)%N.
Proof. by exact: leq_ltn_trans (leq0n _) leq_c. Qed.
Hint Resolve p_gt0.

Open Scope ring_scope.

Definition Fp := ('X ^+ p.-1) * (T ^+ p)%R.

Lemma size_Fp : size Fp = (p * n.+1)%N.
Proof.
rewrite size_mul;  first last.
    by apply: expf_neq0; apply: T_neq0.
  by apply: monic_neq0; apply: monicXn.
rewrite size_polyXn (prednK p_gt0) mulnS.
have HS : (size (T ^+ p)).-1 = (p * n)%N.
  by rewrite size_exp size_T -pred_Sn mulnC.
rewrite -HS -!subn1 addnBA //.
apply: (@leq_trans  (size (T ^+ p)).-1 ); last by apply: leq_pred.
by rewrite HS muln_gt0 p_gt0 andTb lt0n n_neq0.
Qed.

Lemma Fp_neq0 : Fp != 0.
Proof. by rewrite -size_poly_gt0 size_Fp muln_gt0 p_gt0 ltn0Sn. Qed.

Lemma mroot_Fp :
  mroot Fp p.-1 0 /\ forall j,  (j < n)%N -> mroot Fp p (alpha j).
Proof.
split; first by apply/mrootP; exists (T ^+ p); rewrite subr0 mulrC.
move=> j Hle; rewrite -[p]add0n; apply: mrootM.
  by apply: mroot0.
by apply: mrootX; apply: root_T.
Qed.

Definition Sd (P : {poly complexR}) j0 := \sum_(j0 <= j < (size P)) P^`(j).

Lemma size_Sd (P : {poly complexR}) : P != 0 -> size (Sd P 0) = size P.
Proof.
move/polySpred ;
move Hs : (size P).-1 => q.
rewrite /Sd.
elim: q P Hs => [P Hs sP | q Ihq P Hs sP].
  by rewrite sP big_nat1 derivn0.
rewrite big_ltn ; last by rewrite sP.
rewrite derivn0 {1}sP size_addl // big_add1 -pred_Sn.
rewrite (@eq_big_nat _ _ _ _ _ _ (fun i : nat => derivn i (deriv  P) ) );
  last by move => i Hi; apply: derivSn.
suff Hp : (size (P^`()) = q.+1).
  rewrite -Hp Ihq //; last by rewrite Hp -pred_Sn.
  by rewrite lt_size_deriv // -size_poly_gt0 sP.
rewrite [q.+1]pred_Sn -sP /deriv size_poly_eq //.
rewrite sP -!pred_Sn -mulr_natr mulf_neq0 //;
  last by rewrite Num.Theory.pnatr_eq0.
by rewrite -[q.+1]/(q.+2.-1) -sP -lead_coefE lead_coef_eq0 -size_poly_gt0 sP.
Qed.

Definition IFp i :=  (Sd Fp 0).[0] - Cexp (-alpha i) * (Sd Fp 0).[alpha i].

Lemma Eq_IFp :
  k%:~R + (\sum_(0 <= i < n) (gamma i)%:~R * Cexp (alpha i)) = 0 ->
  k%:~R * (Sd Fp 0).[0] +
  \sum_(0 <= i < n) ((gamma i)%:~R * (Sd Fp 0).[alpha i])  =
  \sum_(0 <= i < n) (- ((gamma i)%:~R) * (Cexp ((alpha i)) * (IFp i))).
Proof.
move=> eq_caract.
have -> : \sum_(0 <= i < n) (-(gamma i)%:~R * (Cexp (alpha i) * IFp i)) =
  (\sum_(0 <= i < n) - (((gamma i)%:~R) * Cexp (alpha i))) * (Sd Fp 0).[0]
  - \sum_(0 <= i < n) - ((gamma i)%:~R * (Sd Fp 0).[alpha i]) .
  rewrite big_distrl /= -sumrB /IFp.
  apply: eq_big_nat => i Hineq.
  rewrite !mulrBr mulrA [X in _ - (-_ * X)]mulrA.
  by rewrite CexpRD subrr Cexp0 mul1r !mulNr.
move/eqP : eq_caract; rewrite eq_sym -subr_eq sub0r => /eqP <-.
by rewrite !sumrN opprK.
Qed.

(**** * Analysis part * ****)
Let contFpalpha i x : Crcontinuity_pt (fun y => Fp.[alpha i * y%:C]) x.
Proof.
apply: (@Crcontinuity_pt_ext (fun x => (Fp \Po (alpha i *: 'X)).[x%:C])).
  by move=> y; rewrite horner_comp hornerZ hornerX.
by apply Crcontinuity_pt_poly.
Qed.

Definition Qdalpha i := (Sd Fp 0) \Po ((alpha i) *: 'X).

Lemma Qdalpha_Fpd i x: (Sd Fp 0).[alpha i * x%:C] = (Qdalpha i).[x%:C].
Proof.
by rewrite /Qdalpha horner_comp hornerZ hornerX.
Qed.

Lemma Qderiv_derive x i :
  alpha i * (Qdalpha i).[x%:C] - Crderive (fun y => (Qdalpha i).[y%:C]) x =
  alpha i * Fp.[(alpha i)*x%:C].
Proof.
rewrite Crderive_poly /Qdalpha deriv_comp horner_comp hornerM.
rewrite horner_comp derivZ derivX alg_polyC hornerC mulrC.
rewrite hornerZ hornerX -mulrBr -hornerN -hornerD.
have: (Sd Fp 0 - (Sd Fp 0)^`() = Fp) => [|-> //].
rewrite big_endo; first last.
    by rewrite deriv0.
  by apply: derivD.
rewrite /Sd.
move Hs : (size Fp) => m; case: m Hs => [Hs| m Hs].
  rewrite !big_mkord !big_ord0 subrr.
  by apply/eqP; rewrite eq_sym; rewrite -size_poly_eq0; apply/eqP.
rewrite big_nat_recl //.
set S :=  \sum_(0 <= i0 < m) Fp^`(i0.+1).
rewrite big_nat_recr //= -derivnS.
have: (Fp^`(m.+1)) = 0 => [|->].
  by apply: derivn_poly0; apply: eq_leq.
rewrite addr0 (@eq_big_nat _ _ _ _ _ _ (fun i => Fp^`(i.+1))).
  by rewrite /S addrK.
by move=> j Hineq; rewrite derivnS.
Qed.

Lemma Fp_Crderive x i :
  Crderive (fun y => - (Qdalpha i).[y%:C] * Cexp(-alpha i * y%:C)) x =
    alpha i * Cexp(-alpha i * x%:C)*(Fp.[ alpha i *x%:C]).
Proof.
rewrite CrderiveM; last by apply: ex_Crderive_Cexp.
  rewrite CrderiveN; last by apply ex_Crderive_poly.
  rewrite Crderive_Cexp mulrA -mulrDl -mulrA (mulrC (Cexp _)) [RHS]mulrA.
  by rewrite addrC mulrNN [_ * alpha i]mulrC Qderiv_derive.
by apply/ex_CrderiveN/ex_Crderive_poly.
Qed.

Lemma CrInt_Fp i :
  CrInt (fun x => alpha i * Cexp(-alpha i * x%:C)*(Fp.[alpha i * x%:C]))
     0 1 = IFp i.
Proof.
set f := (fun x => alpha i * Cexp (- alpha i * x%:C) * Fp.[alpha i * x%:C]).
rewrite (@CrInt_ext _
           (Crderive (fun y => - (Qdalpha i).[y%:C] * Cexp(-alpha i * y%:C))));
   last first.
  by move=> x Hx; rewrite Fp_Crderive.
rewrite RInt_Crderive.
+ by rewrite /IFp -!Qdalpha_Fpd mulNr !mulr0 Cexp0 !mulr1 addrC mulrC opprK.
+ move=> x _; apply: ex_CrderiveM; last by apply: ex_Crderive_Cexp.
  by apply/ex_CrderiveN/ex_Crderive_poly.
move=> x _.
apply: (@Crcontinuity_pt_ext
           (fun x =>(alpha i)*Cexp((-alpha i)*x%:C)*(Fp.[(alpha i)*x%:C]))).
  by move=> y; rewrite -Fp_Crderive Crderive_C_eq.
apply: Crcontinuity_pt_mul; last by [].
apply: Crcontinuity_pt_mul.
  by apply: Crcontinuity_pt_const.
by apply: Crcontinuity_pt_exp.
Qed.   

Lemma ex_RInt_Fp i :
  ex_RInt (fun x => alpha i * Cexp(-alpha i * x%:C)*(Fp.[alpha i * x%:C])) 0 1.
Proof.
apply: ex_RInt_cont_C => x H.
apply: Crcontinuity_pt_mul; last by [].
apply: Crcontinuity_pt_mul; first by apply: Crcontinuity_pt_const.
by apply: Crcontinuity_pt_exp.
Qed.

Lemma maj_IFpa i :
  norm (IFp i) <=
  RInt (fun x => norm (alpha i * Cexp(-alpha i * x%:C)*(Fp.[alpha i * x%:C])))
     0 1.
Proof.
rewrite -CrInt_Fp.
apply: CrInt_norm; first by apply: ler01.
move=> x Hineq; apply: Crcontinuity_pt_mul => //; apply: Crcontinuity_pt_mul.
  by apply: Crcontinuity_pt_const.
by apply: Crcontinuity_pt_exp.
Qed.

(* TODO : the "complexR" annotation is necessary in this statement, why? *)
Lemma maj_IFpb i :
  RInt (fun x => norm (alpha i * Cexp(-alpha i * x%:C)*(Fp.[alpha i *x%:C])))
     0 1 =
  norm (alpha i) *
  RInt (fun x =>
            norm (Cexp(-alpha i * x%:C)*(Fp.[ alpha i * x%:C]) : complexR))
     0 1 .
Proof.
rewrite -Rmult_mul -RInt_scal; apply: RInt_ext=> x Hineq.
by rewrite -mulrA normM Rmult_mul.
Qed.

Lemma maj_IFpc i :
  RInt (fun x => norm (Cexp(-alpha i * x%:C)*(Fp.[alpha i * x%:C]) : complexR))
     0 1 <=
  RInt (fun x => norm ((exp(Rmax 0 (Re (-alpha i))))%:C * Fp.[alpha i * x%:C]
            : complexR)) 0 1.
Proof.
apply/RleP; apply: RInt_le; first by apply/RleP/ler01.
    apply: ex_CrInt_norm.
    by move=> x _; apply: Crcontinuity_pt_mul=>//; apply: Crcontinuity_pt_exp.
  apply: ex_CrInt_norm.
  by move=> x _; apply: Crcontinuity_pt_mul=>//; apply: Crcontinuity_pt_const.
move=> x [/RltP H0 /RltP H1].
apply/RleP.
rewrite normM [X in _ <= X]normM.
apply: ler_wpmul2r; first by apply/RleP; apply: norm_ge_0.
rewrite /Cexp /norm /=.
rewrite !mul0r !subr0 !addr0.
rewrite ReM ImM.
rewrite !exprMn -!mulrDr.
set im := Im (- alpha i).
have Htrigo y: (cos y) ^+ 2 + (sin y) ^+ 2 = 1.
  rewrite addrC !exprS !expr0 !mulr1 -Rplus_add -!Rmult_mul; exact: sin2_cos2.
rewrite !Htrigo !mulr1 expr0n /= addr0 !sqrtr_sqr.
rewrite !gtr0_norm.
    have : (Re (- alpha i) * x) <= (Rmax 0 (Re (- alpha i))).
      move: (num_real (Re (-alpha i))).
      rewrite realE.
      move=> /orP [Hpos| Hneg].
        apply: (@ler_trans _ (Re(-alpha i))).
          rewrite -[X in _<=X]mulr1.
          by apply: ler_wpmul2l=>//; apply: ltrW.
        by apply/RleP; apply: Rmax_r.
      apply: (@ler_trans _ (Re (-alpha i) *0)).
        by apply: ler_wnmul2l=> // ; apply:ltrW.
      by rewrite mulr0; apply/RleP; apply: Rmax_l.
    rewrite ler_eqVlt => /orP [/eqP Heq | Hlt].
      by rewrite Heq lerr.
    by apply: ltrW; apply/RltP; apply: exp_increasing; apply/RltP.
  by apply/RltP; apply: exp_pos.
by apply/RltP; apply: exp_pos.
Qed.

Lemma maj_IFpd i :
  RInt (fun x =>
         norm ((exp(Rmax 0 (Re (-alpha i))))%:C *
                Fp.[(alpha i)*x%:C] : complexR)) 0 1 =
  norm (exp(Rmax 0 (Re (-alpha i)))) *
  RInt (fun x => norm (Fp.[(alpha i)*x%:C])) 0 1.
Proof.
rewrite -Rmult_mul -RInt_scal; apply: RInt_ext => x Hineq.
rewrite Rmult_mul normM; congr (_ * _).
by rewrite /norm /= expr0n addr0 sqrtr_sqr.
Qed.

Lemma maj_IFpe i :
  RInt (fun x => norm (Fp.[(alpha i)*x%:C])) 0 1 <= 
  (norm (alpha i))^+ p.-1 * RInt (fun x => norm (T^+ p).[(alpha i)*x%:C]) 0 1.
Proof.
(* TODO : maybe this lemma should be moved close to normM. *)
have norm_exp : forall y n, norm (y ^+n : complexR) = (norm y)^+n.
  move=> y; elim => [|m Ihm].
    rewrite !expr0 /=.
    by rewrite /norm /= expr1n expr0n /= addr0 sqrtr1.
  by rewrite !exprS normM Ihm.
rewrite -Rmult_mul -RInt_scal.
apply/RleP; apply: RInt_le.
      by apply/RleP; apply: ler01.
    apply: (ex_RInt_ext
     (fun x : R => norm (horner Fp (alpha i * x%:C)))).
      by move=> x Hineq; rewrite /norm /=.
    by apply: ex_CrInt_norm.
  apply: (ex_RInt_ext (fun x =>
      (norm ((alpha i) ^+ p.-1 * (T ^+ p).[alpha i * x%:C])%R))).
    by move=> x Hineq; rewrite Rmult_mul normM norm_exp.
  apply: ex_CrInt_norm.
  move=> x Hineq.
  apply: Crcontinuity_pt_mul.
    by apply: Crcontinuity_pt_const.
  apply: (@Crcontinuity_pt_ext
             (fun y => ((T^+ p) \Po ((alpha i) *: 'X )).[y%:C]) ).
    by move=> y; rewrite horner_comp hornerZ hornerX.
  apply: Crcontinuity_pt_poly.
move=> x [/RltP/ltrW H0 /RltP/ltrW  H1]; apply/RleP.
rewrite Rmult_mul /Fp hornerM normM -norm_exp hornerXn exprMn normM.
rewrite [X in X*_]mulrC -mulrA -[X in _ <= X]mul1r.
apply: ler_wpmul2r.
  by apply: mulr_ge0; apply/RleP; apply: norm_ge_0.
rewrite norm_exp.
have: (norm (x%:C : complexR) = x) => [|->].
  by rewrite /norm /= expr0n /= addr0 sqrtr_sqr ger0_norm.
by apply: exprn_ile1.
Qed.

Lemma maj_IFpf i M :
  (forall x, 0 <= x <= 1 -> norm T.[(alpha i)*x%:C] <= M) ->
  RInt (fun x => norm (T^+ p).[(alpha i)*x%:C]) 0 1 <= M ^+ p.
Proof.
rewrite -(prednK p_gt0) //; set m := p.-1.
have HM: M = RInt (fun y => M) 0 1.
  rewrite RInt_const Rmult_mul /Rminus Ropp_opp Rplus_add.
  by rewrite subr0 mul1r.
move=> Hineq; elim: m => [| m Ihm].
  rewrite !expr1 HM.
  apply/RleP/RInt_le; first by apply/RleP/ler01.
      apply: ex_CrInt_norm.
      move=> x Hine.
      apply: (@Crcontinuity_pt_ext
                 (fun y => (T \Po ((alpha i) *: 'X )).[y%:C])).
        by move=> y; rewrite horner_comp hornerZ hornerX.
      by apply: Crcontinuity_pt_poly.
    apply: ex_RInt_const.
  move=> x [/RltP/ltrW H0 /RltP/ltrW H1].
  by apply/RleP/Hineq/andP.
rewrite exprS [X in _<=X]exprS.
apply: (@ler_trans _
           (M * (RInt (fun x : R => norm (T ^+ m.+1).[alpha i * x%:C]) 0 1))).
  rewrite -Rmult_mul -RInt_scal; apply/RleP/RInt_le;first by apply/RleP/ler01.
      apply: ex_CrInt_norm => x Hine.
      apply: (@Crcontinuity_pt_ext
                 (fun y => ((T * T ^+ m.+1) \Po ((alpha i) *: 'X )).[y%:C])).
        by move=> y; rewrite horner_comp hornerZ hornerX.
      by apply: Crcontinuity_pt_poly.
    apply/ex_RInt_scal/ex_CrInt_norm.
    move=> x Hine.
    apply: (@Crcontinuity_pt_ext
               (fun y => ((T ^+ m.+1) \Po ((alpha i) *: 'X )).[y%:C])).
      by move=> y; rewrite horner_comp hornerZ hornerX.
    by apply: Crcontinuity_pt_poly.
  move=> x [/RltP/ltrW H0 /RltP/ltrW H1].
  rewrite hornerM normM !Rmult_mul.
  apply/RleP/ler_wpmul2r; first by apply/RleP; apply: norm_ge_0.
  by apply/Hineq/andP.
apply: ler_wpmul2l; last by apply: Ihm.
apply: (ler_trans _ (Hineq 0 _)); last by rewrite lerr ler01.
by  apply/RleP/norm_ge_0.
Qed.

Lemma maj_IFp i :
  norm (IFp i) <= (`|A i| * `|B i|^+p.-1) .
Proof.
apply: (ler_trans (maj_IFpa i)); rewrite maj_IFpb.
(* TODO : this is probably general enough to be in the main library. *)
have hnorm : forall (V : NormedModule R_AbsRing) (x : V), `|norm x| = norm x.
  by move=> V x; apply/normr_idP/RleP/norm_ge_0.
rewrite !normrM !hnorm -!mulrA; apply: ler_wpmul2l.
  by apply/RleP/norm_ge_0.
apply: (ler_trans (maj_IFpc i)).
rewrite maj_IFpd; apply: ler_wpmul2l; first by apply/RleP; apply: norm_ge_0.
apply: (ler_trans (maj_IFpe i)).
rewrite [X in _*X^+p.-1]mulrC exprMn mulrA mulrC.
apply: ler_wpmul2r; first by apply/exprn_ge0/RleP/norm_ge_0.
rewrite -exprS (prednK p_gt0) //.
have:M i ^+ p <= `|M i| ^+ p by rewrite -normrX; apply/real_ler_norm/num_real.
by apply/ler_trans/maj_IFpf => x inx; apply/ltrW/(svalP (ex_Mc i)).
Qed.

Lemma eq_ltp1 :
  `|(c ^ (n * p))%:R *
       \sum_(0 <= i < n) -(gamma i)%:~R * (Cexp (alpha i) * IFp i)|
   < ((p.-1)`!)%:R.
Proof.
move: majoration; rewrite -ltC_nat; apply : ler_lt_trans.
rewrite mulr_natl normrMn -mulnA -mulnA natrM mulr_natl mulnA.
rewrite expnMn mulnCA natrM mulr_natl -mulrnA -expnSr prednK // -expnM.
rewrite ler_pmuln2r; last by rewrite expn_gt0 lt0n c_neq0.
apply : (ler_trans (ler_norm_sum _ _ _)).
have -> :  (n * An * Bn ^ p.-1)%:R = \sum_(0 <= i < n) ((An * Bn ^ p.-1)%:R).
  by move=> t; rewrite -mulnA -natr_sum sum_nat_const_nat subn0.
rewrite big_nat_cond [ X in _ <= X]big_nat_cond; apply: ler_sum.
move=> i /andP [/andP [Hi0 Hin] _].
rewrite mulrA normrM lecE; simpl Im; rewrite !mulr0 !mul0r addr0.
rewrite -{1}natzc -{1}intrc Im_int eq_refl andTb.
have Re_natM : forall x y: nat, Re ((x * y)%:R  : complexR) = x%:R * y %:R.
  by move => x y; rewrite -natrc -intrc Re_int natrM intrM !mulrz_nat.
rewrite Re_natM natrX.
have cmpa : (Num.bound (norm (((- gamma i)%:~R * Cexp(alpha i))%R : complexR))
              * Num.bound `|A i|)%:R  <= An%:R :> R.
  have -> : i = nat_of_ord (Ordinal Hin) by [].
  by rewrite ler_nat /An -intrc leq_mul //; apply: leq_bigmax.
move: (maj_IFp i); rewrite /norm /= => HIFp.
have ltI : norm (-(gamma i)%:~R * Cexp (alpha i) : complexR) * norm (IFp i) <=
  norm (-(gamma i)%:~R * Cexp (alpha i) : complexR) * `|A i| * `|B i| ^+ p.-1.
  rewrite -mulrA ler_wpmul2l //; apply/RleP; exact: norm_ge_0.
rewrite mulr0 subr0; apply: (ler_trans ltI) => {ltI HIFp}.
have Hltr :  norm (- (gamma i)%:~R * Cexp (alpha i) : complexR) * `|A i| <=
   (Num.bound (norm ((- gamma i)%:~R * Cexp (alpha i) : complexR)) *
           Num.bound `|A i|)%:R .
  rewrite natrM; apply: ler_pmul; first by apply/RleP; apply: norm_ge_0.
      by apply: normr_ge0.
    by apply: ltrW; rewrite mulrNz; apply/archi_boundP/RleP/norm_ge_0.
  by apply/ltrW/archi_boundP/normr_ge0.
move: (ler_trans Hltr cmpa) => {cmpa Hltr} ineq.
apply: ler_pmul => //.
    apply: mulr_ge0; first by apply/RleP; apply: norm_ge_0.
    by apply: normr_ge0.
  by apply: exprn_ge0; apply: normr_ge0.
apply: ler_expn2r => {ineq}; rewrite 1?nnegrE; first by apply: normr_ge0.
  by apply: ler0n.
apply: (@ler_trans _ (Num.bound `|B i|)%:R).
  by apply/ltrW/archi_boundP/normr_ge0.
by rewrite (_ : i = nat_of_ord (Ordinal Hin)) // ler_nat; apply: leq_bigmax.
Qed.

(**** * Algebra part * ****)

Section T_int.

Hypothesis T_Cint :  T \is a polyOver Cint.

Definition pred_rules_1 := 
  (T_Cint, rpred_horner, rpredM, rpredD, rpredMn, rpredX, polyOverX).

Lemma polyOver_Fp : Fp \is a polyOver Cint.
Proof. by rewrite !pred_rules_1. Qed.

Lemma polyOver_Fpd j0 : (Sd  Fp j0) \is a polyOver Cint.
Proof. by apply: rpred_sum => i _; apply/polyOver_derivn/polyOver_Fp. Qed.

Lemma Fp0_re : (Fp^`(p.-1)).[0] = (T^+p).[0] *+ (p.-1`!).
Proof.
rewrite /Fp; elim: p.-1 => [|q ihq].
  by rewrite derivn0 fact0 mulr1n expr0 mul1r.
rewrite exprS -mulrA mulrC -[X in X ^`(q.+1)]addr0 derivnMXaddC hornerD.
by rewrite hornerM hornerX mulr0 addr0 hornerMn ihq -mulrnA factS mulnC.
Qed.

Lemma pre_G_Cint : Fp^`N(p) \is a polyOver Cint.
Proof. by apply/polyOver_nderivn/polyOver_Fp. Qed.

Definition G : {poly complexR} := \sum_(0 <= j < p * n) Fp^`N(p)^`(j).

Lemma G_Cint : G \is a polyOver Cint.
Proof.
by apply:rpred_sum=> j _; apply/polyOver_derivn/polyOver_nderivn/polyOver_Fp.
Qed.

Definition pred_rules := (G_Cint, pred_rules_1).

(* TODO : this is very general and should be migrated to poly *)
Lemma derivn_add {R : ringType} (p : {poly R}) i j : p^`(i+j) = p^`(i)^`(j).
Proof. by rewrite addnC [LHS]iter_add. Qed.

Lemma G_sum : G *+ (p`!) = \sum_(p <= j < size Fp) Fp^`(j).
Proof.
rewrite /G -mulr_natr big_distrl /= size_Fp mulnS addnC -{4}(add0n p).
rewrite big_addn addnK; apply: eq_bigr => i _.
by rewrite mulr_natr -derivnMn -!nderivn_def addnC derivn_add.
Qed.

Lemma size_G : (size G = p * n)%N.
Proof.
have -> : size G = size (G *+ (p`!)).
  by rewrite -scaler_nat size_scale // pnatr_eq0 -lt0n fact_gt0.
rewrite G_sum (_ : \sum_(p <=j< size Fp) Fp^`(j)=(Sd (Fp^`(p)) 0)); last first.
  rewrite /Sd Cr_size_derivn size_Fp -{1}[p]add0n big_addn.
  by apply: eq_bigr => i _; rewrite addnC derivn_add.
rewrite size_Sd.
  by rewrite Cr_size_derivn size_Fp mulnS -{3}[p]addn0 subnDl subn0.
rewrite -size_poly_eq0 Cr_size_derivn size_Fp mulnS -{3}[p]addn0 subnDl subn0.
by rewrite muln_eq0 negb_or n_neq0 -lt0n p_gt0.
Qed. 

Lemma Fpdalpha_re i : (i < n)%N -> (Sd Fp 0).[alpha i] = G.[alpha i] *+ p`!. 
Proof. 
move: mroot_Fp => [_ H] Hi; move: (H i Hi)=> {H} /mrootdP H.
rewrite -hornerMn G_sum /Sd size_Fp mulnS addnC. 
rewrite (@big_cat_nat _ _ _ p) /= ?hornerD ?horner_sum ?leq0n //; first last. 
  by rewrite -{1}[p]add0n leq_add2r leq0n. 
rewrite (@eq_big_nat _ _ _ _ _ _ (fun i => 0));first by rewrite big1_eq add0r.
move=> j /andP [_ C].
by apply/rootP/(mroot_root _ (H (Ordinal C)));rewrite subn_gt0.
Qed. 

Lemma Fpd0_re : (Sd Fp 0).[0] = Fp^`(p.-1).[0] + G.[0] *+ p`!.
Proof.
move: mroot_Fp => [/mrootdP H _].
rewrite -hornerMn G_sum /Sd /G size_Fp mulnS addnC.
have plpnp : (p <= p * n + p)%N  by rewrite -{1}[p]add0n leq_add2r leq0n.
rewrite (big_cat_nat _ _ _ (leq0n p.-1)) /=; last first.
    by rewrite (leq_trans (leq_pred p)).
rewrite hornerD horner_sum (@eq_big_nat _ _ _ _ _ _ (fun i : nat => 0%R)).
  by rewrite big1_eq add0r big_ltn_cond ?hornerD ?(prednK p_gt0).
move=> j /andP [_ Hpi].
move: (H (Ordinal Hpi)) => {H} /= H.
by move: Hpi; rewrite -subn_gt0 => Hpi; move: (mroot_root Hpi H) => /rootP.
Qed.

Lemma Fp_dp1_div_props :
    ~~ ((p`!) %C| Fp^`(p.-1).[0] *+ (c ^ (n * p))) 
    /\ ((p.-1`!) %C| Fp^`(p.-1).[0] *+ c ^ (n * p)). 
Proof.
have HT : T.[0] \in Cint by rewrite !pred_rules.
rewrite Fp0_re; split.
  rewrite horner_exp -{4}(prednK p_gt0) factS (prednK p_gt0) mulrnAC.
  rewrite -mulr_natr -natzc PoszM dvdC_mul2r -?lt0n ?fact_gt0 //.
  rewrite dvdC_int; last by rewrite !pred_rules.
  rewrite expnM -exprMn_n floorCX; last by rewrite !pred_rules.
  rewrite abszX (Euclid_dvdX _ _ prime_p) p_gt0 andbT.
  rewrite -mulr_natr floorCM //; last by rewrite !pred_rules.
  rewrite abszM (_ : (`|floorC (c^n)%:R| = truncC (c^n)%:R)%N); last first.
    by rewrite /truncC ler0n.
  rewrite natCK (Euclid_dvdM _ _ prime_p).
  rewrite (Euclid_dvdX _ _ prime_p) lt0n n_neq0 andbT.
  rewrite (gtnNdvd _ leq_c); last by rewrite lt0n c_neq0.
  rewrite orbF (gtnNdvd _ leq_T) // lt0n absz_eq0.
  by rewrite -(eqr_int complexR_numDomainType) (floorCK HT) T0_neq0.
rewrite mulrnAC -mulr_natr -natzc dvdC_mull //.
by rewrite horner_exp expnM -exprMn_n; apply/rpredX/rpredMn.
Qed.

Lemma Fpd0_div :
    ~~ ((p`!) %C| (Sd Fp 0).[0] *+ c ^ (n * p)) /\
        ((p.-1`!) %C| (Sd Fp 0).[0] *+ c ^(n * p)).
Proof.
move: (Fp_dp1_div_props) => [H1 H2].
rewrite Fpd0_re // -mulr_natr mulrDl !mulr_natr mulrnAC; split.
  by rewrite dvdCMnD // -?lt0n ?fact_gt0 // !pred_rules.
rewrite -{4}(prednK p_gt0) factS mulrnA dvdCMnD -?lt0n ?fact_gt0 //.
by rewrite !pred_rules.
Qed.

Section Sum_G_alpha_int.

Variable sum_G_alpha_int :
   \sum_(0 <= i < n) (gamma i)%:~R * G.[alpha i] *+ c ^ (n * p) \in Cint.

Lemma Fpdalpha_div :
    ~~ (p`! %C|  
          (c ^ (n * p))%:R * k%:~R * (Sd Fp 0).[0] + 
          (c ^ (n * p))%:R *
                  \sum_(0 <= i < n) (gamma i)%:~R * (Sd Fp 0).[alpha i]) /\
    ((p.-1)`! %C|
          (c ^ (n * p))%:R * k%:~R * (Sd Fp 0).[0] + 
          (c ^ (n * p))%:R *
                  \sum_(0 <= i < n) ((gamma i)%:~R * (Sd Fp 0).[alpha i])).
Proof.
rewrite big_distrr /= !mulr_natl.
set a := (\sum_(0 <= i < n) _).
have -> : a = (\sum_(0 <= i < n) 
                ((gamma i)%:~R * G.[alpha i] *+ c ^ (n * p))) *+ p`!.
  rewrite /a -[X in _ = X]mulr_natr big_distrl /=.
  rewrite  big_nat_cond [X in _ = X]big_nat_cond; apply: eq_bigr => i.
  rewrite andbT => /andP [_ Hi].
  rewrite -[X in _ = X * _]mulr_natr mulrC -!mulrA; congr (_ * _).
  rewrite [X in _ = _ * X]mulrC mulrA; congr (_ * _).
  by rewrite Fpdalpha_re // mulr_natr.
split => {a}.
  rewrite dvdCMnD //; last by rewrite -lt0n fact_gt0.
  rewrite mulrnAl -mulrnAr.
  move: Fpd0_div => [] H1 /dvdCP [b bint Hb].
  move: H1; rewrite Hb.
  have simp_fact_div x : (p`! %C| x * (p.-1)`!%:~R) = (p %C| x).
    rewrite -{2}(prednK p_gt0) factS (prednK p_gt0) PoszM dvdC_mul2r //.
    by rewrite -lt0n fact_gt0.
  rewrite simp_fact_div => Hbp.
  have kint : k%:~R \in Cint by apply: Cint_int. 
  rewrite mulrA simp_fact_div.
  rewrite dvdC_int; last by apply: rpredM.
  rewrite floorCM // abszM intCK (Euclid_dvdM _ _ prime_p).
  by rewrite (gtnNdvd _ leq_pk) ?orFb ?absz_gt0 -?dvdC_int.
apply: rpredD.
  rewrite mulrnAl -mulrnAr mulrC.
  by apply/(dvdC_mulr _   (proj2 Fpd0_div))/Cint_int.
rewrite -{2}(prednK p_gt0) factS (prednK p_gt0) mulrnA dvdCMn ?rpredMn //.
by rewrite -lt0n fact_gt0.
Qed.

Lemma eq_gep1 :
  (p.-1`!)%:R <= `|(c^(n * p))%N%:R * (k%:~R) * (Sd Fp 0).[0] + 
  ((c^(n*p))%N%:R * \sum_(0 <= i < n) ((gamma i)%:~R * (Sd Fp 0).[alpha i]))|.
Proof. 
move/and_comm:Fpdalpha_div => [] /dvdCP [z zint Hz].
rewrite Hz -{2}(prednK p_gt0) factS (prednK p_gt0) PoszM.
rewrite dvdC_mul2r; last by rewrite -lt0n fact_gt0. 
move=> {Hz} /negP => /dvdC_neq0 => Hz. 
by rewrite mulr_natr normrMn ler_muln2r (norm_Cint_ge1 zint Hz) orbT.
Qed.

End Sum_G_alpha_int.

End T_int.

Lemma main_contradiction :
  \prod_(i < n) ('X - (alpha i)%:P) *+ c \is a polyOver Cint ->
  k%:~R + \sum_(0 <= i < n) (gamma i)%:~R * Cexp (alpha i) = 0 ->
  ~ ((\sum_(0 <= i < n) ((gamma i)%:~R * (G.[alpha i]) *+ c^(n*p)))
   \in Cint). 
Proof. 
move=> T_Cint eq_caract /eq_gep1.
rewrite -mulrA -mulrDr (Eq_IFp eq_caract) /T => Hge.
by move: (ler_lt_trans (Hge T_Cint) eq_ltp1); rewrite ltrr.
Qed.

End working_context.

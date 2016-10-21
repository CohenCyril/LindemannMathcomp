(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import all_ssreflect ssrnum ssralg ssrint div intdiv poly bigop.
From mathcomp
Require Import polydiv.

(*****************************************************************************)
(*                                                                           *)
(* This file defines some notations and properties of numArchiDomains        *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section SubArchiDomain.

Variable R : numArchiDomainType.

Local Notation Subreal := (@Num.Def.Rreal R).
Local Notation ZtoC := (intr : int -> R).

Lemma floorSub_subproof x : {i | x \is Subreal -> ZtoC i <= x < ZtoC (i + 1) }.
Proof.
have [Rx | _] := boolP (x \is Subreal); last by exists 0.
without loss x_ge0: x Rx / x >= 0.
  have [x_ge0 | /ltrW x_le0] := real_ger0P Rx; first exact.
  case/(_ (- x)) => [||m /(_ isT)]; rewrite ?rpredN ?oppr_ge0 //.
  rewrite ler_oppr ltr_oppl -!rmorphN opprD /= ltr_neqAle ler_eqVlt.
  case: eqP => [-> _ | _ /and3P[lt_x_m _ le_m_x]].
    by exists (- m) => _; rewrite lerr rmorphD ltr_addl ltr01.
  by exists (- m - 1); rewrite le_m_x subrK.
have /ex_minnP[n lt_x_n1 min_n]: exists n, x < n.+1%:R.
  exists (Num.ExtraDef.archi_bound x).
  by apply: (ltr_trans (archi_boundP x_ge0)); rewrite ltr_nat.
exists n%:Z => _; rewrite addrC -intS lt_x_n1 andbT.
case Dn: n => // [n1]; rewrite -Dn.
have [||//|] := @real_lerP _ n%:R x; rewrite ?rpred_nat //.
by rewrite Dn => /min_n; rewrite Dn ltnn.
Qed.

Definition floorSub x := sval (floorSub_subproof x).
Definition Subint : pred_class := fun x : R => (floorSub x)%:~R == x.

Definition truncSub x := if x >= 0 then `|floorSub x|%N else 0%N.
Definition Subnat : pred_class := fun x : R => (truncSub x)%:R == x.

(* Integer subset. *)

Lemma floorSub_itv x : x \is Subreal -> (floorSub x)%:~R <= x < (floorSub x + 1)%:~R.
Proof. by rewrite /floorSub => Rx; case: (floorSub_subproof x) => //= m; apply. Qed.

Lemma floorSub_def x m : m%:~R <= x < (m + 1)%:~R -> floorSub x = m.
Proof.
case/andP=> lemx ltxm1; apply/eqP; rewrite eqr_le -!ltz_addr1.
have /floorSub_itv/andP[lefx ltxf1]: x \is Subreal.
  by rewrite -[x](subrK m%:~R) rpredD ?realz ?ler_sub_real.
by rewrite -!(ltr_int R) 2?(@ler_lt_trans _ x).
Qed.

Lemma intSubK : cancel intr floorSub.
Proof.
by move=> m; apply: floorSub_def; rewrite ler_int ltr_int ltz_addr1 lerr.
Qed.

Lemma floorSubK : {in Subint, cancel floorSub intr}. Proof. by move=> z /eqP. Qed.

Lemma floorSub0 : floorSub 0 = 0. Proof. exact: (intSubK 0). Qed.
Lemma floorSub1 : floorSub 1 = 1. Proof. exact: (intSubK 1). Qed.
Hint Resolve floorSub0 floorSub1.

Lemma floorSubpK (p : {poly R}) :
  p \is a polyOver Subint -> map_poly intr (map_poly floorSub p) = p.
Proof.
move/(all_nthP 0)=> Zp; apply/polyP=> i.
rewrite coef_map coef_map_id0 //= -[p]coefK coef_poly.
by case: ifP => [/Zp/floorSubK // | _]; rewrite floorSub0.
Qed.

Lemma floorSubpP (p : {poly R}) :
  p \is a polyOver Subint -> {q | p = map_poly intr q}.
Proof. by exists (map_poly floorSub p); rewrite floorSubpK. Qed.

Lemma Subint_int m : m%:~R \in Subint.
Proof. by rewrite unfold_in intSubK. Qed.

Lemma SubintP x : reflect (exists m, x = m%:~R) (x \in Subint).
Proof.
by apply: (iffP idP) => [/eqP<-|[m ->]]; [exists (floorSub x) | apply: Subint_int].
Qed.

Lemma floorSubD : {in Subint & Subreal, {morph floorSub : x y / x + y}}.
Proof.
move=> _ y /SubintP[m ->] Ry; apply: floorSub_def.
by rewrite -addrA 2!rmorphD /= intSubK ler_add2l ltr_add2l floorSub_itv.
Qed.

Lemma floorSubN : {in Subint, {morph floorSub : x / - x}}.
Proof. by move=> _ /SubintP[m ->]; rewrite -rmorphN !intSubK. Qed.

Lemma floorSubM : {in Subint &, {morph floorSub : x y / x * y}}.
Proof. by move=> _ _ /SubintP[m1 ->] /SubintP[m2 ->]; rewrite -rmorphM !intSubK. Qed.

Lemma floorSubX n : {in Subint, {morph floorSub : x / x ^+ n}}.
Proof. by move=> _ /SubintP[m ->]; rewrite -rmorphX !intSubK. Qed.

Lemma rpred_Subint S (ringS : subringPred S) (kS : keyed_pred ringS) x :
  x \in Subint -> x \in kS.
Proof. by case/SubintP=> m ->; apply: rpred_int. Qed.

Lemma Subint0 : 0 \in Subint. Proof. exact: (Subint_int 0). Qed.
Lemma Subint1 : 1 \in Subint. Proof. exact: (Subint_int 1). Qed.
Hint Resolve Subint0 Subint1.

Fact Subint_key : pred_key Subint. Proof. by []. Qed.
Fact Subint_subring : subring_closed Subint.
Proof.
by split=> // _ _ /SubintP[m ->] /SubintP[p ->];
    rewrite -(rmorphB, rmorphM) Subint_int.
Qed.
Canonical Subint_keyed := KeyedPred Subint_key.
Canonical Subint_opprPred := OpprPred Subint_subring.
Canonical Subint_addrPred := AddrPred Subint_subring.
Canonical Subint_mulrPred := MulrPred Subint_subring.
Canonical Subint_zmodPred := ZmodPred Subint_subring.
Canonical Subint_semiringPred := SemiringPred Subint_subring.
Canonical Subint_smulrPred := SmulrPred Subint_subring.
Canonical Subint_subringPred := SubringPred Subint_subring.

Lemma Subreal_Subint : {subset Subint <= Subreal}.
Proof. by move=> _ /SubintP[m ->]; apply: realz. Qed.

Lemma Subint_normK x : x \in Subint -> `|x| ^+ 2 = x ^+ 2.
Proof. by move/Subreal_Subint/real_normK. Qed.

Lemma SubintEsign x : x \in Subint -> x = (-1) ^+ (x < 0)%R * `|x|.
Proof. by move/Subreal_Subint/realEsign. Qed.

(* Natural integer subset. *)

Lemma truncSub_itv x : 0 <= x -> (truncSub x)%:R <= x < (truncSub x).+1%:R.
Proof.
move=> x_ge0; have /andP[lemx ltxm1] := floorSub_itv (ger0_real x_ge0).
rewrite /truncSub x_ge0 -addn1 !pmulrn PoszD gez0_abs ?lemx //.
by rewrite -ltz_addr1 -(ltr_int R) (ler_lt_trans x_ge0).
Qed.

Lemma truncSub_def x n : n%:R <= x < n.+1%:R -> truncSub x = n.
Proof.
move=> ivt_n_x; have /andP[lenx _] := ivt_n_x.
by rewrite /truncSub (ler_trans (ler0n _ n)) // (@floorSub_def _ n) // addrC -intS.
Qed.

Lemma natSubK n : truncSub n%:R = n.
Proof. by apply: truncSub_def; rewrite lerr ltr_nat /=. Qed.

Lemma SubnatP x : reflect (exists n, x = n%:R) (x \in Subnat).
Proof.
by apply: (iffP eqP) => [<- | [n ->]]; [exists (truncSub x) | rewrite natSubK].
Qed.

Lemma truncSubK : {in Subnat, cancel truncSub (GRing.natmul 1)}.
Proof. by move=> x /eqP. Qed.

Lemma truncSub_gt0 x : (0 < truncSub x)%N = (1 <= x).
Proof.
apply/idP/idP=> [m_gt0 | x_ge1].
  have /truncSub_itv/andP[lemx _]: 0 <= x.
    by move: m_gt0; rewrite /truncSub; case: ifP.
  by apply: ler_trans lemx; rewrite ler1n.
have /truncSub_itv/andP[_ ltxm1]:= ler_trans ler01 x_ge1.
by rewrite -ltnS -(ltr_nat R) (ler_lt_trans x_ge1).
Qed.

Lemma truncSub0Pn x : reflect (truncSub x = 0%N) (~~ (1 <= x)).
Proof. by rewrite -truncSub_gt0 -eqn0Ngt; apply: eqP. Qed.

Lemma truncSub0 : truncSub 0 = 0%N. Proof. exact: (natSubK 0). Qed.
Lemma truncSub1 : truncSub 1 = 1%N. Proof. exact: (natSubK 1). Qed.

Lemma truncSubD :
  {in Subnat & Num.nneg, {morph truncSub : x y / x + y >-> (x + y)%N}}.
Proof.
move=> _ y /SubnatP[n ->] y_ge0; apply: truncSub_def.
by rewrite -addnS !natrD !natSubK ler_add2l ltr_add2l truncSub_itv.
Qed.

Lemma truncSubM : {in Subnat &, {morph truncSub : x y / x * y >-> (x * y)%N}}.
Proof. by move=> _ _ /SubnatP[n1 ->] /SubnatP[n2 ->]; rewrite -natrM !natSubK. Qed.

Lemma truncSubX n : {in Subnat, {morph truncSub : x / x ^+ n >-> (x ^ n)%N}}.
Proof. by move=> _ /SubnatP[n1 ->]; rewrite -natrX !natSubK. Qed.

Lemma rpred_Subnat S (ringS : semiringPred S) (kS : keyed_pred ringS) x :
  x \in Subnat -> x \in kS.
Proof. by case/SubnatP=> n ->; apply: rpred_nat. Qed.

Lemma Subnat_nat n : n%:R \in Subnat. Proof. by apply/SubnatP; exists n. Qed.
Lemma Subnat0 : 0 \in Subnat. Proof. exact: (Subnat_nat 0). Qed.
Lemma Subnat1 : 1 \in Subnat. Proof. exact: (Subnat_nat 1). Qed.
Hint Resolve Subnat_nat Subnat0 Subnat1.

Fact Subnat_key : pred_key Subnat. Proof. by []. Qed.
Fact Subnat_semiring : semiring_closed Subnat.
Proof.
by do 2![split] => //= _ _ /SubnatP[n ->] /SubnatP[m ->]; rewrite -(natrD, natrM).
Qed.
Canonical Subnat_keyed := KeyedPred Subnat_key.
Canonical Subnat_addrPred := AddrPred Subnat_semiring.
Canonical Subnat_mulrPred := MulrPred Subnat_semiring.
Canonical Subnat_semiringPred := SemiringPred Subnat_semiring.

Lemma Subnat_ge0 x : x \in Subnat -> 0 <= x.
Proof. by case/SubnatP=> n ->; apply: ler0n. Qed.

Lemma Subnat_gt0 x : x \in Subnat -> (0 < x) = (x != 0).
Proof. by case/SubnatP=> n ->; rewrite pnatr_eq0 ltr0n lt0n. Qed.

Lemma norm_Subnat x : x \in Subnat -> `|x| = x.
Proof. by move/Subnat_ge0/ger0_norm. Qed.

Lemma Subreal_Subnat : {subset Subnat <= Subreal}.
Proof. by move=> x /Subnat_ge0; apply: ger0_real. Qed.

Lemma Subnat_sum_eq1 (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> F i \in Subnat) -> \sum_(i | P i) F i = 1 ->
   {i : I | [/\ P i, F i = 1 & forall j, j != i -> P j -> F j = 0]}.
Proof.
move=> natF sumF1; pose nF i := truncSub (F i).
have{natF} defF i: P i -> F i = (nF i)%:R by move/natF/eqP.
have{sumF1} /eqP sumF1: (\sum_(i | P i) nF i == 1)%N.
  by rewrite -(eqr_nat R) natr_sum -(eq_bigr _ defF) sumF1.
have [i Pi nZfi]: {i : I | P i & nF i != 0%N}.
  by apply/sig2W/exists_inP; rewrite -negb_forall_in -sum_nat_eq0 sumF1.
have F'ge0 := (leq0n _, etrans (eq_sym _ _) (sum_nat_eq0 (predD1 P i) nF)).
rewrite -lt0n in nZfi; have [_] := (leqif_add (leqif_eq nZfi) (F'ge0 _)).
rewrite /= big_andbC -bigD1 // sumF1 => /esym/andP/=[/eqP Fi1 /forall_inP Fi'0].
exists i; split=> // [|j neq_ji Pj]; first by rewrite defF // -Fi1.
by rewrite defF // (eqP (Fi'0 j _)) // neq_ji.
Qed.

Lemma Subnat_mul_eq1 x y :
  x \in Subnat -> y \in Subnat -> (x * y == 1) = (x == 1) && (y == 1).
Proof. by do 2!move/truncSubK <-; rewrite -natrM !pnatr_eq1 muln_eq1. Qed.

Lemma Subnat_prod_eq1 (I : finType) (P : pred I) (F : I -> R) :
    (forall i, P i -> F i \in Subnat) -> \prod_(i | P i) F i = 1 ->
  forall i, P i -> F i = 1.
Proof.
move=> natF prodF1; apply/eqfun_inP; rewrite -big_andE.
move: prodF1; elim/(big_load (fun x => x \in Subnat)): _.
elim/big_rec2: _ => // i all1x x /natF N_Fi [Nx x1all1].
by split=> [|/eqP]; rewrite ?rpredM ?Subnat_mul_eq1 // => /andP[-> /eqP].
Qed.

(* Relating Subint and Subnat. *)

Lemma Subint_Subnat : {subset Subnat <= Subint}.
Proof. by move=> _ /SubnatP[n ->]; rewrite pmulrn Subint_int. Qed.

Lemma SubintE x : (x \in Subint) = (x \in Subnat) || (- x \in Subnat).
Proof.
apply/idP/idP=> [/SubintP[[n | n] ->] | ]; first by rewrite Subnat_nat.
  by rewrite NegzE opprK Subnat_nat orbT.
by case/pred2P=> [<- | /(canLR (@opprK _)) <-]; rewrite ?rpredN rpred_nat.
Qed.

Lemma Subnat_norm_Subint x : x \in Subint -> `|x| \in Subnat.
Proof.
case/SubintP=> [m ->]; rewrite [m]intEsign rmorphM rmorph_sign.
by rewrite normrM normr_sign mul1r normr_nat rpred_nat.
Qed.

Lemma SubnatEint x : (x \in Subnat) = (x \in Subint) && (0 <= x).
Proof.
apply/idP/andP=> [Nx | [Zx x_ge0]]; first by rewrite Subint_Subnat ?Subnat_ge0.
by rewrite -(ger0_norm x_ge0) Subnat_norm_Subint.
Qed.

Lemma SubintEge0 x : 0 <= x -> (x \in Subint) = (x \in Subnat).
Proof. by rewrite SubnatEint andbC => ->. Qed.

Lemma Subnat_exp_even x n : ~~ odd n -> x \in Subint -> x ^+ n \in Subnat.
Proof.
rewrite -dvdn2 => /dvdnP[m ->] Zx; rewrite mulnC exprM -Subint_normK ?rpredX //.
exact: Subnat_norm_Subint.
Qed.

Lemma norm_Subint_ge1 x : x \in Subint -> x != 0 -> 1 <= `|x|.
Proof.
rewrite -normr_eq0 => /Subnat_norm_Subint/SubnatP[n ->].
by rewrite pnatr_eq0 ler1n lt0n.
Qed.

Lemma sqr_Subint_ge1 x : x \in Subint -> x != 0 -> 1 <= x ^+ 2.
Proof.
by move=> Zx nz_x; rewrite -Subint_normK // expr_ge1 ?normr_ge0 ?norm_Subint_ge1.
Qed.

Lemma Subint_ler_sqr x : x \in Subint -> x <= x ^+ 2.
Proof.
move=> Zx; have [-> | nz_x] := eqVneq x 0; first by rewrite expr0n.
apply: ler_trans (_ : `|x| <= _); first by rewrite real_ler_norm ?Subreal_Subint.
by rewrite -Subint_normK // ler_eexpr // norm_Subint_ge1.
Qed.

(* divisibility 
Definition int_divisor m := m%:~R : R.
Definition nat_divisor n := n%:R : R.
Coercion nat_divisor : nat >-> R.
Coercion int_divisor : int >-> R.

Lemma nCdivE (p : nat) : p = p%:R :> divisor. Proof. by []. Qed.
Lemma zCdivE (p : int) : p = p%:~R :> divisor. Proof. by []. Qed.
Definition CdivE := (nCdivE, zCdivE).

Definition dvdC (x : divisor) : pred_class :=
   fun y : algC => if x == 0 then y == 0 else y / x \in Cint.
Notation "x %| y" := (y \in dvdC x) : C_expanded_scope.
Notation "x %| y" := (@in_mem divisor y (mem (dvdC x))) : C_scope.

Definition eqCmod (e x y : divisor) := (e %| x - y)%C.

Notation "x == y %[mod e ]" := (eqCmod e x y) : C_scope.
Notation "x != y %[mod e ]" := (~~ (x == y %[mod e])%C) : C_scope.*)


End SubArchiDomain.

Section SubArchiClosedField.

Variable R : numArchiClosedFieldType.

Lemma conj_Subint x : x \in (@Subint R) -> x^* = x.
Proof. by move/Subreal_Subint/conj_Creal. Qed. 

Lemma conj_Subnat x : x \in (@Subnat R) -> x^* = x.
Proof. by case/SubnatP=> n ->; apply: rmorph_nat. Qed.

End SubArchiClosedField. 












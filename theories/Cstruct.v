(* --------------------------------------------------------------------
 * (c) Copyright 2014--2015 INRIA.
 *
 * You may distribute this file under the terms of the CeCILL-B license
 * -------------------------------------------------------------------- *)

Require Import Reals Rtrigo1.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq choice.
From mathcomp Require Import fintype ssrint ssrnum ssrcomplex ssralg.
From mathcomp Require Import poly ssrnat div intdiv mxpoly rat bigop.
Require Import Rstruct.

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.

Definition complexR := R[i].

Canonical complexR_eqType := [eqType of complexR].
Canonical complexR_choiceType := [choiceType of complexR].
Canonical complexR_zmodType := [zmodType of complexR].
Canonical complexR_ringType := [ringType of complexR].
Canonical complexR_comRingType := [comRingType of complexR].
Canonical complexR_unitRingType := [unitRingType of complexR].
Canonical complexR_comUnitRingType := [comUnitRingType of complexR].
Canonical complexR_idomainType := [idomainType of complexR].
Canonical complexR_fieldType := [fieldType of complexR].
Canonical complexR_decFieldType := [decFieldType of complexR].
Canonical complexR_closedFieldType := [closedFieldType of complexR].
Canonical complexR_numDomainType := [numDomainType of complexR].
Canonical complexR_numFieldType := [numFieldType of complexR].
Canonical complexR_numClosedFieldType := [numClosedFieldType of complexR].

Lemma addcalc : forall a b c d : R, (a +i* b) + (c +i* d) =
  (a + c) +i* (b + d).
Proof. by done. Qed.

Lemma mulcalc : forall a b c d : R, (a +i* b) * (c +i* d) =
  ((a * c) - (b * d)) +i* ((a * d) + (b * c)).
Proof. by done. Qed. 

Notation "x %:~C" := (real_complex _ (@intmul _ (GRing.one _) x))
  (at level 2, left associativity, format "x %:~C") : ring_scope.

Lemma Rapprox (x : R) :
    exists y : int, (y-1)%:~R <= x < y%:~R .
Proof.
wlog: x / x > 0 => [Ih | /ltrW xpos].
  move: (num_real x); rewrite realE => /orP [].
    rewrite le0r => /orP [/eqP H | H]; last by apply: Ih.
    exists 1; rewrite H; apply/andP; split.
      by rewrite subrr le0r eq_refl orTb.
    by apply: ltr01.
  rewrite -oppr_ge0 le0r; move=> /orP [| Hx].
    rewrite oppr_eq0 => /eqP Hx.
    exists 1; rewrite subrr Hx; apply/andP; split.
      by rewrite le0r eq_refl orTb.
    by apply: ltr01.
  move: (Ih (-x) Hx) => [z /andP []].
  rewrite ler_oppr ltr_oppl ler_eqVlt => /orP [/eqP xz1 | mzltx] Hsup.
    exists (-z + 1 + 1); rewrite addrK xz1 -mulrNz opprD opprK lerr.
    by rewrite [(_ + _ + _)%:~R]intrD -[X in X < _]addr0 ltr_add2l ltr01.
  exists (- z +1 ); rewrite addrK ltrW ?(ltr_le_trans mzltx) // ?mulrNz //.
  by rewrite -mulrNz opprD opprK.
have Hpr : exists n:nat, x < n%:R.
  by suff xpos2 : 0 <= x by exists (Num.bound x); apply: archi_boundP.
exists (ex_minn Hpr); apply/andP; split; last by case /ex_minnP : Hpr.
case /ex_minnP : Hpr => m Hm IH.
rewrite lerNgt; apply/negP; rewrite subzn; last first.
  rewrite -(@ltr0n R_numDomainType).
  by apply: (@ler_lt_trans _ x 0 m%:R xpos Hm).
move/IH; rewrite -subn_eq0 subKn; first by apply/negP.
by move: (@ler_lt_trans _ x 0 m%:R xpos Hm); rewrite (ltr0n ).
Qed.

(****** Defs ******)

Notation Creal := (@Num.Def.Rreal complexR_numDomainType).

Definition floorC (x : complexR) :=
  xchoose (Rapprox (Re x)) -1.

Definition Cint : pred_class := 
  fun x : complexR => (floorC x)%:~R == x.

Definition truncC (x : complexR) := 
  if x >= 0 then absz (floorC x) else 0%N.

Definition Cnat : pred_class := 
  fun x : complexR => (truncC x)%:R == x.

Definition eqC_nat n p : (n%:R == p%:R :> complexR) = (n == p) := eqr_nat _ n p.
Definition leC_nat n p : (n%:R <= p%:R :> complexR) = (n <= p)%N := ler_nat _ n p.
Definition ltC_nat n p : (n%:R < p%:R :> complexR) = (n < p)%N := ltr_nat _ n p.
Definition Cchar : [char complexR] =i pred0 := @char_num _.

(****** Prop int ******)

Lemma ReK m :
  Re (m%:C)  = m%:~R.
Proof. by rewrite -complexr0 /= intz. Qed.

Lemma ImK (m : int) :
  Im (m%:C) = 0.
Proof. by rewrite -complexr0 /=. Qed.

Lemma Re_int m :
  (Re m%:~C)  = (m%:~R :R).
Proof. by done. Qed.

Lemma Im_int (m : int) :
  (Im m%:~C)  = (0 : R).
Proof. by done. Qed.

Lemma Re_intbis m :
  (Re (m%:~R : complexR)) = (m%:~R : R).
Proof. by rewrite raddfMz /=. Qed.

Lemma Im_intbis (m : int) :
  (Im (m%:~R : complexR)) = (0 :R).
Proof. by rewrite raddfMz /= mul0rz. Qed.

Lemma intrc (m : int) :
   (m%:~C)  = (m%:~R : complexR).
Proof. 
apply/eqP; rewrite eq_complex; apply/andP; split; apply/eqP.
  by rewrite Re_int Re_intbis.
by rewrite Im_int Im_intbis.
Qed.

Lemma intc_eq0 (m : int) :
   ((m%:~C) == (0 : complexR)) = (m == 0).
Proof. by rewrite eq_complex Re_int Im_int /= eq_refl andbT intr_eq0. Qed.

Lemma natrc (n : nat) :
   ((n%:R)%:~R)  = (n%:R : complexR).
Proof. by rewrite mulrz_nat. Qed.

Lemma natzc (n : nat) :
   (n%:~R)  = (n%:R : complexR).
Proof. by rewrite pmulrn. Qed.

(****** Creal ******)

Lemma Creal_Imd (x : complexR) :
  x \is Creal -> Im x = 0.
Proof.
by rewrite realE; move => /orP []; rewrite lecE; 
  move=> /andP [/eqP /= H1 H2].
Qed.

Lemma Creal_Imi (x : complexR) :
  Im x = 0 -> x \is Creal.
Proof.
move=> /eqP Hx; rewrite realE; apply/orP; rewrite lecE Hx lecE /=.
by move: Hx; rewrite eq_sym => -> /=; apply/orP; rewrite -realE; apply: num_real.
Qed.

Lemma Creal_ImP (z : complexR) : 
  reflect (Im z = 0) (z \is Creal).
Proof.
case H : (z \is Creal).
  by apply ReflectT; apply Creal_Imd.  
by apply ReflectF; move/Creal_Imi; apply/negP; apply negbT.
Qed.

Lemma Creal_int (m : int) :
  m%:~C \is Creal.
Proof.
by apply/Creal_ImP; apply: Im_int.
Qed.

Lemma CrealP (z : complexR) : 
  reflect (exists x : R, x%:C = z ) (z \is Creal).
Proof.
case H : (z \is Creal).
  apply: ReflectT; exists (Re z); apply /eqP; rewrite eq_complex eq_refl /=.
  by rewrite eq_sym; apply /eqP; apply /Creal_ImP.
apply: ReflectF; move => [x /eqP]; rewrite eq_complex /=.
move=> /andP [Hre]; rewrite eq_sym.
by move/eqP/Creal_ImP; apply/negP/negbT.
Qed.

Lemma Creal_lt (x y : complexR) :
  x \is Creal -> y \is Creal -> (x < y) = (Re x < Re y).
Proof.
by move=> /Creal_ImP Hx /Creal_ImP /eqP Hy; rewrite ltcE Hx Hy /=.
Qed.

Lemma Creal_le (x y : complexR) :
  x \is Creal -> y \is Creal -> (x <= y) = (Re x <= Re y).
Proof.
by move=> /Creal_ImP Hx /Creal_ImP /eqP Hy; rewrite lecE Hx Hy /=.
Qed.

(****** Cint ******)

Lemma floorC_itv (x : complexR) : 
  x \is Creal -> ((floorC x)%:~C) <= x < ((floorC x + 1)%:~C).
Proof.
move=> /Creal_ImP Hx.
rewrite /floorC -addrA [-1 + 1]addrC addrN addr0 lecE ltcE.
move: (Creal_int (xchoose (Rapprox (Re x)) - 1)) => /Creal_ImP ->.
move: (Creal_int (xchoose (Rapprox (Re x)))) => /Creal_ImP ->.
by rewrite Hx /= eq_refl /=; apply (xchooseP (Rapprox (Re x))). 
Qed.

Lemma floorC_def (x : complexR) (m : int) :
  m%:~C <= x < (m + 1)%:~C -> floorC x = m.
Proof.
rewrite lecE ltcE /floorC /=.
move=> /andP [/andP [_ HinfRe] /andP [_ HsupRe]].
move: (xchooseP (Rapprox (Re x))) => /andP [] H1.
have :(xchoose (Rapprox (Re x)))%:~R = (xchoose (Rapprox (Re x)) -1+1)%:~R
    => [| H H2].
   by rewrite -addrA subrr addr0.
apply/eqP/negbFE/negbTE/negP; rewrite neqr_lt; move/orP.
rewrite -!lez_addr1 -!(ler_int R_numDomainType) -H; move=> [bii|bii].
  by move: (ler_trans bii HinfRe); apply/negP/negbT; apply ltr_geF.
by move: (ler_trans bii H1); apply/negP/negbT; apply ltr_geF.
Qed.

Lemma floorC0 : floorC 0 = 0.
Proof.
apply floorC_def; apply/andP; split; by [done|rewrite add0r ltr01].
Qed.

Lemma floorC1 : floorC 1 = 1.
Proof.
apply floorC_def; apply/andP; split; first by done.
by rewrite -[X in X < _]add0r raddfD ltr_add2r ltr01.
Qed.

Hint Resolve floorC0 floorC1.

Lemma intCK : cancel intr floorC.
Proof.
move=> x; apply: floorC_def; apply/andP; split; first by rewrite intrc.
by rewrite intrc raddfD -[X in X < _]addr0 ltr_add2l ltr01.
Qed.

Lemma floorCK : {in Cint, cancel floorC intr}.
Proof.
by move=> x; rewrite unfold_in; move=> /eqP xint.
Qed.

Lemma Cint0 : 0 \in Cint.
Proof. by rewrite unfold_in floorC0. Qed.

Lemma Cint1 : 1 \in Cint.
Proof. by rewrite unfold_in floorC1. Qed.

Hint Resolve Cint0 Cint1.

Lemma Cint_int m : m%:~R \in Cint.
Proof. by rewrite unfold_in intCK. Qed.

Lemma CintP x : reflect (exists m, x = m%:~R) (x \in Cint).
Proof.
case H : (x \in Cint).
  by apply ReflectT; exists (floorC x); rewrite floorCK.
by apply ReflectF; move=> [m Hm]; move: H; rewrite Hm Cint_int.
Qed.

Lemma Creal_Cint : {subset Cint <= Creal}.
Proof.
by move=> x /CintP [m Hm]; rewrite Hm -intrc; apply: Creal_int.
Qed.

Lemma conj_Cint x : x \in Cint -> x^* = x.
Proof.
by move/Creal_Cint => /CrealP [y <-]; apply: conjc_real.
Qed.

Lemma Cint_normK x : x \in Cint -> `|x| ^+ 2 = x ^+ 2.
Proof.
by move/Creal_Cint => /CrealP [y <-]; rewrite sqr_normc conjc_real expr2.
Qed.

Lemma floorCD : {in Cint & Creal, {morph floorC : x y / x + y}}.
Proof.
move=> M X /CintP [m ->] /CrealP [x <-]; apply: floorC_def.
rewrite raddfD raddfD !intCK /= intrc ler_add2l.
rewrite [(m + floorC x%:C + 1)%:~R]raddfD /=.
rewrite [(m + floorC x%:C)%:~R]raddfD /=.
rewrite [(m%:~R + (floorC x%:C)%:~R + 1%:~R)%:C]raddfD /=.
rewrite [ (m%:~R + (floorC x%:C)%:~R)%:C]raddfD /=.
rewrite -intrc -addrA ltr_add2l -raddfD -raddfD /=.
by apply: floorC_itv; apply/CrealP; exists x.
Qed.

Lemma floorCN : {in Cint, {morph floorC : x / - x}}.
Proof.
move=> M /CintP [m ->]; apply/eqP; rewrite -[X in _ == X ]sub0r.
rewrite eq_sym subr_eq -floorCD.
    by rewrite addrC -raddfB /= subrr floorC0.
  by apply/CintP; exists (-m); rewrite raddfN.
by rewrite -intrc Creal_int.
Qed.

Lemma floorCM : {in Cint &, {morph floorC : x y / x * y}}.
Proof.
move=>  X Y /CintP [x ->] /CintP [y ->]; apply: floorC_def.
rewrite intrM rmorphM /= !intCK !intrc lerr /= raddfD /= intrM.
by rewrite -[X in X < _]addr0 ltr_add2l ltr01.
Qed.

Lemma floorCX n : {in Cint, {morph floorC : x / x ^+ n}}.
Proof.
elim: n => [M /CintP [m Hm]| n Ihn M HM].
  by rewrite !expr0 floorC1.
rewrite !exprS floorCM ?Ihn //=.
move: HM => /CintP [m ->].
by rewrite exprnP exprz_pintl //; apply: Cint_int.
Qed.

Lemma rpred_Cint S (ringS : subringPred S) (kS : keyed_pred ringS) x :
  x \in Cint -> x \in kS.
Proof. by case/CintP=> m ->; apply: rpred_int. Qed.

Lemma floorCpK (p : {poly complexR}) :
  p \is a polyOver Cint -> map_poly intr (map_poly floorC p) = p.
Proof.
move/(all_nthP 0)=> Zp; apply/polyP=> i.
rewrite coef_map coef_map_id0 //= -[p]coefK coef_poly.
by case: ifP => [/Zp/floorCK // | _]; rewrite floorC0.
Qed.

Lemma floorCpP (p : {poly complexR}) :
  p \is a polyOver Cint -> {q | p = map_poly intr q}.
Proof. by exists (map_poly floorC p); rewrite floorCpK. Qed.

Fact Cint_key : pred_key Cint.
Proof. by []. Qed.

Fact Cint_subring : subring_closed Cint.
Proof. by split=> // _ _ /CintP[m ->] /CintP[p ->];
    rewrite -(rmorphB, rmorphM) Cint_int. Qed.

Canonical Cint_keyed := KeyedPred Cint_key.
Canonical Cint_opprPred := OpprPred Cint_subring.
Canonical Cint_addrPred := AddrPred Cint_subring.
Canonical Cint_mulrPred := MulrPred Cint_subring.
Canonical Cint_zmodPred := ZmodPred Cint_subring.
Canonical Cint_semiringPred := SemiringPred Cint_subring.
Canonical Cint_smulrPred := SmulrPred Cint_subring.
Canonical Cint_subringPred := SubringPred Cint_subring.

(****** Cnat ******)

Lemma truncC_itv x : 0 <= x -> (truncC x)%:R <= x < (truncC x).+1%:R.
Proof.
move=> x_ge0; have /andP[lemx ltxm1] := floorC_itv (ger0_real x_ge0).
rewrite /truncC x_ge0 -addn1 !pmulrn PoszD gez0_abs ?lemx.
  rewrite -!intrc floorC_itv // realE; apply/orP; by left.
rewrite -ltz_addr1 -(ltr_int [numFieldType of complexR]) (ler_lt_trans x_ge0) //.
by rewrite -intrc.
Qed.

Lemma truncC_def x n : n%:R <= x < n.+1%:R -> truncC x = n.
Proof.
move=> ivt_n_x; have /andP[lenx _] := ivt_n_x.
rewrite /truncC (ler_trans (ler0n _ n)) // (@floorC_def _ n) // addrC -intS.
by rewrite !intrc.
Qed.

Lemma natCK n : truncC n%:R = n.
Proof. by apply: truncC_def; rewrite lerr ltr_nat /=. Qed.

Lemma CnatP x : reflect (exists n, x = n%:R) (x \in Cnat).
Proof.
by apply: (iffP eqP) => [<- | [n ->]]; [exists (truncC x) | rewrite natCK].
Qed.

Lemma truncCK : {in Cnat, cancel truncC (GRing.natmul 1)}.
Proof. by move=> x /eqP. Qed.

Lemma truncC_gt0 x : (0 < truncC x)%N = (1 <= x).
Proof.
apply/idP/idP=> [m_gt0 | x_ge1].
  have /truncC_itv/andP[lemx _]: 0 <= x.
    by move: m_gt0; rewrite /truncC; case: ifP.
  by apply: ler_trans lemx; rewrite ler1n.
have /truncC_itv/andP[_ ltxm1]:= ler_trans ler01 x_ge1.
by rewrite -ltnS -ltC_nat (ler_lt_trans x_ge1).
Qed.

Lemma truncC0Pn x : reflect (truncC x = 0%N) (~~ (1 <= x)).
Proof. by rewrite -truncC_gt0 -eqn0Ngt; apply: eqP. Qed.

Lemma truncC0 : truncC 0 = 0%N. 
Proof. exact: (natCK 0). Qed.

Lemma truncC1 : truncC 1 = 1%N. 
Proof. exact: (natCK 1). Qed.

Lemma truncCD :
  {in Cnat & Num.nneg, {morph truncC : x y / x + y >-> (x + y)%N}}.
Proof.
move=> _ y /CnatP[n ->] y_ge0; apply: truncC_def.
by rewrite -addnS !natrD !natCK ler_add2l ltr_add2l truncC_itv.
Qed.

Lemma truncCM : {in Cnat &, {morph truncC : x y / x * y >-> (x * y)%N}}.
Proof. by move=> _ _ /CnatP[n1 ->] /CnatP[n2 ->]; rewrite -natrM !natCK. Qed.

Lemma truncCX n : {in Cnat, {morph truncC : x / x ^+ n >-> (x ^ n)%N}}.
Proof. by move=> _ /CnatP[n1 ->]; rewrite -natrX !natCK. Qed.

Lemma rpred_Cnat S (ringS : semiringPred S) (kS : keyed_pred ringS) x :
  x \in Cnat -> x \in kS.
Proof. by case/CnatP=> n ->; apply: rpred_nat. Qed.

Lemma Cnat_nat n : n%:R \in Cnat. 
Proof. by apply/CnatP; exists n. Qed.

Lemma Cnat0 : 0 \in Cnat. 
Proof. exact: (Cnat_nat 0). Qed.

Lemma Cnat1 : 1 \in Cnat. 
Proof. exact: (Cnat_nat 1). Qed.

Hint Resolve Cnat_nat Cnat0 Cnat1.

Fact Cnat_key : pred_key Cnat. 
Proof. by []. Qed.

Fact Cnat_semiring : semiring_closed Cnat.
Proof.
by do 2![split] => //= _ _ /CnatP[n ->] /CnatP[m ->]; rewrite -(natrD, natrM).
Qed.

Canonical Cnat_keyed := KeyedPred Cnat_key.
Canonical Cnat_addrPred := AddrPred Cnat_semiring.
Canonical Cnat_mulrPred := MulrPred Cnat_semiring.
Canonical Cnat_semiringPred := SemiringPred Cnat_semiring.

Lemma Cnat_ge0 x : x \in Cnat -> 0 <= x.
Proof. by case/CnatP=> n ->; apply: ler0n. Qed.

Lemma Cnat_gt0 x : x \in Cnat -> (0 < x) = (x != 0).
Proof. by case/CnatP=> n ->; rewrite pnatr_eq0 ltr0n lt0n. Qed.

Lemma conj_Cnat x : x \in Cnat -> x^* = x.
Proof. by case/CnatP=> n ->; apply: rmorph_nat. Qed.

Lemma norm_Cnat x : x \in Cnat -> `|x| = x.
Proof. by move/Cnat_ge0/ger0_norm. Qed.

Lemma Creal_Cnat : {subset Cnat <= Creal}.
Proof.
by move=> x /Cnat_ge0 Hx; rewrite realE; apply/orP; left.
Qed.

Lemma Cnat_mul_eq1 x y :
  x \in Cnat -> y \in Cnat -> (x * y == 1) = (x == 1) && (y == 1).
Proof. by do 2!move/truncCK <-; rewrite -natrM !pnatr_eq1 muln_eq1. Qed.


(****** Cint / Cnat ******)

Lemma Cint_Cnat : {subset Cnat <= Cint}.
Proof. by move=> _ /CnatP[n ->]; rewrite pmulrn Cint_int. Qed.

Lemma CintE x : (x \in Cint) = (x \in Cnat) || (- x \in Cnat).
Proof.
apply/idP/idP=> [/CintP[[n | n] ->] | ]; first by rewrite Cnat_nat.
  by rewrite NegzE opprK Cnat_nat orbT.
by case/pred2P=> [<- | /(canLR (@opprK _)) <-]; rewrite ?rpredN rpred_nat.
Qed.

Lemma Cnat_norm_Cint x : x \in Cint -> `|x| \in Cnat.
Proof.
case/CintP=> [m ->]; rewrite [m]intEsign rmorphM rmorph_sign.
by rewrite normrM normr_sign mul1r normr_nat rpred_nat.
Qed.

Lemma CnatEint x : (x \in Cnat) = (x \in Cint) && (0 <= x).
Proof.
apply/idP/andP=> [Nx | [Zx x_ge0]]; first by rewrite Cint_Cnat ?Cnat_ge0.
by rewrite -(ger0_norm x_ge0) Cnat_norm_Cint.
Qed.

Lemma CintEge0 x : 0 <= x -> (x \in Cint) = (x \in Cnat).
Proof. by rewrite CnatEint andbC => ->. Qed.

Lemma norm_Cint_ge1 x : x \in Cint -> x != 0 -> 1 <= `|x|.
Proof.
rewrite -normr_eq0 => /Cnat_norm_Cint/CnatP[n ->].
by rewrite pnatr_eq0 ler1n lt0n.
Qed.

(****** Divisibilite ******)


Definition dvdC (x : int) : pred_class :=
   fun y : complexR => if x == 0 then y == 0 else y / (x%:~R) \in Cint.

Notation "( x %C| y )" := (y \in dvdC x) : ring_scope.

Definition eqCmod (e : int) (x y : complexR) := (e %C| x - y).

Lemma dvdCP x y : reflect (exists2 z, z \in Cint & y = z * x%:~R) (x %C| y).
Proof.
rewrite unfold_in; have [-> | nz_x] := altP eqP.
  by apply: (iffP eqP) => [-> | [z _ ->]]; first exists 0; rewrite ?mulr0.
have nzr_x : ( (x%:~R : complexR) != 0 ) by rewrite intr_eq0.
apply: (iffP idP) => [Zyx | [z Zz ->]].
  by exists (y / x%:~R); rewrite ?divfK.
by rewrite mulfK.
Qed.

Lemma dvdC0 x : (x %C| 0).
Proof. by apply/dvdCP; exists 0; rewrite ?mul0r. Qed.

Lemma dvdC_mull x y z : y \in Cint -> (x %C| z) -> (x %C| y * z).
Proof.
move=> Zy /dvdCP[m Zm ->]; apply/dvdCP.
by exists (y * m); rewrite ?mulrA ?rpredM.
Qed.

Lemma dvdC_mulr x y z : y \in Cint -> (x %C| z) -> (x %C| z * y).
Proof. by rewrite mulrC; apply: dvdC_mull. Qed.

Lemma dvdC_mul2r x y z : y != 0 -> (x * y %C| z * y%:~R) = (x %C| z).
Proof.
move=> nz_y; rewrite !unfold_in !(mulIr_eq0 _ (mulIf nz_y)).
rewrite mulrAC rmorphM /= invfM mulrA divfK; last by rewrite intr_eq0.
by rewrite mulIr_eq0 //; apply: mulIf; rewrite intr_eq0.
Qed.

Lemma dvdC_refl x : (x %C| x%:~R).
Proof. by apply/dvdCP; exists 1; rewrite ?mul1r. Qed.

Hint Resolve dvdC_refl.

Lemma dvdC_trans x y z : (x %C| y%:~R ) -> (y %C| z) -> (x %C| z).
Proof. by move=> x_dv_y /dvdCP[m Zm ->]; apply: dvdC_mull. Qed.

Fact dvdC_key x : pred_key (dvdC x).
Proof. by []. Qed.

Lemma dvdC_zmod x : zmod_closed (dvdC x).
Proof.
split=> [| _ _ /dvdCP[y Zy ->] /dvdCP[z Zz ->]]; first exact: dvdC0.
by rewrite -mulrBl dvdC_mull ?rpredB.
Qed.

Canonical dvdC_keyed x := KeyedPred (dvdC_key x).
Canonical dvdC_opprPred x := OpprPred (dvdC_zmod x).
Canonical dvdC_addrPred x := AddrPred (dvdC_zmod x).
Canonical dvdC_zmodPred x := ZmodPred (dvdC_zmod x).

Lemma dvdC_nat (p n : nat) : (p%Z %C| n%:R ) = (p %| n)%N.
Proof.
rewrite unfold_in CintEge0 ?divr_ge0 ?invr_ge0 ?ler0n // !pnatr_eq0 eqz_nat.
have [-> | nz_p] := altP eqP ; first by rewrite dvd0n.
apply/CnatP/dvdnP=> [[q def_q] | [q ->]]; exists q.
  by apply/eqP; rewrite -eqC_nat natrM -def_q divfK ?pnatr_eq0. 
by rewrite [num in num / _]natrM mulfK ?pnatr_eq0.
Qed.

Lemma dvdC_int (p : nat) x : x \in Cint -> (p%Z %C| x) = (p %| `|floorC x|)%N.
Proof.
move=> Zx; rewrite -{1}(floorCK Zx) {1}[floorC x]intEsign.
by rewrite rmorphMsign /= rpredMsign dvdC_nat.
Qed.

Lemma dvdC_Cint x y : (x %C| y) -> y \in Cint.
Proof.
move=> /dvdCP [z Hz ->]; apply (rpredM Hz); apply: Cint_int.
Qed.

Lemma dvdC_neq0 x y : ~ (x %C| y) -> y != 0.
Proof.
case: (boolP ( y == 0)).
move => /eqP Heq /=.
rewrite Heq => H.
by move: ( dvdC0 x) => Hf.
by move=> Heq H /=.
Qed.

(******  modulo ******)

Lemma eqCmod_refl e x : eqCmod e x x.
Proof. by rewrite /eqCmod subrr rpred0. Qed.

Lemma eqCmodm0 e : eqCmod e e%:~R 0. 
Proof. by rewrite /eqCmod subr0. Qed.
Hint Resolve eqCmod_refl eqCmodm0.

Lemma eqCmod0 e x : eqCmod e x 0 = (e %C| x).
Proof. by rewrite /eqCmod subr0. Qed.

Lemma eqCmod_sym e x y : eqCmod e x y = eqCmod e y x.
Proof. by rewrite /eqCmod -opprB rpredN. Qed.

Lemma eqCmod_trans e y x z :
  eqCmod e x y -> eqCmod e y z -> eqCmod e x z.
Proof. by move=> Exy Eyz; rewrite /eqCmod -[x](subrK y) -addrA rpredD. Qed.

Lemma eqCmod_transl e x y z :
  eqCmod e x y -> eqCmod e x z -> eqCmod e y z.
Proof.
by rewrite eqCmod_sym; move=> Hyx Hxz; apply: (eqCmod_trans Hyx Hxz).
Qed.

Lemma eqCmod_transr e x y z :
  eqCmod e x y -> eqCmod e z x -> eqCmod e z y.
Proof. by move=> Hxy Hzx; apply: (eqCmod_trans Hzx Hxy). Qed.

Lemma eqCmodN e x y : 
  eqCmod e (-x) y = eqCmod e x (-y).
Proof. by rewrite eqCmod_sym /eqCmod !opprK addrC. Qed.

Lemma eqCmodDr e x y z : 
  eqCmod e (y + x) (z + x) = eqCmod e y z.
Proof. by rewrite /eqCmod addrAC opprD !addrA subrK. Qed.

Lemma eqCmodDl e x y z : 
  eqCmod e (x + y) (x + z) = eqCmod e y z.
Proof. by rewrite !(addrC x) eqCmodDr. Qed.

Lemma eqCmodD e x1 x2 y1 y2 :
  eqCmod e x1 x2 -> eqCmod e y1 y2 -> eqCmod e (x1 + y1) (x2 + y2).
Proof. rewrite -(eqCmodDl e x2 y1) -(eqCmodDr e y1); exact: eqCmod_trans. Qed.

Lemma eqCmod_nat (e m n : nat) : 
  eqCmod e m%:R n%:R = (m == n %[mod e]).
Proof.
wlog lenm: m n / (n <= m)%N.
  by move=> IH; case/orP: (leq_total m n) => /IH //; rewrite eqCmod_sym eq_sym.
by rewrite /eqCmod -natrB // dvdC_nat eqn_mod_dvd.
Qed.

Lemma eqCmod0_nat (e m : nat) : 
  eqCmod e m%:R 0 = (e %| m)%N.
Proof. by rewrite eqCmod0 dvdC_nat. Qed.

Lemma eqCmodMr e :
  {in Cint, forall z x y, eqCmod e x y -> eqCmod e (x * z) (y * z)}.
Proof. by move=> z Zz x y; rewrite /eqCmod -mulrBl => /dvdC_mulr->. Qed.

Lemma eqCmodMl e :
  {in Cint, forall z x y, eqCmod e x y -> eqCmod e (z * x) (z * y)}.
Proof. by move=> z Zz x y Exy; rewrite !(mulrC z) eqCmodMr. Qed.

Lemma eqCmodMl0 e : {in Cint, forall x, eqCmod e (x * e%:~R) 0 }.
Proof. by move=> x Zx; rewrite -(mulr0 x) eqCmodMl. Qed.

Lemma eqCmodMr0 e : {in Cint, forall x, eqCmod e (e%:~R * x) 0 }.
Proof. by move=> x Zx; rewrite /= mulrC eqCmodMl0. Qed.

Lemma eqCmod_addl_mul e : 
{in Cint, forall x y, eqCmod e (x * e%:~R + y)  y }.
Proof. by move=> x Zx y; rewrite -{2}[y]add0r eqCmodDr eqCmodMl0. Qed.

Lemma eqCmodM e : {in Cint & Cint, forall x1 y2 x2 y1,
  eqCmod e x1 x2 -> eqCmod e y1 y2 -> eqCmod e (x1 * y1) (x2 * y2) }.
Proof.
move=> x1 y2 Zx1 Zy2 x2 y1 eq_x /(eqCmodMl Zx1)/eqCmod_trans-> //.
exact: eqCmodMr.
Qed.

(* divisibility for complex-integers *)
Lemma dvdCMn x y : x != 0%N -> (x %C| y *+ x) = (y \in Cint).
Proof.
  rewrite -mulr_natr => Hx.
  rewrite -{2}[x]mul1n PoszM -natzc dvdC_mul2r.
    by rewrite /dvdC /= unfold_in divr1.
  by rewrite eqz_nat.
Qed.

Lemma dvdCMnD n x y : 
  n != 0%N -> y \in Cint -> (n %C| x + (y *+ n)) = (n %C| x).
Proof.
  move=> Hn Hy.
  rewrite -!eqCmod0.
  rewrite -mulr_natr addrC.  
  move: (@eqCmod_addl_mul n y Hy x) => H.
  case Hx : (eqCmod n x 0).
    apply: (eqCmod_trans H Hx).
  apply: negPf; apply/negP => Hf.
  move/negP: Hx => Hx; apply: Hx.
  by apply: (eqCmod_transl H Hf).
Qed.
  

(* complex exponential *)

Definition Cexp (z : complexR) :=
  (exp(Re z))%:C * (cos (Im z) +i* sin (Im z)).

Lemma Cexp_exp x :
  x \in Creal -> Cexp(x) = (exp(Re x))%:C.
Proof.
move=> /Creal_ImP Him. 
by rewrite /Cexp Him // sin_0 cos_0 complexr0 mulr1.
Qed.

Lemma Cexp0 :
  Cexp(0) = 1.
Proof. by rewrite /Cexp /= sin_0 cos_0 complexr0 mulr1 expR0. Qed.

Lemma CexpRD x y :
  Cexp(x) * Cexp(y) = Cexp(GRing.add x y).
Proof.
rewrite /Cexp mulrA [X in X *_ = _]mulrC mulrA -rmorphM /= expRD addrC -mulrA.
by rewrite -raddfD /= mulcalc [(_*_) + (_*_)]addrC -sin_add -cos_add -raddfD.
Qed.

Lemma CexpRX x :
  forall n : nat,
    Cexp(x) ^+ n = Cexp(x *+ n).
Proof.
elim => [|n Ihn].
  by rewrite expr0 mulr0n Cexp0.
by rewrite exprS Ihn mulrS CexpRD.
Qed.

Lemma Euler :
  1 + Cexp (PI%:C * 'i) = 0.
Proof.
rewrite /Cexp ImiRe ReiNIm -complexr0 /= cos_PI sin_PI !complexr0.
rewrite oppr0 exp_0 mul1r; apply/eqP.
by rewrite eq_complex /= addr0 addrN eq_refl.
Qed.

Lemma ReM (x : complexR) y :
  Re (x * y%:C) = (Re x) * y.
Proof.
rewrite real_complexE; case: x => r i.
by rewrite mulcalc /= mulr0 subr0.
Qed.

Lemma ImM (x : complexR) y :
  Im (x * y%:C) = (Im x) * y.
Proof.
rewrite real_complexE; case: x => r i.
by rewrite mulcalc /= mulr0 add0r.
Qed.

Lemma ReX (y : R) n :
  Re (y%:C ^+ n) = y ^+ n.
Proof.
elim: n => [| n Ihn].
  by rewrite !expr0 /=.  
by rewrite !exprS mulrC ReM Ihn mulrC.
Qed.

Lemma ImX (y : R) n :
  Im (y%:C ^+ n) = 0.
Proof.
elim: n => [| n Ihn].
  by rewrite !expr0 /=.  
by rewrite !exprS mulrC ImM Ihn mul0r.
Qed.

(* move to mxpoly ? *)
Lemma poly_caract_root (F E: fieldType) (f:{rmorphism F -> E}) x : 
    algebraicOver f x -> x != 0 -> 
    exists P : {poly F}, [&&  P \is monic, root (map_poly f P) x & P`_0 != 0].
Proof.
move=> /integral_algebraic [P Pmonic Proot] xneq0.
wlog P_0: P Proot Pmonic / P`_0 != 0=> [hwlog|]; last by exists P; apply/and3P.
have Pneq0 : P != 0 by rewrite monic_neq0.
have [n [Q /implyP /(_ Pneq0) rootQN0 P_eq]] := multiplicity_XsubC P 0.
move: Pneq0 Proot Pmonic.
rewrite P_eq rmorphM rootM rmorphX rmorphB rmorph0 /= map_polyX => Pn0 Pr Pm.
have Qmonic : Q \is monic by move:Pm; rewrite monicMr ?monic_exp ?monicXsubC.
have Qn : Q`_0 != 0 by rewrite -horner_coef0.
have Qr : root (map_poly f Q) x.
 move: Pr; case: {P_eq Pn0 Pm} n => [|n] .
    by rewrite expr0 rootC oner_eq0 orbF.
  by rewrite rmorph0 root_exp_XsubC (negPf xneq0) orbF.
exact: (hwlog Q).
Qed.

Lemma ratr_eq0 (x : rat) : ((ratr x) == (0: complexR)) = (x == 0).
Proof.
by rewrite -numq_eq0 mulf_eq0 invr_eq0 !intr_eq0 (negbTE (denq_neq0 x)) orbF.
Qed.

Lemma poly_caract_int (x : complexR) : algebraicOver ratr x -> x != 0 ->
    exists P : {poly int}, (P != 0) && root (map_poly intr P) x &&
    (P`_0 != 0) && (0 < lead_coef P).
Proof.
move => algebraic_x xn0.
case: (poly_caract_root algebraic_x xn0) => [P /andP [mon /andP [r nc]]].
set P' :=
    \sum_(0 <= i < size P)
       (\prod_(0 <= j < size P | j != i) (denq P`_j) * numq P`_i) *: 'X^i
    : {poly int}.
exists P'.
have Pn0 : P != 0.
  by apply/negP=> /eqP p0; case/negP:nc; rewrite p0 coef0.
have sp_n0 : size P != 0%N.
  by rewrite size_poly_eq0.
have prn0 : forall pr : pred nat,
      \prod_(0 <= j < size P | pr j) denq P`_j != 0.
  move => pr; elim: {1 3} (size P) (leqnn (size P))=> [| n In] ns.
    by rewrite big_nil.
  rewrite big_mkcond big_nat_recr //; case: (pr n).
    by rewrite mulf_eq0 denq_eq0 orbF -big_mkcond In // ltnW.
  by rewrite /= mulr1 -big_mkcond In // ltnW.
have nc' : P'`_0 != 0.
  rewrite /P'; move: sp_n0; case hs:(size P)=>[| k] // _. 
  rewrite big_nat_recl; last by [].
  rewrite expr0 alg_polyC addrC.
  have eqb :forall i, (0 <= i < k)%N -> 
       (\prod_(0<= j < k.+1 |j != i.+1) denq P`_j * numq P`_i.+1) *: 'X^i.+1 =
       (\prod_(0<= j < k.+1 |j != i.+1) denq P`_j * numq P`_i.+1) *: 'X^i * 'X.
    by move => i _; rewrite exprS -scalerAl (mulrC 'X).
  rewrite (eq_big_nat _ _ eqb) -big_distrl -cons_poly_def coef_cons eqxx {eqb}.
  by rewrite mulf_eq0 negb_or numq_eq0 nc andbT -hs; apply: prn0.
have -> : P' != 0.
  by apply/negP=> /eqP p0; case/negP: nc'; rewrite p0 coef0.
rewrite nc' andbT andTb /P' big_mkord.
rewrite -(poly_def _
          (fun i => (\prod_(0 <= j < size P | j != i) denq P`_j * numq P`_i))).
rewrite /root horner_poly.
rewrite size_poly_eq; last first.
  rewrite mulf_eq0 numq_eq0 -lead_coefE lead_coef_eq0 negb_or Pn0 andbT.
  by apply: prn0.
move: r; rewrite /root horner_poly => /eqP r /=.
rewrite [X in X == 0]
               (_ : _ = (\prod_(0 <= j < size P) denq P`_j)%:~R *
                     \sum_(i < size P) ratr P`_i * x ^+ i).
  rewrite r mulr0 eqxx andTb.
  rewrite lead_coef_poly; first last.
    rewrite mulf_eq0 negb_or prn0 numq_eq0 -lead_coefE.
    by move/monicP: mon=> ->.
  by rewrite lt0n.
  rewrite -lead_coefE; move/monicP: (mon) => ->; have -> :numq 1 = 1%N by [].
  rewrite mulr1.
  apply: (big_rec (fun x => 0 < x)) => // i w ci cw.
  by rewrite mulr_gt0 // denq_gt0.
rewrite big_distrr; apply: eq_bigr => i _ /=.
rewrite coef_poly /=; case: i => i ic /=; rewrite ic !mulrA; congr (_ * _).
have := (denq_neq0 P`_i); rewrite -(intr_eq0 complexR_numDomainType) => di.
apply: (mulIf di); rewrite mulfVK // mulrC -!rmorphM /= mulrA.
congr ((_ * _)%:~R); rewrite !big_mkord.
by apply/esym; apply:(@bigD1 _ _ _ _ (Ordinal ic) (fun _ => true)).
Qed.

(* divisibility for polynomials values *)
Lemma divz_coef :
   forall P : {poly complexR}, P \is a polyOver Cint ->
   forall k : nat, (forall i : nat, (i < size P)%N -> (k %C| P`_i)) ->
      forall x : complexR, x \in Cint -> (k %C| P.[x]).
Proof.
move=> P HP k0 Hdiv x Hx; rewrite horner_coef.
apply big_rec; first by rewrite dvdC0.
move=> i y bla /dvdCP [zy zyint Hzy].
rewrite -eqCmod0 Hzy addrC (@eqCmod_trans _ (P`_i * x ^+ i)) //;
  first by rewrite eqCmod_addl_mul //.
rewrite -{2}[0](mul0r (x ^+ i) ) eqCmodMr //; first by rewrite rpredX //.
by rewrite eqCmod0; apply: Hdiv.
Qed.

(* degree of derivatives for complex polynomials. *)
Lemma size_deriv_Pneq0 (P : {poly complexR}) :
   P != 0 -> (size (P^`())).+1 = (size P).
Proof.
rewrite -size_poly_gt0 => P_neq0.
case H : (size P).-1 => [|np].
  have Hs : size P = 1%N.
    move: H; rewrite NPeano.Nat.eq_pred_0.
    by move=> [/eqP | //]; move: P_neq0; rewrite lt0n => /negbTE ->.
  rewrite Hs -addn1 -[X in _ = X]addn1; apply/eqP.
  rewrite eqn_add2r -leqn0 -(leq_add2r 1) addn1 addn1 -Hs.
  by apply: lt_size_deriv; rewrite -size_poly_gt0.
rewrite /deriv size_poly_eq.
  by rewrite (prednK P_neq0).
rewrite H [X in P`_X]/= [X in _*+X]/= -{1}H.
rewrite -lead_coefE mulrn_eq0 lead_coef_eq0 /=.
by rewrite -size_poly_gt0.
Qed.

(* TODO: This one already exists in polyorder, but it requires
   a structure that is to strong : realDomainType *)
Lemma size_deriv (P : {poly complexR}) : size (P^`()) = (size P).-1.
Proof.
case: (boolP (P == 0)) => [/eqP -> | P_neq0].
  by rewrite deriv0 size_poly0 /=.
by rewrite -(size_deriv_Pneq0 P_neq0) /=.
Qed.

(* This one already exists in cauchyreals, with name size_derivn
   but it requires a structure that is to strong: realDomainType. *)
Lemma Cr_size_derivn (P : {poly complexR}) j :
    (size (P^`(j)) = (size P) - j)%N.
Proof.
elim: j => [ | j ihj]; first by rewrite subn0 derivn0.
by rewrite derivnS subnS -ihj size_deriv.
Qed.


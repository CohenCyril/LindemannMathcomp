(* --------------------------------------------------------------------
 * (c) Copyright 2014--2015 INRIA.
 *
 * You may distribute this file under the terms of the CeCILL-B license
 * -------------------------------------------------------------------- *)

Require Import Reals Rtrigo1.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq choice.
From mathcomp Require Import fintype ssrint ssrnum complex ssralg.
From mathcomp Require Import poly ssrnat div intdiv mxpoly rat bigop.
Require Import Rstruct Archistruct.

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.

(* Definition des complexes sur les réels de Coq *)

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
Canonical complexR_numArchiDomainType := [numArchiDomainType of complexR].
Canonical complexR_numArchiFieldType := [numArchiFieldType of complexR].
Canonical complexR_numArchiClosedFieldType := [numArchiClosedFieldType of complexR].

(* Récupération des notations *)

Notation Creal := (@Num.Def.Rreal complexR_numDomainType).
Notation Cint := (@Subint complexR).
Notation Cnat := (@Subnat complexR).

(* Injections *)

Notation QtoC := (ratr : rat -> complexR).


Notation ZtoC := (intr : int -> complexR).

Definition ZtoCE :=
  let CnF := complexR_numFieldType in
  let ZtoCm := intmul1_rmorphism CnF in
  ((rmorph0 ZtoCm, rmorph1 ZtoCm, rmorphMn ZtoCm, rmorphN ZtoCm, rmorphD ZtoCm),
   (rmorphM ZtoCm, rmorphX ZtoCm),
   (rmorphMz ZtoCm, @intr_norm CnF, @intr_sg CnF),
   =^~ (@ler_int CnF, @ltr_int CnF, (inj_eq (@intr_inj CnF)))).

(* retour à R depuis les complexes *)
Notation Re_R := complex.Re.
Notation Im_R := complex.Im.
Notation norm_R := ComplexField.normc.

Notation RtoC := (real_complex R).

Ltac RtoC_simpl := 
  rewrite -?complexRe -?complexIm -?[`| _ |]/(((norm_R _)%:C)%C) -?[((_)%:C)%C]/(RtoC _) /=.

Lemma RtoC_inj : injective RtoC.
Proof. by move => x y /eqP; rewrite /RtoC eq_complex /= eq_refl andbT => /eqP. Qed.

Lemma RtoC_norm x : RtoC `|x| = `|RtoC x|.
Proof.
rewrite normc_def; RtoC_simpl; apply/eqP; rewrite (inj_eq RtoC_inj); apply/eqP.
by rewrite expr0n /= addr0 sqrtr_sqr.
Qed.

Lemma ler_RtoC x y : (RtoC x <= RtoC y) = (x <= y).
Proof. by rewrite -lecR; RtoC_simpl. Qed.

Lemma ltr_RtoC x y : (RtoC x < RtoC y) = (x < y).
Proof. by rewrite -ltcR; RtoC_simpl. Qed.

Definition RtoCE :=
  let CnF := R_rcfType in
  let RtoCm := ComplexField.real_complex_rmorphism CnF in
  ((rmorph0 RtoCm, rmorph1 RtoCm, rmorphMn RtoCm, rmorphN RtoCm, rmorphD RtoCm),
   (rmorphM RtoCm, rmorphX RtoCm),
   (rmorphMz RtoCm, RtoC_norm),
   =^~ (ler_RtoC, ltr_RtoC, (inj_eq RtoC_inj))).

(* tactiques *)
Definition C_simpl :=
  (addr0, add0r, subr0, mulr0, mul0r, mulr1, mul1r, mulr0n, mulrS, expr0, exprS).

(* complex exponential *)

Definition Cexp (z : complexR) :=
  RtoC (exp(Re_R z)) * (RtoC (cos (Im_R z)) + 'i * RtoC (sin (Im_R z))).

Lemma Cexp_exp x :
  x \in Creal -> Cexp(x) = RtoC (exp(Re_R x)).
Proof.
move=> /Creal_ImP; RtoC_simpl; rewrite /Cexp => /eqP.
rewrite /eqP fmorph_eq0 => /eqP ->; rewrite sin_0 cos_0 /=.
by rewrite !RtoCE !C_simpl.
Qed.

Lemma Cexp0 :
  Cexp(0) = 1.
Proof. by rewrite /Cexp /= sin_0 cos_0 !RtoCE !C_simpl expR0. Qed.

Lemma CexpRD x y :
  Cexp(x) * Cexp(y) = Cexp(GRing.add x y).
Proof.
rewrite /Cexp mulrA [X in X *_ = _]mulrC mulrA -rmorphM /= expRD addrC -mulrA.
rewrite -raddfD /= mulC_rect -!rmorphM -rmorphD -rmorphB /= -cos_add.
by rewrite [X in RtoC( X + _)]mulrC -sin_add -!raddfD [y + x]addrC /=.
Qed.

Lemma Cexp_morph : {morph Cexp : x y / x + y >-> x * y}.
Proof. by move=> x y; rewrite CexpRD. Qed.


Lemma CexpRX x :
  forall n : nat,
    Cexp(x) ^+ n = Cexp(x *+ n).
Proof.
elim => [|n Ihn]; rewrite !C_simpl; first by rewrite Cexp0.
by rewrite Ihn Cexp_morph.
Qed.

(* Inutile ici ?
Lemma Euler :
  1 + Cexp (PI%:C * 'i) = 0.
Proof.
rewrite /Cexp ImiRe ReiNIm -complexr0 /= cos_PI sin_PI !complexr0.
rewrite oppr0 exp_0 mul1r; apply/eqP.
by rewrite eq_complex /= addr0 addrN eq_refl.
Qed. *)

(* Utile ?
Lemma ReM (x : complexR) y :
  Re_R (x * (RtoC y)) = (Re_R x) * y.
Proof. by rewrite real_complexE; case: x => r i /=; rewrite !C_simpl. Qed.

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
Qed. *)
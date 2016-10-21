From mathcomp Require Import all_ssreflect.
From mathcomp
Require Import ssralg ssrnum mxpoly rat poly ssrint.
Require Import Cstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Local Notation ZtoC := Cstruct.ZtoC.
Local Notation RtoC := Cstruct.RtoC.
Local Notation QtoC := Cstruct.QtoC.

Section Def.

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

Lemma ratr_eq0 (x : rat) : ((QtoC x) == (0: complexR)) = (x == 0).
Proof.
by rewrite -numq_eq0 mulf_eq0 invr_eq0 !intr_eq0 (negbTE (denq_neq0 x)) orbF.
Qed.

Lemma poly_caract_int (x : complexR) : algebraicOver QtoC x -> x != 0 ->
    exists P : {poly int}, (P != 0) && root (map_poly ZtoC P) x &&
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

Lemma polyMin_subproof (x : complexR) : algebraicOver QtoC x -> x != 0 -> 
    {P : {poly int} | (P != 0) && root (map_poly ZtoC P) x &&
    (P`_0 != 0) && (0 < lead_coef P)}.
Proof.
move => x_alg x_neq0.
move: (sigW (poly_caract_int x_alg x_neq0)) => [P /andP [] /andP [] /andP [] P_neq0 x_root_P P0_neq0 lcP_gt0].
by exists P; rewrite P_neq0 x_root_P P0_neq0 lcP_gt0.
Qed.


Definition algebraic (x : complexR) := algebraicOver QtoC x.

(* TODO : revoir pour apprendre 
Definition polyMin (x : complexR) (H : algebraic x) : {poly int}.
Proof.
case: (boolP (x != 0)) => [x_neq0 | _ ].
  exact: sval(polyMin_subproof H x_neq0).
exact: 'X.
Defined. *)

Definition polyMin (x : complexR) (H : algebraic x) :=
  match Sumbool.sumbool_of_bool(x != 0) with
  |right _ => 'X
  |left toto => sval(polyMin_subproof H toto) 
  end.

Lemma polyMin_neq0 (x : complexR) (H : algebraic x) : (polyMin H) != 0.
Proof.
rewrite /polyMin.
case : ((Sumbool.sumbool_of_bool (x != 0))) => [a | _]; last first.
  by rewrite polyX_eq0.
by move: (svalP (polyMin_subproof H a)) => /andP [ /andP [ /andP [-> _] _] _].
Qed.

Lemma polyMin_root (x : complexR) (H : algebraic x) : 
  root (map_poly ZtoC (polyMin H)) x.
Proof.
rewrite /polyMin.
case : ((Sumbool.sumbool_of_bool (x != 0))) => [a | /eqP ->]; last first.
  by rewrite map_polyX rootX.
by move: (svalP (polyMin_subproof H a)) => /andP [ /andP [ /andP [_ ->] _] _].
Qed.

Lemma polyMin_lcoef_gt0 (x : complexR) (H : algebraic x) : 
  0 < lead_coef (polyMin H).
Proof.
rewrite /polyMin.
case : ((Sumbool.sumbool_of_bool (x != 0))) => [a | _]; last first.
  by rewrite lead_coefX.
by move: (svalP (polyMin_subproof H a)) => /andP [ /andP [ /andP [_ _] _] ->].
Qed.

Definition Cexp_span (n : nat) (a : n.-tuple complexR) (alpha : n.-tuple complexR) :=
  \sum_(i : 'I_n) (tnth a i) * Cexp (tnth alpha i).

End Def.

Section Theory.


End Theory.


Section Wlog1.

Variable l : nat.
Variable alpha : l.-tuple complexR.
Hypothesis alpha_uniq : uniq alpha.
Hypothesis alpha_algebraic : forall i : 'I_l, algebraic (tnth alpha i).
Variable a : l.-tuple complexR.
Hypothesis a_neq0 : forall i : 'I_l, (tnth a i) != 0.
Hypothesis a_algebraic : forall i : 'I_l, algebraic (tnth a i).
About Cexp_span.
Hypothesis Lindemann_false : Cexp_span a alpha == 0.



(* Polynômes associés *)

(* polynôme de chaque a_i *)
Definition poly_a i := polyMin (alpha_algebraic i).

(* produit de tous les polynomes *)
Definition prod_poly_a := \prod_(i : 'I_l) (poly_a i).


(* on récupère l'ensemble des racines 
en séquence pour l'instant, on doit attendre pour la vraie notation 
et qu'on transforme en L.-tuple : b *)
Definition b_seq := sval(closed_field_poly_normal (map_poly ZtoC prod_poly_a)).
Notation L := (size b_seq).
Definition b := in_tuple b_seq.

(* on vérifie que chaque a_i est bien dans b_j *)
Lemma a_in_b : 
  {f : 'I_l -> 'I_L | injective f & forall i : 'I_l, (tnth a i) = (tnth b (f i))}.
Proof.

Search _ "root".

have H x P : root P x -> 
 
polydiv.Pdiv.CommonIdomain.root_factor_theorem:
  forall (R : idomainType) (p : {poly R}) (x : R), root p x = polydiv.Pdiv.IdomainDefs.dvdp ('X - x%:P) p
rootM: forall (R : idomainType) (p q : {poly R}) (x : R), root (p * q) x = root p x || root q x
root_prod_XsubC: forall (R : idomainType) (rs : seq R) (x : R), root (\prod_(a <- rs) ('X - a%:P)) x = (x \in rs)

End Wlog1. 



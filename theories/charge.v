(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
From mathcomp Require Import mathcomp_extra boolp classical_sets cardinality.
From mathcomp Require Import functions fsbigop set_interval.
From HB Require Import structures.
Require Import reals ereal signed topology numfun normedtype sequences.
Require Import esum measure realfun lebesgue_measure lebesgue_integral.

(******************************************************************************)
(*                               Charges                                      *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file contains a formalization of charges (a.k.a. signed measures) and *)
(* their theory (Hahn decomposition theorem, etc.).                           *)
(*                                                                            *)
(* * Mathematical structures                                                  *)
(*       additive_charge T R == type of additive charges over T a semiring    *)
(*                              of sets                                       *)
(*                              The HB class is AdditiveCharge.               *)
(* {additive_charge set T -> \bar R} == notation for additive_charge T R      *)
(*                charge T R == type of charges over T a semiring of sets     *)
(*                              The HB class is Charge.                       *)
(*  {charge set T -> \bar R} == notation for charge T R                       *)
(*  measure_of_charge nu nu0 == measure corresponding to the charge nu, nu0   *)
(*                              is a proof that nu is non-negative            *)
(*                                                                            *)
(* * Instances of mathematical structures                                     *)
(*              crestr nu mD == restriction of the charge nu to the domain D  *)
(*                              where mD is a proof that D is measurable      *)
(*             crestr0 nu mD == csrestr nu mD that returns 0 for              *)
(*                              non-measurable sets                           *)
(*                     czero == zero charge                                   *)
(*               cscale r nu == charge nu scaled by a factor r : R            *)
(*                                                                            *)
(* * Theory                                                                   *)
(*         positive_set nu P == P is a positive set with nu a charge          *)
(*         negative_set nu N == N is a negative set with nu a charge          *)
(* hahn_decomposition nu P N == the full set can be decomposed in P and N,    *)
(*                              a positive set and a negative set for the     *)
(*                              charge nu                                     *)
(*        jordan_pos nu nuPN == the charge obtained by restricting the charge *)
(*                              nu to the positive set P of the Hahn          *)
(*                              decomposition nuPN: hahn_decomposition nu P N *)
(*        jordan_neg nu nuPN == the charge obtained by restricting the charge *)
(*                              nu to the positive set N of the Hahn          *)
(*                              decomposition nuPN: hahn_decomposition nu P N *)
(*              'd nu '/d mu == Radon-Nikodym derivative of nu w.r.t. mu      *)
(*                              (the scope is charge_scope)                   *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "{ 'additive_charge' 'set' T '->' '\bar' R }"
  (at level 36, T, R at next level,
    format "{ 'additive_charge'  'set'  T  '->'  '\bar'  R }").
Reserved Notation "{ 'charge' 'set' T '->' '\bar' R }"
  (at level 36, T, R at next level,
    format "{ 'charge'  'set'  T  '->'  '\bar'  R }").
Reserved Notation "'d nu '/d mu" (at level 10, nu, mu at next level,
  format "''d'  nu  ''/d'  mu").

Declare Scope charge_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

HB.mixin Record isAdditiveCharge d (T : semiRingOfSetsType d) (R : numFieldType)
  (mu : set T -> \bar R) := { charge_semi_additive : semi_additive mu }.

#[short(type=additive_charge)]
HB.structure Definition AdditiveCharge d (T : semiRingOfSetsType d)
  (R : numFieldType) := { mu of isAdditiveCharge d T R mu & FinNumFun d mu }.

Notation "{ 'additive_charge' 'set' T '->' '\bar' R }" :=
  (additive_charge T R) : ring_scope.

#[export] Hint Resolve charge_semi_additive : core.

HB.mixin Record isCharge d (T : semiRingOfSetsType d) (R : numFieldType)
    (mu : set T -> \bar R) := {
  charge_semi_sigma_additive : semi_sigma_additive mu }.

#[short(type=charge)]
HB.structure Definition Charge d (T : semiRingOfSetsType d) (R : numFieldType)
  := { mu of isCharge d T R mu & AdditiveCharge d mu }.

Notation "{ 'charge' 'set' T '->' '\bar' R }" := (charge T R) : ring_scope.

Section charge_lemmas.
Context d (T : measurableType d) (R : numFieldType).
Implicit Type nu : {charge set T -> \bar R}.

Lemma charge0 nu : nu set0 = 0.
Proof.
have /[!big_ord0] ->// := @charge_semi_additive _ _ _ nu (fun=> set0) 0%N.
exact: trivIset_set0.
Qed.

Hint Resolve charge0 : core.

Lemma charge_semi_additiveW nu :
  nu set0 = 0 -> semi_additive nu -> semi_additive2 nu.
Proof.
move=> nu0 anu A B mA mB + AB; rewrite -bigcup2inE bigcup_mkord.
move=> /(anu (bigcup2 A B)) ->.
- by rewrite !(big_ord_recl, big_ord0)/= adde0.
- by move=> [|[|[]]]//=.
- move=> [|[|i]] [|[|j]]/= _ _ //.
  + by rewrite AB => -[].
  + by rewrite setI0 => -[].
  + by rewrite setIC AB => -[].
  + by rewrite setI0 => -[].
  + by rewrite set0I => -[].
  + by rewrite set0I => -[].
  + by rewrite setI0 => -[].
Qed.

Lemma charge_semi_additive2E nu : semi_additive2 nu = additive2 nu.
Proof.
rewrite propeqE; split=> [anu A B ? ? ?|anu A B ? ? _ ?]; last by rewrite anu.
by rewrite anu //; exact: measurableU.
Qed.

Lemma charge_semi_additive2 nu : semi_additive2 nu.
Proof. exact: charge_semi_additiveW. Qed.

Hint Resolve charge_semi_additive2 : core.

Lemma chargeU nu : additive2 nu. Proof. by rewrite -charge_semi_additive2E. Qed.

Lemma chargeDI nu (A B : set T) : measurable A -> measurable B ->
  nu A = nu (A `\` B) + nu (A `&` B).
Proof.
move=> mA mB; rewrite -charge_semi_additive2.
- by rewrite -setDDr setDv setD0.
- exact: measurableD.
- exact: measurableI.
- by apply: measurableU; [exact: measurableD |exact: measurableI].
- by rewrite setDE setIACA setICl setI0.
Qed.

Lemma charge_partition nu S P N :
  measurable S -> measurable P -> measurable N ->
  P `|` N = [set: T] -> P `&` N = set0 -> nu S = nu (S `&` P) + nu (S `&` N).
Proof.
move=> mS mP mN PNT PN0; rewrite -{1}(setIT S) -PNT setIUr chargeU//.
- exact: measurableI.
- exact: measurableI.
- by rewrite setICA -(setIA S P N) PN0 setIA setI0.
Qed.

End charge_lemmas.
#[export] Hint Resolve charge0 : core.
#[export] Hint Resolve charge_semi_additive2 : core.

Definition measure_of_charge d (T : measurableType d) (R : realType)
  (nu : set T -> \bar R) of (forall E, 0 <= nu E) := nu.

Section measure_of_charge.
Context d (T : measurableType d) (R : realType).
Variables (nu : {charge set T -> \bar R}) (nupos : forall E, 0 <= nu E).

Local Notation mu := (measure_of_charge nupos).

Let mu0 : mu set0 = 0. Proof. exact: charge0. Qed.

Let mu_ge0 S : 0 <= mu S. Proof. by rewrite nupos. Qed.

Let mu_sigma_additive : semi_sigma_additive mu.
Proof. exact: charge_semi_sigma_additive. Qed.

HB.instance Definition _ := isMeasure.Build d R T (measure_of_charge nupos)
  mu0 mu_ge0 mu_sigma_additive.

End measure_of_charge.
Arguments measure_of_charge {d T R}.

Section charge_lemmas_realFieldType.
Context d (T : measurableType d) (R : realFieldType).
Implicit Type nu : {charge set T -> \bar R}.

Lemma chargeD nu (A B : set T) : measurable A -> measurable B ->
  nu (A `\` B) = nu A - nu (A `&` B).
Proof.
move=> mA mB.
rewrite (chargeDI nu mA mB) addeK// fin_numE 1?gt_eqF 1?lt_eqF//.
- by rewrite ltey_eq fin_num_measure//; exact:measurableI.
- by rewrite ltNye_eq fin_num_measure//; exact:measurableI.
Qed.

End charge_lemmas_realFieldType.

Definition crestr d (T : measurableType d) (R : numDomainType) (D : set T)
  (f : set T -> \bar R) of measurable D := fun X => f (X `&` D).

Section charge_restriction.
Context d (T : measurableType d) (R : numFieldType).
Variables (nu : {charge set T -> \bar R}) (D : set T) (mD : measurable D).

Local Notation restr := (crestr nu mD).

Let crestr_finite_measure_function U : measurable U -> restr U \is a fin_num.
Proof.
move=> mU.
by have /(fin_num_measure nu) : measurable (U `&` D) by exact: measurableI.
Qed.

HB.instance Definition _ := SigmaFinite_isFinite.Build _ _ _
  restr crestr_finite_measure_function.

Let crestr_semi_additive : semi_additive restr.
Proof.
move=> F n mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
rewrite -(charge_semi_additive _ _ mFD)//; last exact: bigsetU_measurable.
by rewrite /crestr /FD big_distrl.
Qed.

HB.instance Definition _ :=
  isAdditiveCharge.Build _ _ _ restr crestr_semi_additive.

Let crestr_semi_sigma_additive : semi_sigma_additive restr.
Proof.
move=> F mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
rewrite /restr setI_bigcupl; apply: charge_semi_sigma_additive => //.
by apply: bigcup_measurable => k _; exact: measurableI.
Qed.

HB.instance Definition _ :=
  isCharge.Build _ _ _ restr crestr_semi_sigma_additive.

End charge_restriction.

Definition crestr0 d (T : measurableType d) (R : realFieldType) (D : set T)
  (f : set T -> \bar R) (mD : measurable D) :=
    fun X => if X \in measurable then crestr f mD X else 0.

Section charge_restriction0.
Context d (T : measurableType d) (R : realFieldType).
Variables (nu : {charge set T -> \bar R}) (D : set T) (mD : measurable D).

Local Notation restr := (crestr0 nu mD).

Let crestr0_fin_num_fun : fin_num_fun restr.
Proof. by move=> U mU; rewrite /crestr0 mem_set// fin_num_measure. Qed.

HB.instance Definition _ := SigmaFinite_isFinite.Build _ _ _
  restr crestr0_fin_num_fun.

Let crestr0_additive : semi_additive restr.
Proof.
move=> F n mF tF mU; rewrite /crestr0 mem_set// charge_semi_additive//=.
by apply: eq_bigr => i _; rewrite mem_set.
Qed.

HB.instance Definition _ := isAdditiveCharge.Build _ _ _ restr crestr0_additive.

Let crestr0_sigma_additive : semi_sigma_additive restr.
Proof.
move=> F mF tF mU; rewrite /crestr0 mem_set//.
rewrite [X in X --> _](_ : _ = (fun n => \sum_(0 <= i < n) crestr nu mD (F i))).
  exact: charge_semi_sigma_additive.
by apply/funext => n; apply: eq_bigr => i _; rewrite mem_set.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ restr crestr0_sigma_additive.

End charge_restriction0.

Section charge_zero.
Context d (T : measurableType d) (R : realFieldType).
Local Open Scope ereal_scope.

Definition czero (A : set T) : \bar R := 0.

Let czero0 : czero set0 = 0. Proof. by []. Qed.

Let czero_finite_measure_function B : measurable B -> czero B \is a fin_num.
Proof. by []. Qed.

HB.instance Definition _ := SigmaFinite_isFinite.Build _ _ _
  czero czero_finite_measure_function.

Let czero_semi_additive : semi_additive czero.
Proof. by move=> F n mF tF mUF; rewrite /czero big1. Qed.

HB.instance Definition _ :=
  isAdditiveCharge.Build _ _ _ czero czero_semi_additive.

Let czero_sigma_additive : semi_sigma_additive czero.
Proof.
move=> F mF tF mUF; rewrite [X in X --> _](_ : _ = cst 0); first exact: cvg_cst.
by apply/funext => n; rewrite big1.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ czero czero_sigma_additive.

End charge_zero.
Arguments czero {d T R}.

Section charge_scale.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realFieldType).
Variables (r : R) (nu : {charge set T -> \bar R}).

Definition cscale (A : set T) : \bar R := r%:E * nu A.

Let cscale0 : cscale set0 = 0. Proof. by rewrite /cscale charge0 mule0. Qed.

Let cscale_finite_measure_function U : measurable U -> cscale U \is a fin_num.
Proof. by move=> mU; apply: fin_numM => //; exact: fin_num_measure. Qed.

HB.instance Definition _ := SigmaFinite_isFinite.Build _ _ _
  cscale cscale_finite_measure_function.

Let cscale_semi_additive : semi_additive cscale.
Proof.
move=> F n mF tF mU; rewrite /cscale charge_semi_additive//.
rewrite fin_num_sume_distrr// => i j _ _.
by rewrite fin_num_adde_defl// fin_num_measure.
Qed.

HB.instance Definition _ :=
  isAdditiveCharge.Build _ _ _ cscale cscale_semi_additive.

Let cscale_sigma_additive : semi_sigma_additive cscale.
Proof.
move=> F mF tF mUF; rewrite /cscale; rewrite [X in X --> _](_ : _ =
    (fun n => r%:E * \sum_(0 <= i < n) nu (F i))); last first.
  apply/funext => k; rewrite fin_num_sume_distrr// => i j _ _.
  by rewrite fin_num_adde_defl// fin_num_measure.
rewrite /mscale; have [->|r0] := eqVneq r 0%R.
  rewrite mul0e [X in X --> _](_ : _ = (fun=> 0)); first exact: cvg_cst.
  by under eq_fun do rewrite mul0e.
by apply: cvgeMl => //; apply: charge_semi_sigma_additive.
Qed.

HB.instance Definition _ := isCharge.Build _ _ _ cscale
  cscale_sigma_additive.

End charge_scale.

Section positive_negative_set.
Context d (R : numDomainType) (T : measurableType d).
Implicit Types nu : set T -> \bar R.

Definition positive_set nu (P : set T) :=
  measurable P /\ forall A, measurable A -> A `<=` P -> nu A >= 0.

Definition negative_set nu (N : set T) :=
  measurable N /\ forall A, measurable A -> A `<=` N -> nu A <= 0.

End positive_negative_set.

Section positive_negative_set_lemmas.
Context d (T : measurableType d) (R : numFieldType).
Implicit Types nu : {charge set T -> \bar R}.

Lemma negative_set_charge_le0 nu N : negative_set nu N -> nu N <= 0.
Proof. by move=> [mN]; exact. Qed.

Lemma negative_set0 nu : negative_set nu set0.
Proof. by split => // A _; rewrite subset0 => ->; rewrite charge0. Qed.

Lemma positive_negative0 nu P N : positive_set nu P -> negative_set nu N ->
  forall S, measurable S -> nu (S `&` P `&` N) = 0.
Proof.
move=> [mP posP] [mN negN] S mS; apply/eqP; rewrite eq_le; apply/andP; split.
  apply: negN; first by apply: measurableI => //; exact: measurableI.
  by apply/setIidPl; rewrite -setIA setIid.
rewrite -setIAC.
apply: posP; first by apply: measurableI => //; exact: measurableI.
by apply/setIidPl; rewrite -setIA setIid.
Qed.

End positive_negative_set_lemmas.

Section positive_negative_set_realFieldType.
Context d (T : measurableType d) (R : realFieldType).
Implicit Types nu : {charge set T -> \bar R}.

Lemma bigcup_negative_set nu (F : (set T)^nat) :
    (forall i, negative_set nu (F i)) ->
  negative_set nu (\bigcup_i F i).
Proof.
move=> hF; have mUF : measurable (\bigcup_k F k).
  by apply: bigcup_measurable => n _; have [] := hF n.
split=> [//|S mS SUF].
pose SF n := (S `&` F n) `\` \bigcup_(k < n) F k.
have SSF : S = \bigcup_i SF i.
  transitivity (\bigcup_k seqDU (fun n => S `&` F n) k); last first.
    by apply: eq_bigcup => // n _; rewrite seqDUIE.
  by rewrite -seqDU_bigcup_eq -setI_bigcupr setIidl.
have mSF n : measurable (SF n).
  apply: measurableD; first by apply: measurableI => //; have [] := hF n.
  by apply: bigcup_measurable => // k _; have [] := hF k.
have SFS : (fun n => \sum_(0 <= i < n) nu (SF i)) --> nu S.
  by rewrite SSF; apply: charge_semi_sigma_additive => //;
    [by rewrite /SF -seqDUIE; exact: trivIset_seqDU|exact: bigcup_measurable].
have nuS_ n : nu (SF n) <= 0 by have [_] := hF n; apply => // x -[[]].
move/cvg_lim : (SFS) => <-//; apply: lime_le.
  by apply/cvg_ex => /=; first eexists; exact: SFS.
by apply: nearW => n; exact: sume_le0.
Qed.

Lemma negative_setU nu N M :
  negative_set nu N -> negative_set nu M -> negative_set nu (N `|` M).
Proof.
move=> nN nM; rewrite -bigcup2E; apply: bigcup_negative_set => -[//|[//|/= _]].
exact: negative_set0.
Qed.

End positive_negative_set_realFieldType.

Section hahn_decomposition_lemma.
Context d (T : measurableType d) (R : realType).
Variables (nu : {charge set T -> \bar R}) (D : set T).

Let elt_prop (x : set T * \bar R) := [/\ measurable x.1,
  x.1 `<=` D, 0 <= x.2 & nu x.1 >= mine (x.2 * 2^-1%:E) 1].

Let elt_type := {x : set T * \bar R * set T | elt_prop x.1}.

Let A_ (x : elt_type) := (proj1_sig x).1.1.
Let g_ (x : elt_type) := (proj1_sig x).1.2.
Let U_ (x : elt_type) := (proj1_sig x).2.

Let mA_ x : measurable (A_ x). Proof. by move: x => [[[? ?] ?]] []. Qed.
Let A_D x : A_ x `<=` D. Proof. by move: x => [[[? ?] ?]] []. Qed.
Let g_ge0 x : 0 <= g_ x. Proof. by move: x => [[[? ?] ?]] []. Qed.
Let nuA_g_ x : nu (A_ x) >= mine (g_ x * 2^-1%:E) 1.
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let nuA_ge0 x : 0 <= nu (A_ x).
Proof. by rewrite (le_trans _ (nuA_g_ _))// le_minr lee01 andbT mule_ge0. Qed.

Let subDD A := [set nu E | E in [set E | measurable E /\ E `<=` D `\` A] ].

Let d_ A := ereal_sup (subDD A).

Let d_ge0 X : 0 <= d_ X.
Proof. by apply: ereal_sup_ub => /=; exists set0; rewrite ?charge0. Qed.

Let elt_rel i j :=
  [/\ g_ j = d_ (U_ i),  A_ j `<=` D `\` U_ i & U_ j = U_ i `|` A_ j ].

Let next_elt A :
  { B | [/\ measurable B, B `<=` D `\` A & nu B >= mine (d_ A * 2^-1%:E) 1] }.
Proof.
pose m := mine (d_ A * 2^-1%R%:E) 1; apply/cid.
have := d_ge0 A; rewrite le_eqVlt => /predU1P[<-|d_gt0].
  by exists set0; split => //; rewrite charge0.
have /ereal_sup_gt/cid2[_ [B/= [mB BDA <- mnuB]]] : m < d_ A.
  rewrite /m; have [->|dn1oo] := eqVneq (d_ A) +oo.
    by rewrite min_r ?ltey ?gt0_mulye ?leey.
  rewrite -(@fineK _ (d_ A)); last first.
    by rewrite ge0_fin_numE// ?(ltW d_gt0)// lt_neqAle dn1oo leey.
  rewrite -EFinM -fine_min// lte_fin lt_minl; apply/orP; left.
  by rewrite ltr_pdivr_mulr// ltr_pmulr ?ltr1n// fine_gt0// d_gt0/= ltey.
by exists B; split => //; rewrite (le_trans _ (ltW mnuB)).
Qed.

(* TODO: generalize? *)
Let minr_cvg_0_cvg_0 (x : R^nat) : (forall k, 0 <= x k)%R ->
  (fun n => minr (x n * 2^-1) 1)%R --> (0:R)%R -> x --> (0:R)%R.
Proof.
move=> x_ge0 minr_cvg.
apply/(@cvgrPdist_lt _ [normedModType R of R^o]) => _ /posnumP[e].
have : (0 < minr (e%:num / 2) 1)%R by rewrite lt_minr// ltr01 andbT divr_gt0.
move/(@cvgrPdist_lt _ [normedModType R of R^o]) : minr_cvg => /[apply] -[M _ hM].
near=> n; rewrite sub0r normrN.
have /hM : (M <= n)%N by near: n; exists M.
rewrite sub0r normrN !ger0_norm// ?le_minr ?divr_ge0//=.
rewrite -[X in minr _ X](@divrr _ 2) ?unitfE -?minr_pmull//.
rewrite -[X in (_ < minr _ X)%R](@divrr _ 2) ?unitfE -?minr_pmull//.
by rewrite ltr_pmul2r//; exact: lt_min_lt.
Unshelve. all: by end_near. Qed.

Let mine_cvg_0_cvg_fin_num (x : (\bar R)^nat) : (forall k, 0 <= x k) ->
  (fun n => mine (x n * (2^-1)%:E) 1) --> 0 ->
  \forall n \near \oo, x n \is a fin_num.
Proof.
move=> x_ge0 /fine_cvgP[_].
move=> /(@cvgrPdist_lt _ [normedModType R of R^o])/(_ _ ltr01)[N _ hN].
near=> n; have /hN : (N <= n)%N by near: n; exists N.
rewrite sub0r normrN /= ger0_norm ?fine_ge0//; last first.
  by rewrite le_minr mule_ge0//=.
by have := x_ge0 n; case: (x n) => //=; rewrite gt0_mulye//= ltxx.
Unshelve. all: by end_near. Qed.

Let mine_cvg_minr_cvg (x : (\bar R)^nat) : (forall k, 0 <= x k) ->
  (fun n => mine (x n * (2^-1)%:E) 1) --> 0 ->
  (fun n => minr ((fine \o x) n / 2) 1%R) --> (0:R)%R.
Proof.
move=> x_ge0 mine_cvg.
apply: (cvg_trans _ (fine_cvg mine_cvg)).
move/fine_cvgP : mine_cvg => [_ /=] /(@cvgrPdist_lt _ [normedModType R of R^o]).
move=> /(_ _ ltr01)[N _ hN]; apply: near_eq_cvg; near=> n.
have xnoo : x n < +oo.
  rewrite ltNge leye_eq; apply/eqP => xnoo.
  have /hN : (N <= n)%N by near: n; exists N.
  by rewrite /= sub0r normrN xnoo gt0_mulye//= normr1 ltxx.
by rewrite /= -(@fineK _ (x n)) ?ge0_fin_numE//= -fine_min.
Unshelve. all: by end_near. Qed.

Let mine_cvg_0_cvg_0 (x : (\bar R)^nat) : (forall k, 0 <= x k) ->
  (fun n => mine (x n * (2^-1)%:E) 1) --> 0 -> x --> 0.
Proof.
move=> x_ge0 h; apply/fine_cvgP; split; first exact: mine_cvg_0_cvg_fin_num.
apply: (@minr_cvg_0_cvg_0 (fine \o x)) => //; last exact: mine_cvg_minr_cvg.
by move=> k /=; rewrite fine_ge0.
Qed.

Lemma hahn_decomposition_lemma : measurable D ->
  {A | [/\ A `<=` D, negative_set nu A & nu A <= nu D]}.
Proof.
move=> mD; have [A0 [mA0 + A0d0]] := next_elt set0.
rewrite setD0 => A0D.
have [v [v0 Pv]] : {v : nat -> elt_type |
    v 0%N = exist _ (A0, d_ set0, A0) (And4 mA0 A0D (d_ge0 set0) A0d0) /\
    forall n, elt_rel (v n) (v n.+1)}.
  apply: dependent_choice_Type => -[[[A' ?] U] [/= mA' A'D]].
  have [A1 [mA1 A1DU A1t1] ] := next_elt U.
  have A1D : A1 `<=` D by apply: (subset_trans A1DU); apply: subDsetl.
  by exists (exist _ (A1, d_ U, U `|` A1) (And4 mA1 A1D (d_ge0 U) A1t1)).
have Ubig n : U_ (v n) = \big[setU/set0]_(i < n.+1) A_ (v i).
  elim: n => [|n ih]; first by rewrite v0/= big_ord_recr/= big_ord0 set0U v0.
  by have [_ _ ->] := Pv n; rewrite big_ord_recr/= -ih.
have tA : trivIset setT (A_ \o v).
  apply: subsetC_trivIset => n.
  have [_ + _] := Pv n; move/subset_trans; apply.
  by rewrite -setTD; apply: setDSS => //; rewrite Ubig big_ord_recr.
set Aoo := \bigcup_k A_ (v k).
have mAoo : measurable Aoo by exact: bigcup_measurable.
exists (D `\` Aoo).
have cvg_nuA : (fun n => \sum_(0 <= i < n) nu (A_ (v i))) --> nu Aoo.
  exact: charge_semi_sigma_additive.
have nuAoo : 0 <= nu Aoo.
  move/cvg_lim : cvg_nuA => <-//=; apply: nneseries_ge0 => n _.
  exact: nuA_ge0.
have A_cvg_0 : (fun n => nu (A_ (v n))) --> 0.
  rewrite [X in X --> _](_ : _ = (fun n => (fine (nu (A_ (v n))))%:E)); last first.
    by apply/funext => n/=; rewrite fineK// fin_num_measure.
  apply: continuous_cvg => //.
  apply: (@cvg_series_cvg_0 _ [normedModType R of R^o]).
  rewrite (_ : series _ =
      fine \o (fun n => \sum_(0 <= i < n) nu (A_ (v i)))); last first.
    apply/funext => n /=.
    by rewrite /series/= sum_fine//= => i _; rewrite fin_num_measure.
  move: cvg_nuA; rewrite -(@fineK _ (nu Aoo)) ?fin_num_measure//.
  by move=> /fine_cvgP[_ ?]; apply/cvg_ex; exists (fine (nu Aoo)).
have mine_cvg_0 : (fun n => mine (g_ (v n) * 2^-1%:E) 1) --> 0.
  apply: (@squeeze_cvge _ _ _ _ _ _ (fun n => nu (A_ (v n))));
    [|exact: cvg_cst|by []].
  by apply: nearW => n /=; rewrite nuA_g_ andbT le_minr lee01 andbT mule_ge0.
have d_cvg_0 : g_ \o v --> 0 by apply: mine_cvg_0_cvg_0 => //=.
have nuDAoo : nu D >= nu (D `\` Aoo).
  rewrite -[in leRHS](@setDUK _ Aoo D); last first.
    by apply: bigcup_sub => i _; exact: A_D.
  by rewrite chargeU// ?lee_addr// ?setDIK//; exact: measurableD.
split; [by []| |by []]; split; [exact: measurableD | move=> E mE EDAoo].
pose H n := subDD (\big[setU/set0]_(i < n) A_ (v i)).
have EH n : [set nu E] `<=` H n.
  have : nu E \in subDD Aoo by rewrite inE; exists E.
  rewrite -sub1set => /subset_trans; apply => x/= [F [mF FDAoo ?]].
  exists F => //; split => //.
  by apply: (subset_trans FDAoo); apply: setDS; exact: bigsetU_bigcup.
have nudelta n : nu E <= g_ (v n).
  move: n => [|n].
    rewrite v0/=; apply: ereal_sup_ub => /=; exists E; split => //.
    by apply: (subset_trans EDAoo); exact: setDS.
  suff : nu E <= d_ (U_ (v n)) by have [<- _] := Pv n.
  have /le_ereal_sup := EH n.+1; rewrite ereal_sup1 => /le_trans; apply.
  apply/le_ereal_sup => x/= [A' [mA' A'D ?]].
  exists A' => //; split => //.
  by apply: (subset_trans A'D); apply: setDS; rewrite Ubig.
apply: (@closed_cvg _ _ _ _ _ (fun v => nu E <= v) _ _ _ d_cvg_0) => //.
  exact: closed_ereal_le_ereal.
exact: nearW.
Unshelve. all: by end_near. Qed.

End hahn_decomposition_lemma.

Definition hahn_decomposition d (T : measurableType d) (R : realType)
    (nu : {charge set T -> \bar R}) P N :=
  [/\ positive_set nu P, negative_set nu N, P `|` N = [set: T] & P `&` N = set0].

Section hahn_decomposition_theorem.
Context d (T : measurableType d) (R : realType).
Variable nu : {charge set T -> \bar R}.

Let elt_prop (x : set T * \bar R) := [/\ x.2 <= 0,
  negative_set nu x.1 & nu x.1 <= maxe (x.2 * 2^-1%:E) (- 1%E) ].

Let elt_type := {AzU : set T * \bar R * set T | elt_prop AzU.1}.

Let A_ (x : elt_type) := (proj1_sig x).1.1.
Let z_ (x : elt_type) := (proj1_sig x).1.2.
Let U_ (x : elt_type) := (proj1_sig x).2.

Let mA_ x : measurable (A_ x). Proof. by move: x => [[[? ?] ?] [/= ? []]]. Qed.
Let negative_set_A_ x : negative_set nu (A_ x).
Proof. by move: x => [[[? ?] ?]] -[]. Qed.
Let nuA_z_ x : nu (A_ x) <= maxe (z_ x * 2^-1%:E) (- 1%E).
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let nuA_le0 x : nu (A_ x) <= 0.
Proof. by move: x => [[[? ?] ?]] [? h ?]; exact: negative_set_charge_le0. Qed.

Let z_le0 x : z_ x <= 0.
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let subC A := [set nu E | E in [set E | measurable E /\ E `<=` ~` A] ].

Let s_ A := ereal_inf (subC A).

Let s_le0 X : s_ X <= 0.
Proof.
by apply: ereal_inf_lb => /=; exists set0; rewrite ?charge0//=; split.
Qed.

Let elt_rel i j :=
  [/\ z_ j = s_ (U_ i), A_ j `<=` ~` U_ i & U_ j = U_ i `|` A_ j].

Let next_elt U : { A | [/\ A `<=` ~` U,
  negative_set nu A & nu A <= maxe (s_ U * 2^-1%R%:E) (- 1%E)] }.
Proof.
pose m := maxe (s_ U * 2^-1%R%:E) (- 1%E); apply/cid.
have := s_le0 U; rewrite le_eqVlt => /predU1P[->|s_lt0].
  by exists set0; split => //; rewrite ?charge0//; exact: negative_set0.
have /ereal_inf_lt/cid2[_ [B/= [mB BU] <-] nuBm] : s_ U < m.
  rewrite /m; have [->|s0oo] := eqVneq (s_ U) -oo.
    by rewrite max_r ?ltNye// gt0_mulNye// leNye.
  rewrite -(@fineK _ (s_ U)); last first.
    by rewrite le0_fin_numE// ?(ltW s_lt0)// lt_neqAle leNye eq_sym s0oo.
  rewrite -EFinM -fine_max// lte_fin lt_maxr; apply/orP; left.
  by rewrite ltr_pdivl_mulr// gtr_nmulr ?ltr1n// fine_lt0// s_lt0/= ltNye andbT.
have [C [CB nsC nuCB]] := hahn_decomposition_lemma nu mB.
exists C; split => //; first exact: (subset_trans CB).
by rewrite (le_trans nuCB)// (le_trans (ltW nuBm)).
Qed.

Theorem Hahn_decomposition : exists P N, hahn_decomposition nu P N.
Proof.
have [A0 [_ negA0 A0s0]] := next_elt set0.
have [v [v0 Pv]] : {v |
    v 0%N = exist _ (A0, s_ set0, A0) (And3 (s_le0 set0) negA0 A0s0) /\
    forall n, elt_rel (v n) (v n.+1)}.
  apply: dependent_choice_Type => -[[[A s] U] [/= s_le0' nsA]].
  have [A' [? nsA' A's'] ] := next_elt U.
  by exists (exist _ (A', s_ U, U `|` A') (And3 (s_le0 U) nsA' A's')).
have Ubig n : U_ (v n) = \big[setU/set0]_(i < n.+1) A_ (v i).
  elim: n => [|n ih]; first by rewrite v0/= big_ord_recr/= big_ord0 set0U v0.
  by have [_ _ ->] := Pv n; rewrite big_ord_recr/= -ih.
have tA : trivIset setT (A_ \o v).
  apply: subsetC_trivIset => n.
  have [_ + _] := Pv n; move/subset_trans; apply.
  by apply: subsetC; rewrite Ubig big_ord_recr.
set N := \bigcup_k (A_ (v k)).
have mN : measurable N by exact: bigcup_measurable.
have neg_set_N : negative_set nu N.
  by apply: bigcup_negative_set => i; exact: negative_set_A_.
pose P := ~` N.
have mP : measurable P by exact: measurableC.
exists P, N; split; [|exact: neg_set_N|by rewrite /P setvU|by rewrite /P setICl].
split=> // D mD DP; rewrite leNgt; apply/negP => nuD0.
have znuD n : z_ (v n) <= nu D.
  move: n => [|n].
    by rewrite v0 /=; apply: ereal_inf_lb; exists D; split => //; rewrite setC0.
  have [-> _ _] := Pv n; apply: ereal_inf_lb => /=; exists D; split => //.
  apply: (subset_trans DP); apply: subsetC; rewrite Ubig.
  exact: bigsetU_bigcup.
have max_le0 n : maxe (z_ (v n) * 2^-1%:E) (- 1%E) <= 0.
  by rewrite le_maxl leeN10 andbT pmule_lle0.
have not_s_cvg_0 : ~ z_ \o v --> 0.
  move/fine_cvgP => -[zfin] /(@cvgrPdist_lt _ [normedModType R of R^o]).
  have /[swap] /[apply] -[M _ hM] : (0 < `|fine (nu D)|)%R.
    by rewrite normr_gt0// fine_eq0// ?lt_eqF// fin_num_measure.
  near \oo => n.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN /= ler0_norm ?fine_le0// ltr0_norm//; last first.
    by rewrite fine_lt0// nuD0 andbT ltNye_eq fin_num_measure.
  rewrite ltr_opp2; apply/negP; rewrite -leNgt fine_le ?fin_num_measure//.
  by near: n; exact.
have nuN : nu N = \sum_(n <oo) nu (A_ (v n)).
  apply/esym/cvg_lim => //.
  by apply: charge_semi_sigma_additive; [|exact: tA|exact: bigcup_measurable].
have sum_A_maxe : \sum_(n <oo) nu (A_ (v n)) <=
    \sum_(n <oo) maxe (z_ (v n) * 2^-1%:E) (- 1%E) by exact: lee_npeseries.
have : cvg (fun n => \sum_(0 <= k < n) maxe (z_ (v k) * 2^-1%:E) (- 1%E)).
  by apply: is_cvg_ereal_npos_natsum_cond => n _ _; exact: max_le0.
move=> /cvg_ex[[l| |]]; first last.
  - move/cvg_lim => limNoo.
    have : nu N <= -oo by rewrite -limNoo// nuN.
    by rewrite leNgt => /negP; apply; rewrite ltNye_eq fin_num_measure.
  - move/cvg_lim => limoo.
    have := @npeseries_le0 _ (fun n => maxe (z_ (v n) * 2^-1%:E) (- 1%E)) xpredT 0.
    by rewrite limoo// leNgt => /(_ (fun n _ => max_le0 n))/negP; apply.
move/fine_cvgP => [Hfin cvgl].
have : cvg (series (fun n => fine (maxe (z_ (v n) * 2^-1%:E) (- 1%E)))).
  apply/cvg_ex; exists l; move: cvgl.
  rewrite (_ : _ \o _ = (fun n =>
    \sum_(0 <= k < n) fine (maxe (z_ (v k) * 2^-1%:E)%E (- 1%E)%E))%R) //.
  apply/funext => n/=; rewrite sum_fine// => m _.
  rewrite le0_fin_numE; first by rewrite lt_maxr ltNyr orbT.
  by rewrite /maxe; case: ifPn => // _; rewrite mule_le0_ge0.
move/(@cvg_series_cvg_0 _ [normedModType R of R^o]) => maxe_cvg_0.
apply: not_s_cvg_0.
rewrite (_ : _ \o _ = (fun n => z_ (v n) * 2^-1%:E) \* cst 2%:E); last first.
  by apply/funext => n/=; rewrite -muleA -EFinM mulVr ?mule1// unitfE.
rewrite (_ : 0 = 0 * 2%:E); last by rewrite mul0e.
apply: cvgeM; [by rewrite mule_def_fin| |exact: cvg_cst].
apply/fine_cvgP; split.
  move/cvgrPdist_lt : maxe_cvg_0 => /(_ _ ltr01)[M _ hM]; near=> n.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN ltNge => maxe_lt1; rewrite fin_numE; apply/andP; split.
    by apply: contra maxe_lt1 => /eqP ->; rewrite max_r ?leNye//= normrN1 lexx.
  by rewrite lt_eqF// (@le_lt_trans _ _ 0)// mule_le0_ge0.
apply/(@cvgrPdist_lt _ [normedModType R of R^o]) => _ /posnumP[e].
have : (0 < minr e%:num 1)%R by rewrite lt_minr// ltr01 andbT.
move/cvgrPdist_lt : maxe_cvg_0 => /[apply] -[M _ hM].
near=> n; rewrite sub0r normrN.
have /hM : (M <= n)%N by near: n; exists M.
rewrite sub0r normrN /maxe/=; case: ifPn => [_|].
  by rewrite normrN normr1 lt_minr ltxx andbF.
by rewrite -leNgt => ? /lt_le_trans; apply; rewrite le_minl lexx.
Unshelve. all: by end_near. Qed.

Lemma Hahn_decomposition_uniq P1 N1 P2 N2 :
  hahn_decomposition nu P1 N1 -> hahn_decomposition nu P2 N2 ->
  forall S, measurable S ->
    nu (S `&` P1) = nu (S `&` P2) /\ nu (S `&` N1) = nu (S `&` N2).
Proof.
move=> [psP1 nsN1 PN1T PN10] [psP2 nsN2 PN2T PN20] S mS.
move: (psP1) (nsN1) (psP2) (nsN2) => [mP1 _] [mN1 _] [mP2 _] [mN2 _].
split.
- transitivity (nu (S `&` P1 `&` P2)).
  + rewrite (charge_partition _ _ mP2 mN2)//; last exact: measurableI.
    by rewrite (positive_negative0 psP1 nsN2 mS) adde0.
  + rewrite [RHS](charge_partition _ _ mP1 mN1)//; last exact: measurableI.
    by rewrite (positive_negative0 psP2 nsN1 mS) adde0 setIAC.
- transitivity (nu (S `&` N1 `&` N2)).
  + rewrite (charge_partition nu _ mP2 mN2)//; last exact: measurableI.
    have := positive_negative0 psP2 nsN1 mS.
    by rewrite setIAC => ->; rewrite add0e.
  + rewrite [RHS](charge_partition nu _ mP1 mN1)//; last exact: measurableI.
    by rewrite (setIAC _ _ P1) (positive_negative0 psP1 nsN2 mS) add0e setIAC.
Qed.

End hahn_decomposition_theorem.

Section jordan_decomposition.
Context d (T : measurableType d) (R : realType).
Variable nu : {charge set T -> \bar R}.
Variables (P N : set T) (nuPN : hahn_decomposition nu P N).

Let mP : measurable P. Proof. by have [[mP _] _ _ _] := nuPN. Qed.

Let mN : measurable N. Proof. by have [_ [mN _] _ _] := nuPN. Qed.

Let cjordan_pos : {charge set T -> \bar R} :=
  [the charge _ _ of crestr0 nu mP].

Let positive_set_cjordan_pos E : 0 <= cjordan_pos E.
Proof.
have [posP _ _ _] := nuPN.
rewrite /cjordan_pos/= /crestr0/=; case: ifPn => // /[1!inE] mE.
by apply posP; [apply: measurableI|apply: subIsetr].
Qed.

Definition jordan_pos := measure_of_charge _ positive_set_cjordan_pos.

HB.instance Definition _ := Measure.on jordan_pos.

Let finite_jordan_pos : fin_num_fun jordan_pos.
Proof. by move=> U mU; rewrite fin_num_measure. Qed.

HB.instance Definition _ := @Measure_isFinite.Build _ _ _
  jordan_pos finite_jordan_pos.

Let cjordan_neg : {charge set T -> \bar R} :=
  [the charge _ _ of cscale (-1) [the charge _ _ of crestr0 nu mN]].

Let positive_set_cjordan_neg E : 0 <= cjordan_neg E.
Proof.
rewrite /cjordan_neg/= /cscale/= /crestr0/= muleC mule_le0//.
case: ifPn => // /[1!inE] mE.
by move: nuPN => [_ [_ +] _ _] => -> //; exact: measurableI.
Qed.

Definition jordan_neg := measure_of_charge _ positive_set_cjordan_neg.

HB.instance Definition _ := Measure.on jordan_neg.

Let finite_jordan_neg : fin_num_fun jordan_neg.
Proof. by move=> U mU; rewrite fin_num_measure. Qed.

HB.instance Definition _ := @Measure_isFinite.Build _ _ _
  jordan_neg finite_jordan_neg.

Lemma jordan_decomp A : measurable A -> nu A = jordan_pos A - jordan_neg A.
Proof.
move=> mA; rewrite /jordan_pos /jordan_neg/= /measure_of_charge/=.
rewrite /cscale/= /crestr0/= mem_set// -[in LHS](setIT A).
case: nuPN => _ _ <- PN0; rewrite setIUr chargeU//.
- by rewrite EFinN mulN1e oppeK.
- exact: measurableI.
- exact: measurableI.
- by rewrite setIACA PN0 setI0.
Qed.

Lemma jordan_pos_dominates (mu : {measure set T -> \bar R}) :
  nu `<< mu -> jordan_pos `<< mu.
Proof.
move=> nu_mu A mA muA0; have := nu_mu A mA muA0.
rewrite jordan_decomp// /jordan_pos /jordan_neg /measure_of_charge/=.
rewrite /cscale/= /crestr0/= mem_set// EFinN mulN1e oppeK.
have mAP : measurable (A `&` P) by exact: measurableI.
suff : mu (A `&` P) = 0 by move/(nu_mu _ mAP); rewrite /crestr => ->.
by apply/eqP; rewrite eq_le measure_ge0// andbT -muA0 le_measure// inE.
Qed.

Lemma jordan_neg_dominates (mu : {measure set T -> \bar R}) :
  nu `<< mu -> jordan_neg `<< mu.
Proof.
move=> nu_mu A mA muA0; have := nu_mu A mA muA0.
rewrite jordan_decomp// /jordan_pos /jordan_neg /measure_of_charge/=.
rewrite /cscale/= /crestr0/= mem_set//.
have mAN : measurable (A `&` N) by exact: measurableI.
suff : mu (A `&` N) = 0.
  by move=> /(nu_mu _ mAN); rewrite /crestr => ->; rewrite mule0.
by apply/eqP; rewrite eq_le measure_ge0// andbT -muA0 le_measure// inE.
Qed.

End jordan_decomposition.

(* We put definitions and lemmas used only in the proof of the Radon-Nikodym
   theorem as Definition's and Lemma's in the following modules. See
   https://staff.aist.go.jp/reynald.affeldt/documents/measure-ppl2023.pdf
   for an overview. *)
Module approxRN.
Section approxRN.
Context d (T : measurableType d) (R : realType).
Variables mu nu : {measure set T -> \bar R}.

Definition approxRN := [set g : T -> \bar R | [/\
  forall x, 0 <= g x, mu.-integrable [set: T] g &
  forall E, measurable E -> \int[mu]_(x in E) g x <= nu E] ].

Let approxRN_neq0 : approxRN !=set0.
Proof.
exists (cst 0); split => //; first exact: integrable0.
by move=> E mE; rewrite integral0 measure_ge0.
Qed.

Definition int_approxRN := [set \int[mu]_x g x | g in approxRN].

Definition sup_int_approxRN := ereal_sup int_approxRN.

Lemma sup_int_approxRN_ge0 : 0 <= sup_int_approxRN.
Proof.
rewrite -(ereal_sup1 0) le_ereal_sup// sub1set inE.
exists (fun=> 0); last exact: integral0.
by split => //; [exact: integrable0|move=> E; rewrite integral0].
Qed.

End approxRN.
End approxRN.

Module approxRN_seq.
Section approxRN_seq.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variable nu : {finite_measure set T -> \bar R}.

Import approxRN.

Let approxRN := approxRN mu nu.
Let int_approxRN := int_approxRN mu nu.
Let M := sup_int_approxRN mu nu.

Let int_approxRN_ub : exists M, forall x, x \in int_approxRN -> x <= M%:E.
Proof.
exists (fine (nu setT)) => x /[1!inE] -[g [g0 g1 g2] <-{x}].
by rewrite fineK ?fin_num_measure// (le_trans (g2 setT _))// inE.
Qed.

Lemma sup_int_approxRN_lty : M < +oo.
Proof.
rewrite /sup_int_approxRN; have [m hm] := int_approxRN_ub.
rewrite (@le_lt_trans _ _ m%:E)// ?ltey// ub_ereal_sup// => x IGx.
by apply: hm; rewrite inE.
Qed.

Lemma sup_int_approxRN_fin_num : M \is a fin_num.
Proof.
rewrite ge0_fin_numE//; first exact: sup_int_approxRN_lty.
exact: sup_int_approxRN_ge0.
Qed.

Lemma approxRN_seq_ex : { g : (T -> \bar R)^nat |
  forall k, g k \in approxRN /\ \int[mu]_x g k x > M - k.+1%:R^-1%:E }.
Proof.
pose P m g := g \in approxRN /\ M - m.+1%:R^-1%:E < \int[mu]_x g x.
suff : { g : (T -> \bar R) ^nat & forall m, P m (g m)} by case => g ?; exists g.
apply: (@choice _ _ P) => m.
rewrite /P.
have /(@ub_ereal_sup_adherent _ int_approxRN) : (0 < m.+1%:R^-1 :> R)%R.
  by rewrite invr_gt0.
move/(_ sup_int_approxRN_fin_num) => [_ [h Gh <-]].
by exists h; rewrite inE; split => //; rewrite -/M in q.
Qed.

Definition approxRN_seq : (T -> \bar R)^nat := sval approxRN_seq_ex.

Let g_ := approxRN_seq.

Lemma approxRN_seq_prop : forall m,
  g_ m \in approxRN /\ \int[mu]_x (g_ m x) > M - m.+1%:R^-1%:E.
Proof. exact: (projT2 approxRN_seq_ex). Qed.

Lemma approxRN_seq_ge0 x n : 0 <= g_ n x.
Proof. by have [+ _]:= approxRN_seq_prop n; rewrite inE /= => -[]. Qed.

Lemma measurable_approxRN_seq n : measurable_fun setT (g_ n).
Proof. by have := approxRN_seq_prop n; rewrite inE =>-[[_ /integrableP[]]]. Qed.

Definition max_approxRN_seq n x := \big[maxe/-oo]_(j < n.+1) g_ j x.

Let F_ := max_approxRN_seq.

Lemma measurable_max_approxRN_seq n : measurable_fun [set: T] (F_ n).
Proof.
elim: n => [|n ih].
  rewrite /F_ /max_approxRN_seq.
  under eq_fun do rewrite big_ord_recr/=; rewrite -/(measurable_fun _ _).
  under eq_fun do rewrite big_ord0; rewrite -/(measurable_fun _ _).
  under eq_fun do rewrite maxNye; rewrite -/(measurable_fun _ _).
  have [+ _] := approxRN_seq_prop 0%N.
  by rewrite inE /= => -[]// _ _ _; exact: measurable_approxRN_seq.
rewrite /F_ /max_approxRN_seq => m.
under eq_fun do rewrite big_ord_recr.
by apply: measurable_maxe => //; exact: measurable_approxRN_seq.
Qed.

Lemma max_approxRN_seq_ge0 n x : 0 <= F_ n x.
Proof.
by apply/bigmax_geP; right => /=; exists ord0 => //; exact: approxRN_seq_ge0.
Qed.

Lemma max_approxRN_seq_ge n x : F_ n x >= g_ n x.
Proof. by apply/bigmax_geP; right => /=; exists ord_max. Qed.

Lemma max_approxRN_seq_nd x : nondecreasing_seq (F_ ^~ x).
Proof. by move=> a b ab; rewrite (le_bigmax_ord xpredT (g_ ^~ x)). Qed.

Lemma is_cvg_max_approxRN_seq n : cvg (F_ ^~ n).
Proof. by apply: ereal_nondecreasing_is_cvg; exact: max_approxRN_seq_nd. Qed.

Lemma is_cvg_int_max_approxRN_seq A :
  measurable A -> cvg (fun n => \int[mu]_(x in A) F_ n x).
Proof.
move=> mA; apply: ereal_nondecreasing_is_cvg => a b ab.
apply: ge0_le_integral => //.
- by move=> ? ?; exact: max_approxRN_seq_ge0.
- by apply: measurable_funS (measurable_max_approxRN_seq a).
- by move=> ? ?; exact: max_approxRN_seq_ge0.
- exact: measurable_funS (measurable_max_approxRN_seq b).
- by move=> x _; exact: max_approxRN_seq_nd.
Qed.

Definition is_max_approxRN m j :=
  [set x | F_ m x = g_ j x /\ forall k, (k < j)%N -> g_ k x < g_ j x].

Let E := is_max_approxRN.

Lemma is_max_approxRNE m j : E m j = [set x| F_ m x = g_ j x] `&`
    [set x |forall k, (k < j)%nat -> g_ k x < g_ j x].
Proof. by apply/seteqP; split. Qed.

Lemma trivIset_is_max_approxRN n : trivIset [set: nat] (E n).
Proof.
apply/trivIsetP => /= i j _ _ ij.
apply/seteqP; split => // x []; rewrite /E/= => -[+ + [+ +]].
wlog : i j ij / (i < j)%N.
  move=> h Fmgi iFm Fmgj jFm.
  have := ij; rewrite neq_lt => /orP[ji|ji]; first exact: (h i j).
  by apply: (h j i) => //; rewrite eq_sym.
by move=> {}ij Fmgi h Fmgj  => /(_ _ ij); rewrite -Fmgi -Fmgj ltxx.
Qed.

Lemma bigsetU_is_max_approxRN m : \big[setU/set0]_(j < m.+1) E m j = [set: T].
Proof.
apply/seteqP; split => // x _; rewrite -bigcup_mkord.
pose j := [arg max_(j > @ord0 m) g_ j x]%O.
have j0_proof : exists k, (k < m.+1)%N && (g_ k x == g_ j x).
  by exists j => //; rewrite eqxx andbT.
pose j0 := ex_minn j0_proof.
have j0m : (j0 < m.+1)%N by rewrite /j0; case: ex_minnP => // ? /andP[].
have j0max k : (k < j0)%N -> g_ k x < g_ j0 x.
  rewrite /j0; case: ex_minnP => //= j' /andP[j'm j'j] h kj'.
  rewrite lt_neqAle; apply/andP; split; last first.
    rewrite (eqP j'j) /j; case: arg_maxP => //= i _.
    by move/(_ (Ordinal (ltn_trans kj' j'm))); exact.
  apply/negP => /eqP gkj'.
  have := h k; rewrite -(eqP j'j) -gkj' eqxx andbT (ltn_trans kj' j'm).
  by move=> /(_ erefl); rewrite leqNgt kj'.
exists j0 => //; split.
  rewrite /F_ /max_approxRN_seq (bigmax_eq_arg _ ord0)//; last first.
    by move=> ? _; rewrite leNye.
  rewrite /j0/=; case: ex_minnP => //= j' /andP[j'm /eqP].
  by rewrite /g_ => -> h.
by move=> k kj; exact: j0max.
Qed.

Lemma measurable_is_max_approxRN m j : measurable (E m j).
Proof.
rewrite is_max_approxRNE; apply: measurableI => /=.
  rewrite -[X in measurable X]setTI.
  by apply: emeasurable_fun_eq => //; [exact: measurable_max_approxRN_seq|
                                       exact: measurable_approxRN_seq].
rewrite [T in measurable T](_ : _ = \bigcap_(k in `I_j) [set x | g_ k x < g_ j x])//.
apply: bigcap_measurable => k _.
rewrite -[X in measurable X]setTI; apply: emeasurable_fun_lt => //;
exact: measurable_approxRN_seq.
Qed.

End approxRN_seq.
End approxRN_seq.

Module lim_max_approxRN_seq.
Section lim_max_approxRN_seq.
Context d (T : measurableType d) (R : realType).
Variables mu nu : {finite_measure set T -> \bar R}.

Import approxRN.

Let G := approxRN mu nu.
Let M := sup_int_approxRN mu nu.

Import approxRN_seq.

Let g := approxRN_seq mu nu.
Let F := max_approxRN_seq mu nu.

Definition fRN := fun x => lim (F ^~ x).

Lemma measurable_fun_fRN : measurable_fun [set: T] fRN.
Proof.
rewrite (_ : fRN = fun x => lim_esup (F ^~ x)).
  by apply: measurable_fun_lim_esup => // n; exact: measurable_max_approxRN_seq.
by apply/funext=> n; rewrite is_cvg_lim_esupE//; exact: is_cvg_max_approxRN_seq.
Qed.

Lemma fRN_ge0 x : 0 <= fRN x.
Proof.
apply: lime_ge => //; first exact: is_cvg_max_approxRN_seq.
by apply: nearW => ?; exact: max_approxRN_seq_ge0.
Qed.

Let int_fRN_lim A : measurable A ->
  \int[mu]_(x in A) fRN x = lim (fun n => \int[mu]_(x in A) F n x).
Proof.
move=> mA; rewrite monotone_convergence// => n.
- exact: measurable_funS (measurable_max_approxRN_seq mu nu n).
- by move=> ? ?; exact: max_approxRN_seq_ge0.
- by move=> ?; exact: max_approxRN_seq_nd.
Qed.

Let E m j := is_max_approxRN mu nu m j.

Let int_F_nu m A (mA : measurable A) : \int[mu]_(x in A) F m x <= nu A.
Proof.
rewrite [leLHS](_ : _ = \sum_(j < m.+1) \int[mu]_(x in (A `&` E m j)) F m x);
    last first.
  rewrite -[in LHS](setIT A) -(bigsetU_is_max_approxRN mu nu m) big_distrr/=.
  rewrite (@ge0_integral_bigsetU _ _ _ _ (fun n => A `&` E m n))//.
  - by move=> n; apply: measurableI => //; exact: measurable_is_max_approxRN.
  - by apply: measurable_funTS => //; exact: measurable_max_approxRN_seq.
  - by move=> ? ?; exact: max_approxRN_seq_ge0.
  - apply: trivIset_setIl; apply: (@sub_trivIset _ _ _ setT (E m)) => //.
    exact: trivIset_is_max_approxRN.
rewrite [leLHS](_ : _ = \sum_(j < m.+1) (\int[mu]_(x in (A `&` (E m j))) g j x));
    last first.
  apply: eq_bigr => i _; apply:eq_integral => x; rewrite inE => -[?] [] Fmgi h.
  by apply/eqP; rewrite eq_le; rewrite /F Fmgi lexx.
rewrite [leRHS](_ : _ = \sum_(j < m.+1) (nu (A `&` E m j))); last first.
  rewrite -(@measure_semi_additive _ _ _ nu (fun i => A `&` E m i))//.
  - by rewrite -big_distrr/= bigsetU_is_max_approxRN// setIT.
  - by move=> k; apply: measurableI => //; exact: measurable_is_max_approxRN.
  - by apply: trivIset_setIl => //; exact: trivIset_is_max_approxRN.
  - apply: bigsetU_measurable => /= i _; apply: measurableI => //.
    exact: measurable_is_max_approxRN.
apply: lee_sum => //= i _.
have [+ _] := approxRN_seq_prop mu nu i.
rewrite inE /G/= => -[_ _]; apply.
by apply: measurableI => //; exact: measurable_is_max_approxRN.
Qed.

Let F_G m : F m \in G.
Proof.
rewrite inE /G/=; split => //.
- by move=> ?; exact: max_approxRN_seq_ge0.
- apply/integrableP; split; first exact: measurable_max_approxRN_seq.
  under eq_integral.
    by move=> x _; rewrite gee0_abs; last exact: max_approxRN_seq_ge0; over.
  have /le_lt_trans := int_F_nu m measurableT; apply.
  by apply: fin_num_fun_lty; exact: fin_num_measure.
- by move=> A; exact: int_F_nu.
Qed.

Let M_g_F m : M - m.+1%:R^-1%:E < \int[mu]_x g m x /\
              \int[mu]_x g m x <= \int[mu]_x F m x <= M.
Proof.
split; first by have [] := approxRN_seq_prop mu nu m.
apply/andP; split; last first.
  by apply: ereal_sup_ub; exists (F m)  => //; have := F_G m; rewrite inE.
apply: ge0_le_integral => //.
- by move=> x _; exact: approxRN_seq_ge0.
- exact: measurable_approxRN_seq.
- by move=> ? *; exact: max_approxRN_seq_ge0.
- exact: measurable_max_approxRN_seq.
- by move=> ? _; exact: max_approxRN_seq_ge.
Qed.

Lemma int_fRN_lty : \int[mu]_x `|fRN x| < +oo.
Proof.
rewrite (@le_lt_trans _ _ M)//; last exact: sup_int_approxRN_lty.
under eq_integral.
  by move=> x _; rewrite gee0_abs; last exact: fRN_ge0; over.
rewrite int_fRN_lim// lime_le//; first exact: is_cvg_int_max_approxRN_seq.
by apply: nearW => n; have [_ /andP[_ ]] := M_g_F n.
Qed.

Lemma int_fRN_ub A : measurable A -> \int[mu]_(x in A) fRN x <= nu A.
Proof.
move=> mA; rewrite int_fRN_lim// lime_le //.
  exact: is_cvg_int_max_approxRN_seq.
by apply: nearW => n; exact: int_F_nu.
Qed.

Lemma int_fRNE : \int[mu]_x fRN x = M.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite int_fRN_lim// lime_le//; first exact: is_cvg_int_max_approxRN_seq.
  by apply: nearW => n; have [_ /andP[_]] := M_g_F n.
rewrite int_fRN_lim//.
have cvgM : (fun m => M - m.+1%:R^-1%:E) --> M.
  rewrite -[X in _ --> X]sube0; apply: cvgeB.
  + by rewrite fin_num_adde_defl.
  + exact: cvg_cst.
  + apply/fine_cvgP; split; first exact: nearW.
    rewrite [X in X @ _ --> _](_ : _ = (fun x => x.+1%:R^-1))//.
    apply/gtr0_cvgV0; first exact: nearW.
    apply/cvgrnyP.
    rewrite [X in X @ _](_ : _ = fun n => n + 1)%N; first exact: cvg_addnr.
    by apply/funext => n; rewrite addn1.
apply: (@le_trans _ _ (lim (fun m => M - m.+1%:R^-1%:E))).
  by move/cvg_lim : cvgM => ->.
apply: lee_lim; [by apply/cvg_ex; exists M|exact: is_cvg_int_max_approxRN_seq|].
apply: nearW => m.
by have [/[swap] /andP[? _] /ltW/le_trans] := M_g_F m; exact.
Qed.

Section ab_absurdo.
Context A (mA : measurable A) (h : \int[mu]_(x in A) fRN x < nu A).

Lemma epsRN_ex :
  {eps : {posnum R} | \int[mu]_(x in A) (fRN x + eps%:num%:E) < nu A}.
Proof.
have [muA0|] := eqVneq (mu A) 0.
  exists (PosNum ltr01).
  under eq_integral.
    move=> x _; rewrite -(@gee0_abs _ (_ + _)); last first.
      by rewrite adde_ge0// fRN_ge0.
    over.
  rewrite (@integral_abs_eq0 _ _ _ _ setT)//.
    by rewrite (le_lt_trans _ h)// integral_ge0// => x Ax; exact: fRN_ge0.
  by apply: emeasurable_funD => //; exact: measurable_fun_fRN.
rewrite neq_lt ltNge measure_ge0//= => muA_gt0.
pose mid := ((fine (nu A) - fine (\int[mu]_(x in A) fRN x)) / 2)%R.
pose e := (mid / fine (mu A))%R.
have ? : \int[mu]_(x in A) fRN x \is a fin_num.
  rewrite ge0_fin_numE// ?(lt_le_trans h)// ?leey// integral_ge0//.
  by move=> x Ax; exact: fRN_ge0.
have e_gt0 : (0 < e)%R.
  rewrite /e divr_gt0//; last first.
    by rewrite fine_gt0// muA_gt0/= ltey_eq fin_num_measure.
  by rewrite divr_gt0// subr_gt0// fine_lt// fin_num_measure.
exists (PosNum e_gt0); rewrite ge0_integralD//; last 2 first.
  by move=> x Ax; exact: fRN_ge0.
  exact: measurable_funS measurable_fun_fRN.
rewrite integral_cst// -lte_subr_addr//; last first.
  by rewrite fin_numM// fin_num_measure.
rewrite -[X in _ * X](@fineK _ (mu A)) ?fin_num_measure//.
rewrite -EFinM -mulrA mulVr ?mulr1; last first.
  by rewrite unitfE gt_eqF// fine_gt0// muA_gt0/= ltey_eq fin_num_measure.
rewrite lte_subr_addl// addeC -lte_subr_addl//; last first.
rewrite -(@fineK _ (nu A))// ?fin_num_measure// -[X in _ - X](@fineK _)//.
rewrite -EFinB lte_fin /mid ltr_pdivr_mulr// ltr_pmulr// ?ltr1n// subr_gt0.
by rewrite fine_lt// fin_num_measure.
Qed.

Definition epsRN := sval epsRN_ex.

Definition sigmaRN B := nu B - \int[mu]_(x in B) (fRN x + epsRN%:num%:E).

Let fin_num_int_fRN_eps B : measurable B ->
  \int[mu]_(x in B) (fRN x + epsRN%:num%:E) \is a fin_num.
Proof.
move=> mB; rewrite ge0_integralD//; last 2 first.
  by move=> x Bx; exact: fRN_ge0.
  exact: measurable_funS measurable_fun_fRN.
rewrite fin_numD integral_cst// fin_numM ?fin_num_measure// andbT.
rewrite ge0_fin_numE ?measure_ge0//; last first.
  by apply: integral_ge0 => x Bx; exact: fRN_ge0.
rewrite (le_lt_trans _ int_fRN_lty)//.
under [in leRHS]eq_integral.
  move=> x _; rewrite gee0_abs; last first.
    exact: fRN_ge0.
  over.
apply: subset_integral => //; first exact: measurable_fun_fRN.
by move=> x _; exact: fRN_ge0.
Qed.

Let fin_num_sigmaRN B : measurable B -> sigmaRN B \is a fin_num.
Proof.
move=> mB; rewrite /sigmaRN fin_numB fin_num_measure//=.
exact: fin_num_int_fRN_eps.
Qed.

HB.instance Definition _ :=
  @SigmaFinite_isFinite.Build _ _ _ sigmaRN fin_num_sigmaRN.

Let sigmaRN_semi_additive : semi_additive sigmaRN.
Proof.
move=> H n mH tH mUH.
rewrite /sigmaRN measure_semi_additive// big_split/= fin_num_sumeN; last first.
  by move=> i _; rewrite fin_num_int_fRN_eps.
congr (_ - _); rewrite ge0_integral_bigsetU//.
- rewrite -bigcup_mkord.
  have : measurable_fun setT (fun x => fRN x + epsRN%:num%:E).
    by apply: emeasurable_funD => //; exact: measurable_fun_fRN.
  exact: measurable_funS.
- by move=> x _; rewrite adde_ge0//; exact: fRN_ge0.
- exact: sub_trivIset tH.
Qed.

HB.instance Definition _ :=
  @isAdditiveCharge.Build _ _ _ sigmaRN sigmaRN_semi_additive.

Let sigmaRN_semi_sigma_additive : semi_sigma_additive sigmaRN.
Proof.
move=> H mH tH mUH.
rewrite [X in X --> _](_ : _ = (fun n => \sum_(0 <= i < n) nu (H i) -
  \sum_(0 <= i < n) \int[mu]_(x in H i) (fRN x + epsRN%:num%:E))); last first.
  apply/funext => n; rewrite big_split/= fin_num_sumeN// => i _.
  by rewrite fin_num_int_fRN_eps.
apply: cvgeB.
- by rewrite adde_defC fin_num_adde_defl// fin_num_measure.
- exact: measure_semi_sigma_additive.
- rewrite (ge0_integral_bigcup mH _ _ tH).
  + have /cvg_ex[/= l hl] : cvg (fun x =>
        \sum_(0 <= i < x) \int[mu]_(y in H i) (fRN y + epsRN%:num%:E)).
      apply: is_cvg_ereal_nneg_natsum => n _.
      by apply: integral_ge0 => x _; rewrite adde_ge0//; exact: fRN_ge0.
    by rewrite (@cvg_lim _ _ _ _ _ _ l).
  + apply: integrableD => //=.
    * apply: (integrableS measurableT) => //.
      by apply/integrableP; split; [exact: measurable_fun_fRN|exact: int_fRN_lty].
    * apply/integrableP; split => //.
      by rewrite integral_cst// lte_mul_pinfty// ltey_eq fin_num_measure.
  + by move=> x _; rewrite adde_ge0//; exact: fRN_ge0.
Qed.

HB.instance Definition _ := @isCharge.Build _ _ _ sigmaRN
  sigmaRN_semi_sigma_additive.

End ab_absurdo.

End lim_max_approxRN_seq.
End lim_max_approxRN_seq.

Section radon_nikodym_finite.
Context d (T : measurableType d) (R : realType).
Variables mu nu : {finite_measure set T -> \bar R}.

Import approxRN.

Let G := approxRN mu nu.
Let M := sup_int_approxRN mu nu.

Import lim_max_approxRN_seq.

Let f := fRN mu nu.
Let mf := measurable_fun_fRN.
Let f_ge0 := fRN_ge0.

Lemma radon_nikodym_finite : nu `<< mu -> exists f : T -> \bar R,
  [/\ forall x, f x >= 0, mu.-integrable [set: T] f &
      forall E, measurable E -> nu E = \int[mu]_(x in E) f x].
Proof.
move=> nu_mu; exists f; split.
  - by move=> x; exact: f_ge0.
  - by apply/integrableP; split; [exact: mf|exact: int_fRN_lty].
move=> // A mA.
apply/eqP; rewrite eq_le int_fRN_ub// andbT leNgt; apply/negP => abs.
pose sigma : {charge set T -> \bar R} :=
  [the {charge set T -> \bar R} of sigmaRN mA abs].
have [P [N [[mP posP] [mN negN] PNX PN0]]] := Hahn_decomposition sigma.
pose AP := A `&` P.
have mAP : measurable AP by exact: measurableI.
have muAP_gt0 : 0 < mu AP.
  rewrite lt_neqAle measure_ge0// andbT eq_sym.
  apply/eqP/(@contra_not _ _ (nu_mu _ mAP))/eqP; rewrite gt_eqF//.
  rewrite (@lt_le_trans _ _ (sigma AP))//.
    rewrite (@lt_le_trans _ _ (sigma A))//; last first.
      rewrite (charge_partition _ _ mP mN)// gee_addl//.
      by apply: negN => //; exact: measurableI.
    by rewrite sube_gt0// (proj2_sig (epsRN_ex mA abs)).
  rewrite /sigma/= /sigmaRN lee_subel_addl ?fin_num_measure//.
  by rewrite lee_paddl// integral_ge0// => x _; rewrite adde_ge0//; exact: f_ge0.
pose h x := if x \in AP then f x + (epsRN mA abs)%:num%:E else f x.
have mh : measurable_fun setT h.
  apply: measurable_fun_if => //.
  - by apply: (measurable_fun_bool true); rewrite preimage_mem_true.
  - by apply: measurable_funTS; apply: emeasurable_funD => //; exact: mf.
  - by apply: measurable_funTS; exact: mf.
have hge0 x : 0 <= h x.
  by rewrite /h; case: ifPn => [_|?]; [rewrite adde_ge0// f_ge0|exact: f_ge0].
have hnuP S : measurable S -> S `<=` AP -> \int[mu]_(x in S) h x <= nu S.
  move=> mS SAP.
  have : 0 <= sigma S.
    by apply: posP => //; apply: (subset_trans SAP); exact: subIsetr.
  rewrite sube_ge0; last by rewrite fin_num_measure// orbT.
  apply: le_trans; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  rewrite -{1}(setIid S) integral_mkcondr; apply/eq_integral => x /[!inE] Sx.
  by rewrite /restrict /h !ifT// inE//; exact: SAP.
have hnuN S : measurable S -> S `<=` ~` AP -> \int[mu]_(x in S) h x <= nu S.
  move=> mS ScAP; rewrite /h; under eq_integral.
    move=> x xS; rewrite ifF; last first.
      by apply/negbTE; rewrite notin_set; apply: ScAP; apply: set_mem.
    over.
  exact: int_fRN_ub.
have hnu S : measurable S -> \int[mu]_(x in S) h x <= nu S.
  move=> mS.
  rewrite -(setD0 S) -(setDv AP) setDDr.
  have mSIAP : measurable (S `&` AP) by exact: measurableI.
  have mSDAP : measurable (S `\` AP) by exact: measurableD.
  rewrite integral_setU //.
  - rewrite measureU//.
      by apply: lee_add; [exact: hnuN|exact: hnuP].
    by rewrite setDE setIACA setICl setI0.
  - exact: measurable_funTS.
  - by rewrite disj_set2E setDE setIACA setICl setI0.
have int_h_M : \int[mu]_x h x > M.
  have mCAP := measurableC mAP.
  have disj_AP : [disjoint AP & ~` AP] by exact/disj_set2P/setICr.
  rewrite -(setUv AP) integral_setU ?setUv// /h.
  under eq_integral do rewrite ifT//.
  under [X in _ < _ + X]eq_integral.
    by move=> x; rewrite inE /= => xE0p; rewrite memNset//; over.
  rewrite ge0_integralD//; last 2 first.
    - by move=> x _; exact: f_ge0.
    - by apply: measurable_funTS; exact: mf.
  rewrite integral_cst // addeAC -integral_setU//; last 2 first.
    by rewrite setUv//; exact: mf.
    by move=> x _; exact: f_ge0.
  rewrite setUv int_fRNE -lte_subel_addl; last first.
    rewrite ge0_fin_numE// ?sup_int_approxRN_lty//.
      exact: approxRN_seq.sup_int_approxRN_lty.
    exact: sup_int_approxRN_ge0.
  by rewrite /M subee ?mule_gt0// approxRN_seq.sup_int_approxRN_fin_num.
have Gh : G h.
  split=> //; apply/integrableP; split => //.
  under eq_integral do rewrite gee0_abs//.
  by rewrite (le_lt_trans (hnu _ measurableT))// ltey_eq fin_num_measure.
have : \int[mu]_x h x <= M.
  rewrite -(ereal_sup1 (\int[mu]_x h x)).
  rewrite (@le_ereal_sup _ [set \int[mu]_x h x] (int_approxRN mu nu))//.
  by rewrite sub1set inE; exists h.
by rewrite leNgt int_h_M.
Qed.

End radon_nikodym_finite.

Section radon_nikodym.
Context d (T : measurableType d) (R : realType).

Let radon_nikodym_sigma_finite
    (mu : {sigma_finite_measure set T -> \bar R})
    (nu : {finite_measure set T -> \bar R}) :
  nu `<< mu ->
  exists2 f : T -> \bar R, mu.-integrable [set: T] f &
    forall E, E \in measurable -> nu E = integral mu E f.
Proof.
move=> nu_mu.
have [F TF mFAFfin] := sigma_finiteT mu.
have {mFAFfin}[mF Ffin] := all_and2 mFAFfin.
pose E := seqDU F.
have mE k : measurable (E k).
  by apply: measurableD => //; exact: bigsetU_measurable.
have Efin k : mu (E k) < +oo.
  by rewrite (le_lt_trans _ (Ffin k))// le_measure ?inE//; exact: subDsetl.
have bigcupE : \bigcup_i E i = setT by rewrite TF [RHS]seqDU_bigcup_eq.
have tE := @trivIset_seqDU _ F.
pose mu_ j : {finite_measure set T -> \bar R} :=
  [the {finite_measure set _ -> \bar _} of mfrestr (mE j) (Efin j)].
have H1 i : nu (E i) < +oo by rewrite ltey_eq fin_num_measure.
pose nu_ j : {finite_measure set T -> \bar R} :=
  [the {finite_measure set _ -> \bar _} of mfrestr (mE j) (H1 j)].
have nu_mu_ k : nu_ k `<< mu_ k.
  by move=> S mS mu_kS0; apply: nu_mu => //; exact: measurableI.
have [g Hg] := choice (fun j => radon_nikodym_finite (nu_mu_ j)).
have [g_ge0 integrable_g int_gE {Hg}] := all_and3 Hg.
pose f_ j x := if x \in E j then g j x else 0.
have fRN_ge0 k x : 0 <= f_ k x by rewrite /f_; case: ifP.
have mf_ k : measurable_fun setT (f_ k).
  apply: measurable_fun_if => //.
  - by apply: (measurable_fun_bool true); rewrite preimage_mem_true.
  - rewrite preimage_mem_true.
    by apply: measurable_funTS => //; have /integrableP[] := integrable_g k.
have int_f_T k : integrable mu setT (f_ k).
  apply/integrableP; split => //.
  under eq_integral do rewrite gee0_abs//.
  rewrite -(setUv (E k)) integral_setU //; last 3 first.
    - exact: measurableC.
    - by rewrite setUv.
    - exact/disj_set2P/subsets_disjoint.
  rewrite /f_; under eq_integral do rewrite ifT//.
  rewrite (@eq_measure_integral _ _ _ (E k) (mu_ k)); last first.
    by move=> A mA AEj; rewrite /mu_ /= /mfrestr /mrestr setIidl.
  rewrite -int_gE ?inE//.
  under eq_integral.
    move=> x /[!inE] /= Ekx; rewrite ifF; last by rewrite memNset.
    over.
  by rewrite integral0 ?adde0 ltey_eq fin_num_measure.
have int_f_E j S : measurable S -> \int[mu]_(x in S) f_ j x = nu (S `&` E j).
  move=> mS.
  have mSIEj := measurableI _ _ mS (mE j).
  have mSDEj := measurableD mS (mE j).
  rewrite -{1}(setUIDK S (E j)) (integral_setU _ mSIEj mSDEj)//; last 2 first.
    - by rewrite setUIDK; exact: (measurable_funS measurableT).
    - by apply/disj_set2P; rewrite setDE setIACA setICr setI0.
  rewrite /f_ -(eq_integral _ (g j)); last first.
    by move=> x /[!inE] SIEjx; rewrite /f_ ifT// inE; exact: (@subIsetr _ S).
  rewrite (@eq_measure_integral _ _ _ (S `&` E j) (mu_ j)); last first.
    move=> A mA; rewrite subsetI => -[_ ?]; rewrite /mu_ /=.
    by rewrite /mfrestr /mrestr setIidl.
  rewrite -int_gE; last exact: measurableI.
  under eq_integral.
    move=> x; rewrite inE setDE /= => -[_ Ejx].
    rewrite ifF; last by rewrite memNset.
    over.
  by rewrite integral0 adde0 /nu_/= /mfrestr /mrestr -setIA setIid.
pose f x : \bar R := \sum_(j <oo) f_ j x.
have int_f_nuT : \int[mu]_x f x = nu setT.
  rewrite integral_nneseries//.
  transitivity (\sum_(n <oo) nu (E n)).
    by apply: eq_eseriesr => i _; rewrite int_f_E// setTI.
  rewrite -bigcupE measure_bigcup//.
  by apply: eq_eseriesl => // x; rewrite in_setT.
exists f.
  apply/integrableP; split; first exact: ge0_emeasurable_fun_sum.
  under eq_integral do (rewrite gee0_abs; last exact: nneseries_ge0).
  by rewrite int_f_nuT ltey_eq fin_num_measure.
move=> A /[!inE] mA; rewrite integral_nneseries//; last first.
  by move=> n; exact: measurable_funTS.
rewrite nneseries_esum; last by move=> m _; rewrite integral_ge0.
under eq_esum do rewrite int_f_E//.
rewrite -nneseries_esum; last first.
  by move=> n; rewrite measure_ge0//; exact: measurableI.
rewrite (@eq_eseriesl _ _ (fun x => x \in [set: nat])); last first.
  by move=> x; rewrite in_setT.
rewrite -measure_bigcup//.
- by rewrite -setI_bigcupr bigcupE setIT.
- by move=> i _; exact: measurableI.
- exact: trivIset_setIl.
Qed.

Let Radon_Nikodym0
  (mu : {sigma_finite_measure set T -> \bar R}) (nu : {charge set T -> \bar R}) :
  nu `<< mu ->
  exists2 f : T -> \bar R, mu.-integrable [set: T] f &
    forall A, measurable A -> nu A = \int[mu]_(x in A) f x.
Proof.
move=> nu_mu; have [P [N nuPN]] := Hahn_decomposition nu.
have [fp intfp fpE] := @radon_nikodym_sigma_finite mu
  [the {finite_measure set _ -> \bar _} of jordan_pos nuPN]
  (jordan_pos_dominates nuPN nu_mu).
have [fn intfn fnE] := @radon_nikodym_sigma_finite mu
  [the {finite_measure set _ -> \bar _} of jordan_neg nuPN]
  (jordan_neg_dominates nuPN nu_mu).
exists (fp \- fn); first exact: integrableB.
move=> E mE; rewrite [LHS](jordan_decomp nuPN mE)// integralB//.
- by rewrite -fpE ?inE// -fnE ?inE.
- exact: (integrableS measurableT).
- exact: (integrableS measurableT).
Qed.

Definition Radon_Nikodym
    (mu : {sigma_finite_measure set T -> \bar R})
    (nu : {charge set T -> \bar R}) : T -> \bar R :=
  match pselect (nu `<< mu) with
  | left nu_mu => sval (cid2 (Radon_Nikodym0 nu_mu))
  | right _ => cst -oo
  end.

Local Notation "'d nu '/d mu" := (Radon_Nikodym mu nu).

Theorem Radon_Nikodym_integrable
    (mu : {sigma_finite_measure set T -> \bar R})
    (nu : {charge set T -> \bar R}) :
    nu `<< mu ->
  mu.-integrable [set: T] ('d nu '/d mu).
Proof.
move=> numu; rewrite /Radon_Nikodym; case: pselect => // {}numu.
by case: cid2.
Qed.

Theorem Radon_Nikodym_integral
    (mu : {sigma_finite_measure set T -> \bar R})
    (nu : {charge set T -> \bar R}) :
    nu `<< mu ->
  forall A, measurable A -> nu A = \int[mu]_(x in A) ('d nu '/d mu) x.
Proof.
move=> numu; rewrite /Radon_Nikodym; case: pselect => // {}numu.
by case: cid2.
Qed.

End radon_nikodym.
Notation "'d nu '/d mu" := (Radon_Nikodym mu nu) : charge_scope.
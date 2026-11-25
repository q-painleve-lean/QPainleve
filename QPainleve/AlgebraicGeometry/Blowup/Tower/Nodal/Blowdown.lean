/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.ExceptionalPrime
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Subdivision
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.SmoothProjective

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.NodalContraction
import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Numbering
import QPainleve.AlgebraicGeometry.Blowup.Tower.Isometry.PointBlowdown
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension

/-!
# Transporting nodal boundary contractions

Matching the boundary prime classes of two anticanonical pairs allows one to
contract the same exceptional component in either pair. The contraction is a
blowup at a closed node of the descended boundary, and the ordered branches of
that boundary are obtained from the oriented subdivision. This is the local
step for varying the internal centers of a toric presentation while retaining
its prescribed nodal contractions.

The contraction uses Castelnuovo's criterion in
[Stacks Project, Lemma 54.16.9(1)](https://stacks.math.columbia.edu/tag/0C2N).
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry Chow LineBundleClass
open Scheme Scheme.IdealSheafData

universe u v

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] [IsAlgClosed k] [NeZero (2 : k)]

local notation "S(" k ")" => Spec (CommRingCat.of k)
local notation "g(" k ", " X ")" => (X ↘ S(k))
local notation "K(" k ", " X ")" => LineBundleClass.mk (canonicalBundle k X 2)
local notation "I(" p ")" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ p)
local notation "J(" Y ", " p ")" => vanishingIdeal (X := Y)
  (Closeds.mk (closure {p}) isClosed_closure)
local notation "P(" D ", " a ")" => Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D a))
local notation "C(" a ")" => vanishingIdeal (Closeds.mk (closure {Subtype.val a}) isClosed_closure)

variable {X Z : Scheme.{u}} [X.Over S(k)] [Z.Over S(k)]
  [X.IsProjectiveOver k] [Z.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 g(k, X)] [SmoothOfRelativeDimension 2 g(k, Z)]
  [Scheme.IsRationalOver g(k, X)] [Scheme.IsRationalOver g(k, Z)]
  {D : X.IdealSheafData} {F : Z.IdealSheafData}

omit [Z.IsProjectiveOver k] [Scheme.IsRationalOver g(k, Z)] in
private theorem isNodeOfReducedBoundary_map_of_exceptional_support
    {Y : Scheme.{u}} [Y.Over S(k)] [Y.IsProjectiveOver k] [IsIntegral Y]
    [SmoothOfRelativeDimension 2 g(k, Y)] {f : Z ⟶ Y} [f.IsOver S(k)]
    (hF : F.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ g(k, Z)))
    (hcan : LineBundleClass.mk hF.toInvertibleSheaf = K(k, Z))
    {p : Y} (hp : IsClosed ({p} : Set Y)) (a : Z ≅ (J(Y, p)).blowup)
    (ha : a.hom ≫ (J(Y, p)).blowupToBase = f) (hs : ((J(Y, p)).comap f).support ≤ F.support) :
    (F.map f).IsNodeOfReducedBoundary g(k, Y) p := by
  let : Smooth g(k, Y) := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian Y := isNoetherian_of_finiteType g(k, Y)
  let I := J(Y, p)
  let π := I.blowupToBase
  let : I.blowup.Over S(k) := ⟨π ≫ g(k, Y)⟩
  let : SmoothOfRelativeDimension 2 (I.blowup ↘ S(k)) :=
    smoothOfRelativeDimension_blowup_closed_point g(k, Y) hp
  have hπ : a.inv ≫ f = π := by rw [← ha, Iso.inv_hom_id_assoc]
  have hover : a.inv ≫ g(k, Z) = π ≫ g(k, Y) := by
    rw [← comp_over f S(k), ← Category.assoc, hπ]
  let : a.inv.IsOver S(k) := ⟨hover⟩
  let F' := F.comap a.inv
  let hF' : F'.IsEffectiveCartier := hF.comap a.inv
  obtain ⟨d, hd⟩ := F.exists_iso_of_comap_eq_ker a.symm F'.subschemeι F'.ker_subschemeι.symm
  simp only [Iso.symm_hom] at hd
  have hN' := hN.comp_of_etale d.hom
  rw [← Category.assoc, hd, Category.assoc, hover] at hN'
  have hcan' : LineBundleClass.mk hF'.toInvertibleSheaf = K(k, I.blowup) := by
    rw [← hF.pullback_mk_toInvertibleSheaf hF', hcan, pullback_mk, mk_pullback_canonicalBundle]
  have hs' : (I.comap π).support ≤ F'.support := by
    rw [← hπ, comap_comp, support_comap (I.comap f), support_comap F]
    have h : ((I.comap f).support : Set Z) ⊆ F.support := SetLike.coe_subset_coe.mpr hs
    exact SetLike.coe_subset_coe.mp (Set.preimage_mono (f := a.inv) h)
  obtain ⟨_, _, _, _, hnode⟩ :=
    hF'.anticanonical_nodal_boundary_point_blowdown k hp hN' hcan'
  have hmap : F'.map π = F.map f := by
    have hcomap := congrArg (fun J : Z.IdealSheafData ↦ J.comap a.inv)
      (F.comap_map_of_isOpenImmersion a.hom)
    rw [← comap_comp, Iso.inv_hom_id, comap_id] at hcomap
    dsimp only [F']
    rw [← hcomap, ← map_comp, ha]
  exact hmap ▸ hnode.mp hs'

variable [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
  [∀ z : Z, UniqueFactorizationMonoid (Z.presheaf.stalk z)]

omit [NeZero (2 : k)] in
private theorem isExceptionalCurveOfFirstKind_of_boundaryPrime_match
    (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier)
    [IsReduced D.subscheme] [IsReduced F.subscheme]
    (hcanD : LineBundleClass.mk hD.toInvertibleSheaf = K(k, X))
    (hcanF : LineBundleClass.mk hF.toInvertibleSheaf = K(k, Z))
    (e : (intersectionBilinForm k X).IsometryEquiv (intersectionBilinForm k Z))
    (σ : D.boundaryPrimes ≃ F.boundaryPrimes) (hσ : ∀ q, e P(D, q) = P(F, σ q))
    {p : D.boundaryPrimes} (hp : (C(p)).IsExceptionalCurveOfFirstKind) :
    (C(σ p)).IsExceptionalCurveOfFirstKind := by
  have hanti := hD.map_ofMul_inv_toInvertibleSheaf_of_boundaryPrimes hF e.toLinearMap.toAddMonoidHom
    σ hσ
  rw [hcanD, hcanF] at hanti
  have hK : e (Additive.ofMul K(k, X)) = Additive.ofMul K(k, Z) := by
    simpa only [ofMul_inv, map_neg, neg_inj, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
      LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv] using hanti
  obtain ⟨hsq, hdegree⟩ :=
    (isExceptionalCurveOfFirstKind_vanishingIdeal_iff k (D.boundaryPrimeEmbedding p)).mp
      (by simpa only [coe_boundaryPrimeEmbedding] using hp)
  rw [← coe_boundaryPrimeEmbedding F (σ p)]
  apply (isExceptionalCurveOfFirstKind_vanishingIdeal_iff k (F.boundaryPrimeEmbedding (σ p))).mpr
  refine ⟨?_, ?_⟩
  · simpa only [hσ, intersectionBilinForm_apply, toMul_ofMul, hsq] using
      e.map_app P(D, p) P(D, p)
  · simpa only [hσ, hK, intersectionBilinForm_apply, toMul_ofMul, hdegree] using
      e.map_app (Additive.ofMul K(k, X)) P(D, p)

private theorem pullback_blowupExceptionalClass_eq_boundaryPrime
    {Y : Scheme.{u}} {p : Y} {f : Z ⟶ Y} (a : Z ≅ (I(p)).blowup)
    (ha : a.hom ≫ (I(p)).blowupToBase = f) (q : F.boundaryPrimes)
    (hfiber : (I(p)).comap f = C(q)) :
    pullback a.hom (I(p)).blowupExceptionalClass =
      primeDivisorClass (F.boundaryPrimeEmbedding q) := by
  rw [primeDivisorClass_def]
  have hq := isEffectiveCartier_vanishingIdeal_closure_singleton
    (F.boundaryPrimeEmbedding q).property
  exact (I(p)).pullback_blowupExceptionalClass_of_comap_eq a.hom hq (by
    rw [← comap_comp, ha, hfiber, coe_boundaryPrimeEmbedding])

/-- If a Picard isometry carries the boundary primes of one anticanonical pair
to those of another, a specified point blowdown of a boundary component on the
first surface can be matched by a contraction on the second. The morphism contracts
the matched prime
scheme-theoretically. Its center is a node of the anticanonical image boundary,
and its boundary map is an oriented subdivision of the descended cycle.
The Picard isometry descends uniquely along the two blowdown morphisms. -/
theorem exists_matched_nodal_boundary_blowdown
    (hF : F.IsEffectiveCartier) (hD : D.IsEffectiveCartier)
    [PrestableFamily (F.subscheme ↘ S(k))] [IsReduced D.subscheme]
    (hcanD : LineBundleClass.mk hD.toInvertibleSheaf = K(k, X))
    (hcanF : LineBundleClass.mk hF.toInvertibleSheaf = K(k, Z))
    (e : (intersectionBilinForm k X).IsometryEquiv (intersectionBilinForm k Z))
    (σ : D.boundaryPrimes ≃ F.boundaryPrimes) (hσ : ∀ q, e P(D, q) = P(F, σ q))
    {m : ℕ} [NeZero m] {ι : Type v} {points : ι → (F.subscheme ↘ S(k)).smoothLocus}
    (A : Scheme.NodalCycleNumbering points m)
    {Y₀ : Scheme.{u}} [Y₀.Over S(k)] [Y₀.IsProjectiveOver k] [IsIntegral Y₀]
    [SmoothOfRelativeDimension 2 g(k, Y₀)]
    {f₀ : X ⟶ Y₀} [f₀.IsOver S(k)] {p₀ : Y₀} (hp₀ : IsClosed ({p₀} : Set Y₀))
    (a₀ : X ≅ (I(p₀)).blowup) (ha₀ : a₀.hom ≫ (I(p₀)).blowupToBase = f₀)
    (q : D.boundaryPrimes) (hfiber₀ : (I(p₀)).comap f₀ = C(q)) :
    ∃ (Y : Scheme.{u}) (s : Y ⟶ S(k)) (f : Z ⟶ Y) (p : Y),
      let : Y.Over S(k) := ⟨s⟩
      ∃ (_ : IsIntegral Y) (_ : Y.IsProjectiveOver k) (_ : SmoothOfRelativeDimension 2 g(k, Y)),
        Scheme.IsRationalOver g(k, Y) ∧ f.IsOver S(k) ∧ IsModification f ∧ IsClosed ({p} : Set Y) ∧
        (I(p)).comap f = C(σ q) ∧
        ∃ a : Z ≅ (I(p)).blowup, a.hom ≫ (I(p)).blowupToBase = f ∧
          let E := F.map f
          ∃ (hE : E.IsEffectiveCartier) (_ : PrestableFamily (E.subscheme ↘ S(k))),
            LineBundleClass.mk hE.toInvertibleSheaf = K(k, Y) ∧
            E.comap f = F * C(σ q) ∧ E.IsNodeOfReducedBoundary g(k, Y) p ∧
            ∃ (n : ℕ) (_ : NeZero n), m = n + 1 ∧
              ∃ (B : Scheme.NodalCycleNumbering
                  (PEmpty.elim : PEmpty.{v + 1} → (E.subscheme ↘ S(k)).smoothLocus) n)
                (β : F.subscheme ⟶ E.subscheme),
                β ≫ E.subschemeι = F.subschemeι ≫ f ∧ β.IsOrientedCycleSubdivision A B ∧
                ∃! e₀ : (intersectionBilinForm k Y₀).IsometryEquiv (intersectionBilinForm k Y),
                  ∀ x : Additive (LineBundleClass Y₀),
                    e (Additive.ofMul (pullback f₀ x.toMul)) =
                      Additive.ofMul (pullback f (e₀ x).toMul) := by
  have hN : AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ g(k, Z)) := by
    rw [← F.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  let : IsReduced F.subscheme := hN.isReduced
  let : Smooth g(k, Y₀) := SmoothOfRelativeDimension.smooth 2 _
  let : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian g(k, Y₀)
  let : IsRegularLocalRing (Y₀.presheaf.stalk p₀) := isRegularLocalRing_stalk_of_smooth g(k, Y₀) p₀
  have hd₀ := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq g(k, Y₀) 2).mp inferInstance).2
    p₀ hp₀
  have hq : (C(q)).IsExceptionalCurveOfFirstKind := by
    rw [← hfiber₀, ← ha₀, comap_comp]
    have hex := isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p₀ hp₀ hd₀
    exact hex.comap_of_isIso a₀.hom
  have hcurve := isExceptionalCurveOfFirstKind_of_boundaryPrime_match hD hF hcanD hcanF e σ hσ hq
  let : Smooth g(k, Z) := SmoothOfRelativeDimension.smooth 2 _
  obtain ⟨Y, s, f, p, hY, hproj, hsm, hf, hmod, hp, -, hfiber, -, a, ha⟩ :=
    hcurve.exists_smooth_projective_contraction (k := k)
  let : Y.Over S(k) := ⟨s⟩
  let : IsIntegral Y := hY
  let : Y.IsProjectiveOver k := hproj
  let : SmoothOfRelativeDimension 2 g(k, Y) := hsm
  let : f.IsOver S(k) := hf
  let : IsModification f := hmod
  obtain ⟨bir, hbir⟩ := IsModification.birationalOver f
  have hft : f ≫ g(k, Y) = g(k, Z) := comp_over f _
  have hBir : BirationalOver g(k, Z) g(k, Y) := ⟨bir, by
    simpa only [Category.assoc, Category.comp_id, hft] using congrArg (· ≫ g(k, Y)) hbir⟩
  have hRat := hBir.symm.isRationalOver g(k, Y) g(k, Z)
  have hs : ((I(p)).comap f).support ≤ F.support := by
    rw [← SetLike.coe_subset_coe, hfiber, coe_support_vanishingIdeal]
    exact
      (closure_minimal (Set.singleton_subset_iff.mpr (mem_boundaryPrimes.mp (σ q).property).1)
        F.support.isClosed)
  obtain ⟨hE, hpre, hcan, htotal, n, hn, hlen, B, β, hβ, hsub⟩ :=
    hF.exists_numbering_of_exceptional_boundary_contraction A hcanF hp a ha hs
  refine ⟨Y, s, f, p, hY, hproj, hsm, hRat, hf, hmod, hp, hfiber, a, ha,
    hE, hpre, hcan, hfiber ▸ htotal, ?_, n, hn, hlen, B, β, hβ, hsub, ?_⟩
  · have hI : I(p) = J(Y, p) := Y.ker_fromSpecResidueField_eq_vanishingIdeal p
    let a' := a ≪≫ blowupIso (Iso.refl Y) (hI.trans (comap_id _).symm)
    have ha' : a'.hom ≫ (J(Y, p)).blowupToBase = f := by
      simp only [a', Iso.trans_hom, Category.assoc, blowupIso_hom_blowupToBase,
        Iso.refl_hom, Category.comp_id, ha]
    exact isNodeOfReducedBoundary_map_of_exceptional_support hF hN hcanF hp a' ha' (hI ▸ hs)
  · refine existsUnique_picardIsometry_of_pointBlowdowns hp₀ hp a₀ a ha₀ ha e ?_
    rw [pullback_blowupExceptionalClass_eq_boundaryPrime a₀ ha₀ q hfiber₀,
      pullback_blowupExceptionalClass_eq_boundaryPrime a ha (σ q) hfiber]
    exact hσ q

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

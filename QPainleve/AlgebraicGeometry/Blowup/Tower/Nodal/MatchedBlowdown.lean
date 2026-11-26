/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Subdivision
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Tower.Isometry.PointBlowdown
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.PrescribedBlowdown
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.ExceptionalCurve
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

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
local notation "P(" D ", " a ")" => Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D a))
local notation "C(" a ")" => vanishingIdeal (Closeds.mk (closure {Subtype.val a}) isClosed_closure)

variable {X Z : Scheme.{u}} [X.Over S(k)] [Z.Over S(k)]
  [X.IsProjectiveOver k] [Z.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 g(k, X)] [SmoothOfRelativeDimension 2 g(k, Z)]
  [Scheme.IsRationalOver g(k, X)] [Scheme.IsRationalOver g(k, Z)]
  {D : X.IdealSheafData} {F : Z.IdealSheafData}

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
  have htestD := isExceptionalCurveOfFirstKind_iff_primeDivisorClass k (D.boundaryPrimeEmbedding p)
  have htestF :=
    isExceptionalCurveOfFirstKind_iff_primeDivisorClass k (F.boundaryPrimeEmbedding (σ p))
  dsimp only at htestD htestF
  obtain ⟨hsq, hdegree⟩ := htestD.mp (by simpa only [coe_boundaryPrimeEmbedding] using hp)
  rw [← coe_boundaryPrimeEmbedding F (σ p)]
  refine htestF.mpr ⟨?_, ?_⟩
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
the matched prime scheme-theoretically. Its center is a node of the anticanonical image boundary,
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
  let : IsReduced F.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := F.subscheme ↘ S(k))).isReduced
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
  obtain ⟨Y, s, f, p, hY, hproj, hsm, hRat, hf, hmod, hp, hfiber, a, ha,
    hE, hpre, hcan, hnode, htotal, _, n, hn, hlen, B, β, hβ, hsub⟩ :=
    A.exists_numbered_nodal_boundary_blowdown hF hcanF (σ q) hcurve
  let : Y.Over S(k) := ⟨s⟩
  let : IsIntegral Y := hY
  let : Y.IsProjectiveOver k := hproj
  let : SmoothOfRelativeDimension 2 g(k, Y) := hsm
  let : f.IsOver S(k) := hf
  refine ⟨Y, s, f, p, hY, hproj, hsm, hRat, hf, hmod, hp, hfiber, a, ha,
    hE, hpre, hcan, htotal, hnode, n, hn, hlen, B, β, hβ, hsub, ?_⟩
  refine existsUnique_picardIsometry_of_pointBlowdowns hp₀ hp a₀ a ha₀ ha e ?_
  rw [pullback_blowupExceptionalClass_eq_boundaryPrime a₀ ha₀ q hfiber₀,
    pullback_blowupExceptionalClass_eq_boundaryPrime a ha (σ q) hfiber]
  exact hσ q

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

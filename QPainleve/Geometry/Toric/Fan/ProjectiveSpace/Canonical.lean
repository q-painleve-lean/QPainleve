/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Boundary

import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Integral
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Canonical
import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.AlgebraicGeometry.IdealSheaf.Product
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The anticanonical boundary of the toric projective plane

The coordinate hyperplanes contribute one copy each of the first twisting class.
Their reduced union pulls back to the boundary of the projective-space fan.
-/

public section

open AlgebraicGeometry CategoryTheory Module TopologicalSpace
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
  [Nonempty (projectiveSpace b hi).cones]

local notation "S" => Spec (CommRingCat.of k)
local notation "𝒫" => MvPolynomial.homogeneousSubmodule (Fin 3) k
local notation "P" => Proj 𝒫
local notation "Φ" => projectiveSpace b hi
local notation "X" => Fan.finiteFanScheme k Φ
local notation "D" => Fan.toricBoundaryIdeal k Φ inferInstance
local notation "K" => LineBundleClass.mk (QPainleve.canonicalBundle k P 2)
local notation "H" => Proj.coordinateHyperplaneIdeal (k := k) (n := 2)
local notation "hH" => Proj.isEffectiveCartier_coordinateHyperplaneIdeal (k := k) (n := 2)

local instance (j : Fin 3) : IsIntegral (H j).subscheme :=
  Proj.isIntegral_subscheme_coordinateHyperplaneIdeal (k := k) j

private theorem coordinateHyperplane_genericPoint_injective :
    Function.Injective (fun j : Fin 3 ↦ (H j).subschemeι (genericPoint (H j).subscheme)) := by
  intro j l h
  dsimp only at h
  classical
  by_contra hne
  have he : H j = H l := by
    rw [← (H j).vanishingIdeal_closure_subschemeι_genericPoint,
      ← (H l).vanishingIdeal_closure_subschemeι_genericPoint, h]
  have hp := Proj.isEffectiveCartier_comap_coordinateHyperplaneIdeal (k := k) hne
  rw [he] at hp
  have hz : (H l).comap (H l).subschemeι = ⊥ := by
    exact (congrArg (fun I ↦ I.comap (H l).subschemeι) (H l).ker_subschemeι).symm.trans
      (H l).subschemeι.comap_ker_self
  rw [hz] at hp
  exact hp.stalkIdeal_ne_bot (genericPoint (H l).subscheme) (stalkIdeal_bot _)

/-- The ideal sheaf of the reduced toric boundary on the projective plane
represents the canonical class. -/
theorem mk_toInvertibleSheaf_boundaryIdeal_projectivePlane
    [SmoothOfRelativeDimension 2 (X ↘ S)] (hD : (D).IsEffectiveCartier) :
    LineBundleClass.mk hD.toInvertibleSheaf =
      LineBundleClass.mk (QPainleve.canonicalBundle k X 2) := by
  classical
  let e := projectivePlaneIso k b hi
  let J : (P).IdealSheafData := (∏ j : Fin 3, H j).radical
  have hDe : J.comap e.hom = D := projectivePlaneIso_comap_coordinateTriangle k b hi inferInstance
  have hDe' : (D).comap e.inv = J := by rw [← hDe, ← comap_comp, e.inv_hom_id, comap_id]
  let hJ : J.IsEffectiveCartier := hDe' ▸ hD.comap e.inv
  let : (P).Over S := ⟨Proj.toSpecCoeff 𝒫⟩
  let : e.hom.IsOver S := ⟨by
    -- The polynomial Proj structure map is the coefficient morphism.
    change e.hom ≫ Proj.toSpecCoeff 𝒫 = _
    rw [projectivePlaneIso_hom_toSpecCoeff k, finiteFanScheme_over k]⟩
  have : SmoothOfRelativeDimension 2 (P ↘ S) :=
    Proj.smoothOfRelativeDimension_polynomial k
  have : QuasiCompact (P ↘ S) := Proj.quasiCompact_toSpecCoeff 𝒫
  have : Smooth (P ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral P := Proj.isIntegral_polynomialProj
  have : IsNoetherian P := isNoetherian_of_finiteType (P ↘ S)
  have := (P ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let p : Fin 3 ↪ CodimensionOnePoint P :=
    ⟨fun j ↦ ⟨(H j).subschemeι (genericPoint (H j).subscheme),
      (hH j).coheight_subschemeι_genericPoint⟩,
      fun _ _ he ↦ coordinateHyperplane_genericPoint_injective k (congrArg Subtype.val he)⟩
  have hs (x : CodimensionOnePoint P) : (x : P) ∈ J.support ↔ x ∈ Set.range p := by
    dsimp only [J]
    rw [support_radical, ← SetLike.mem_coe, coe_support_prod, Set.mem_iUnion, Set.mem_range]
    exact exists_congr fun j ↦
      ((hH j).mem_support_iff_eq_subschemeι_genericPoint x.property).trans
        ⟨fun h ↦ Subtype.ext h.symm, fun h ↦ (congrArg Subtype.val h).symm⟩
  have heq (j : Fin 3) :
      primeDivisorClass (p j) = LineBundleClass.mk (Proj.polynomialTwistingBundle 1) := by
    rw [primeDivisorClass_def, mk_toInvertibleSheaf_congr _ (hH j)
      ((H j).vanishingIdeal_closure_subschemeι_genericPoint)]
    simpa only [inv_mk] using Proj.mk_dual_coordinateHyperplaneIdeal (k := k) j
  have hcan : K = LineBundleClass.mk (Proj.polynomialTwistingBundle (-3)) := by
    apply mk_eq_mk_iff.mpr
    rw [QPainleve.canonicalBundle_obj, differentialForms_def,
      Proj.polynomialTwistingBundle_obj]
    exact ⟨Proj.differentialFormsTwoIsoTwistingSheaf k⟩
  have hJcan : LineBundleClass.mk hJ.toInvertibleSheaf = K := by
    have hJ' : vanishingIdeal J.support = J := by
      dsimp only [J]
      rw [support_radical, vanishingIdeal_support]
    have : IsReduced J.subscheme := hJ' ▸
      (inferInstance : IsReduced (vanishingIdeal J.support).subscheme)
    have hh := hJ.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass p hs
    simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hh
    rw [← inv_inj, ← Additive.ofMul.injective.eq_iff, hh,
      hcan, Proj.mk_polynomialTwistingBundle_eq_zpow (-3),
      ← zpow_neg, neg_neg, ofMul_zpow]
    rfl
  rw [← mk_pullback_canonicalBundle k e.hom 2, ← pullback_mk, ← hJcan]
  exact (mk_toInvertibleSheaf_congr (hDe.symm ▸ hD) hD hDe).symm.trans
    (hJ.pullback_mk_toInvertibleSheaf (hDe.symm ▸ hD)).symm

end TauCeti.Toric.Fan

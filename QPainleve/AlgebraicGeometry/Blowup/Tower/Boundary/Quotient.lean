/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.CartierDivisor.Excision
import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# The boundary quotient of a nodal blowup tower

Every center lies in the reduced total transform of the boundary at its stage. The
projection of the tower therefore identifies the two open complements. Picard
excision identifies each boundary quotient with the Picard group of that complement,
so pullback gives the canonical comparison of the quotients. The prime divisor
classes are indexed by their generic points, including the exceptional boundary
components and the strict transform of a component with a self-node.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

universe u

variable {S K X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
  {D : S.IdealSheafData} {s : S ⟶ K} {π : X ⟶ S}

local notation "U₀" => Closeds.compl (Scheme.IdealSheafData.support
  (Scheme.IdealSheafData.comap D π))
local notation "U₁" => Closeds.compl (Scheme.IdealSheafData.support
  (Scheme.IdealSheafData.comap D (BlowupTower.toBase T ≫ π)))

private theorem boundaryCompl_eq_preimage :
    U₁ = T.toBase ⁻¹ᵁ U₀ := by
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.compl_support_comap]

/-- A nodal boundary tower is an isomorphism over the complement of the boundary. -/
theorem isIso_morphismRestrict_boundaryCompl (hT : IsNodalBoundaryTower D s π T) :
    IsIso (T.toBase ∣_ U₀) := by
  induction hT with
  | nil =>
    rw [toBase_nil]
    infer_instance
  | @snoc _ W R I _ p hp hI hnode ih =>
    have hsupport : (I.support : Set W) = {p} := by
      rw [hI, Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hp.closure_eq]
    have hcenter : (I.support : Set W) ⊆ (D.comap (R.toBase ≫ π)).support := by
      rw [hsupport, Set.singleton_subset_iff]
      exact Scheme.IdealSheafData.mem_support_of_isNodeOfReducedBoundary hnode
    have hstep := I.isIso_blowupToBase_restrict_of_disjoint_support (U := R.toBase ⁻¹ᵁ U₀) (by
        rw [← boundaryCompl_eq_preimage (D := D) (π := π) (T := R)]
        exact disjoint_compl_left.mono_right hcenter)
    rw [toBase_snoc, morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hstep ih

variable [IsIntegral X] [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
  [IsIntegral Y] [IsNoetherian Y] [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

variable {B : X.IdealSheafData} {f : X ⟶ K}

local notation "baseCompl" => Closeds.compl (Scheme.IdealSheafData.support B)
local notation "totalCompl" => Closeds.compl (Scheme.IdealSheafData.support
  (Scheme.IdealSheafData.comap B (BlowupTower.toBase T)))

/-- Pullback along a nodal boundary tower identifies the Picard quotients by the prime
divisors supported in the boundary and in its reduced total transform, respectively. -/
def boundaryQuotientEquiv (hT : IsNodalBoundaryTower B f (𝟙 X) T) :
    (Additive (LineBundleClass X) ⧸ Scheme.Opens.primeDivisorSpanCompl baseCompl) ≃ₗ[ℤ]
      (Additive (LineBundleClass Y) ⧸ Scheme.Opens.primeDivisorSpanCompl totalCompl) := by
  have h := hT.isIso_morphismRestrict_boundaryCompl
  rw [Scheme.IdealSheafData.comap_id] at h
  exact (T.toBase.quotientPrimeDivisorSpanComplEquiv baseCompl).trans
    (Submodule.quotEquivOfEq _ _ (congrArg (Scheme.Opens.primeDivisorSpanCompl (X := Y))
      (B.compl_support_comap T.toBase).symm))

/-- On line bundle representatives, the boundary quotient equivalence is pullback by
the projection of the tower. -/
@[simp]
theorem boundaryQuotientEquiv_mk (hT : IsNodalBoundaryTower B f (𝟙 X) T) (a : LineBundleClass X) :
    hT.boundaryQuotientEquiv (Submodule.Quotient.mk (Additive.ofMul a)) =
      Submodule.Quotient.mk (Additive.ofMul (LineBundleClass.pullback T.toBase a)) := by
  have h := hT.isIso_morphismRestrict_boundaryCompl
  rw [Scheme.IdealSheafData.comap_id] at h
  simp only [boundaryQuotientEquiv, LinearEquiv.trans_apply,
    Scheme.Hom.quotientPrimeDivisorSpanComplEquiv_mk, Submodule.quotEquivOfEq_mk]

end QPainleve.BlowupTower.IsNodalBoundaryTower

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import QPainleve.Geometry.Toric.Fan.Boundary.Center
public import QPainleve.LinearAlgebra.Determinant.Dual

import TauCeti.AlgebraicGeometry.IdealSheaf.Section
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.FunctionField
import QPainleve.Geometry.Toric.Fan.Smooth

/-!
# Ordered internal blowups of a toric surface

An oriented rank-two fan and an ordered list of rays with nonzero center parameters determine
an actual tower of point blowups. Each center is placed on the current strict transform of the
reduced toric boundary. The same ray and parameter can occur repeatedly, giving centers that
are infinitely near. The Picard marking uses full transforms of the exceptional classes.

The models follow Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Definition 1.2. The construction uses `Ray.binomialCenterOnBoundary` and
`QPainleve.BlowupTower.alongBoundary`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- The determinant character of a primitive ray generator takes every integral value. -/
theorem Ray.surjective_detCharacter (ρ : Φ.Ray) (b : Module.Basis (Fin 2) ℤ N) :
    Function.Surjective (b.detDualEquiv ρ.primitiveGenerator).toAddMonoidHom := by
  apply b.surjective_detDualEquiv_of_isPrimitive
  rw [Ray.primitiveGenerator_def]
  exact primitiveGenerator_isPrimitive Φ.lattice (Φ.isToricCone ρ.toCone.property) _

variable [h₀ : Nonempty Φ.cones] (b : Module.Basis (Fin 2) ℤ N)

local notation "boundary" => Φ.boundaryIdeal h₀
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "χ(" ρ ")" => LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator ρ))

/-- The Cartier ideal on the reduced boundary with orbit coordinate `z^v = -c⁻¹`,
where the character `z^v` has exponent `det(v, ·)` for the ray generator `v`. -/
def Ray.internalCenter (ρ : Φ.Ray) (c : ℂˣ) :
    {J : (boundary).subscheme.IdealSheafData // J.IsEffectiveCartier} :=
  ⟨(ρ.binomialCenterOnBoundary rankTwo (m := χ(ρ)) (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c).ker,
    ρ.isEffectiveCartier_ker_binomialCenterOnBoundary rankTwo (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c⟩

@[simp]
theorem Ray.internalCenter_val (ρ : Φ.Ray) (c : ℂˣ) :
    (ρ.internalCenter b c).val =
      (ρ.binomialCenterOnBoundary rankTwo (m := χ(ρ)) (b.detDualEquiv_self _)
        (ρ.surjective_detCharacter b) c).ker := (rfl)

/-- In the original fan scheme, the center ideal is the kernel of the binomial point
in the primitive determinant character. -/
theorem Ray.map_internalCenter_subschemeι (ρ : Φ.Ray) (c : ℂˣ) :
    (ρ.internalCenter b c).val.map (boundary).subschemeι =
      (ρ.binomialCenter rankTwo (m := χ(ρ)) (b.detDualEquiv_self _)
        (ρ.surjective_detCharacter b) c).ker := by
  rw [Ray.internalCenter_val, Scheme.IdealSheafData.map_ker]
  exact congrArg Scheme.Hom.ker (ρ.binomialCenterOnBoundary_comp_subschemeι rankTwo
    (m := χ(ρ)) (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c)

/-- Two ordered inputs give disjoint center supports on any embedded copy of the boundary
exactly when the ray or the parameter differs. In particular the test also applies on a
strict transform after any of the preceding internal blowups. -/
theorem disjoint_support_map_internalCenter_iff {Y : Scheme}
    (j : (boundary).subscheme ⟶ Y) [IsClosedImmersion j] (ρ τ : Φ.Ray) (c d : ℂˣ) :
    Disjoint (((ρ.internalCenter b c).val.map j).support : Set Y)
      (((τ.internalCenter b d).val.map j).support : Set Y) ↔ (ρ, c) ≠ (τ, d) := by
  let pt : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
  let center (ρ : Φ.Ray) (c : ℂˣ) :=
    ρ.binomialCenterOnBoundary rankTwo (m := χ(ρ)) (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c
  have hsupport (ρ : Φ.Ray) (c : ℂˣ) :
      (((ρ.internalCenter b c).val.map j).support : Set Y) = {j (center ρ c pt)} := by
    have : IsClosedImmersion (center ρ c) :=
      ρ.isClosedImmersion_binomialCenterOnBoundary rankTwo (b.detDualEquiv_self _)
        (ρ.surjective_detCharacter b) c
    rw [Ray.internalCenter_val, Scheme.IdealSheafData.map_ker, Scheme.Hom.support_ker,
      (center ρ c ≫ j).isClosedEmbedding.isClosed_range.closure_eq]
    exact Set.range_eq_singleton fun x ↦ congrArg (center ρ c ≫ j) (Subsingleton.elim x pt)
  rw [hsupport, hsupport, Set.disjoint_singleton, j.isClosedEmbedding.injective.ne_iff]
  apply not_congr
  constructor
  · intro h
    let p (ρ : Φ.Ray) (c : ℂˣ) :=
      ρ.binomialCenter rankTwo (m := χ(ρ)) (b.detDualEquiv_self _)
        (ρ.surjective_detCharacter b) c
    have hpc (ρ : Φ.Ray) (c : ℂˣ) : p ρ c pt = (boundary).subschemeι (center ρ c pt) :=
      congrArg (fun f : Spec (.of ℂ) ⟶ Φ.algebraicRealization ↦ f pt)
        (ρ.binomialCenterOnBoundary_comp_subschemeι rankTwo (b.detDualEquiv_self _)
          (ρ.surjective_detCharacter b) c).symm
    have hpt : p ρ c pt = p τ d pt := by rw [hpc, hpc, h]
    have hker : (p ρ c).ker = (p τ d).ker :=
      (p ρ c).ker_eq_ker_fromSpecResidueField.trans
        ((congrArg (fun x ↦ (Φ.algebraicRealization.fromSpecResidueField x).ker) hpt).trans
        (p τ d).ker_eq_ker_fromSpecResidueField.symm)
    have he : p ρ c = p τ d :=
      ((p ρ c).ker_eq_ker_iff_of_comp_eq_id (p τ d)
        (ρ.binomialCenter_comp_structureMap _ _ _ _) (τ.binomialCenter_comp_structureMap _ _ _ _)
        ).mp hker
    have hρ := ρ.eq_of_binomialCenter_eq rankTwo (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c (b.detDualEquiv_self _)
      (τ.surjective_detCharacter b) d he
    subst τ
    exact Prod.ext rfl (ρ.binomialCenter_injective _ _ _ he)
  · intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl

variable {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)

/-- The ordered internal blowups with the indicated boundary rays and parameters.
At each stage the center is the image of the original binomial point in the current boundary. -/
def internalBlowupTower : Σ Y, WithBoundary (boundary).subschemeι n Y :=
  alongBoundary (boundary).subschemeι fun j ↦ (s j).internalCenter b (c j)

/-- The empty list of internal centers leaves the toric model unchanged. -/
@[simp]
theorem internalBlowupTower_zero (s : Fin 0 → Φ.Ray) (c : Fin 0 → ℂˣ) :
    internalBlowupTower b s c = ⟨Φ.algebraicRealization, .nil (boundary).subschemeι⟩ :=
  alongBoundary_zero _ _

/-- The last center is mapped into the model already blown up at the preceding centers. -/
@[simp]
theorem internalBlowupTower_succ (s : Fin (n + 1) → Φ.Ray) (c : Fin (n + 1) → ℂˣ) :
    internalBlowupTower b s c =
      let P := internalBlowupTower b (s ∘ Fin.castSucc) (c ∘ Fin.castSucc)
      let J := (s (Fin.last n)).internalCenter b (c (Fin.last n))
      ⟨_, P.2.snoc J.val J.property⟩ :=
  alongBoundary_succ _ _

/-- All internal centers are reduced closed points of their successive ambient surfaces. -/
theorem isClosedPointTower_internalBlowupTower :
    IsClosedPointTower Φ.algebraicRealization (internalBlowupTower b s c).2.toTower := by
  apply isClosedPointTower_alongBoundary
  intro j
  exact (s j).exists_closedPoint_ker_binomialCenterOnBoundary rankTwo (b.detDualEquiv_self _)
    ((s j).surjective_detCharacter b) (c j)

/-- The Picard group of the model is marked by the original toric classes and the full
transforms of the exceptional classes, with coordinates in the given center order. -/
def internalBlowupPicardMarking (hΦ : Φ.IsRegular) :
    (Pic(Φ.algebraicRealization) × (Fin n → ℤ)) ≃ₗ[ℤ]
      Pic((internalBlowupTower b s c).1) := by
  have : SmoothOfRelativeDimension 2 Φ.algebraicRealizationStructureMap :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  exact (internalBlowupTower b s c).2.toTower.picardMarking
    (isClosedPointTower_internalBlowupTower b s c) Φ.algebraicRealizationStructureMap

/-- The marking pulls back the toric class and adds the indicated total exceptional classes. -/
@[simp]
theorem internalBlowupPicardMarking_apply (hΦ : Φ.IsRegular)
    (a : Pic(Φ.algebraicRealization) × (Fin n → ℤ)) :
    internalBlowupPicardMarking b s c hΦ a = (internalBlowupTower b s c).2.toTower.picardHom a := by
  simp [internalBlowupPicardMarking]

end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Center
public import QPainleve.LinearAlgebra.Determinant.Dual

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.IdealSheaf.Section

/-!
# Internal centers on toric boundaries

An ordered basis of the rank-two lattice determines a primitive determinant character
for each ray. The resulting binomial points define effective Cartier ideals on the
reduced boundary. Their supports in any closed embedding of the boundary are disjoint
exactly when the ray or the parameter differs.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- The determinant character of a primitive ray generator takes every integral value. -/
theorem Ray.surjective_detCharacter (ρ : Φ.Ray) (b : Module.Basis (Fin 2) ℤ N) :
    Function.Surjective (b.detDualEquiv ρ.primitiveGenerator).toAddMonoidHom :=
  b.surjective_detDualEquiv_of_isPrimitive ρ.primitiveGenerator_isPrimitive

variable [h₀ : Nonempty Φ.cones] (b : Module.Basis (Fin 2) ℤ N)

local notation "boundary" => Φ.boundaryIdeal h₀
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

/-- The internal center ideal on a fixed ray determines its parameter. -/
theorem Ray.internalCenter_injective (ρ : Φ.Ray) :
    Function.Injective (fun c : ℂˣ ↦ (ρ.internalCenter b c).val) := by
  intro c d h
  have hker := congrArg (fun J ↦ Scheme.IdealSheafData.map J (boundary).subschemeι) h
  rw [ρ.map_internalCenter_subschemeι, ρ.map_internalCenter_subschemeι] at hker
  let hc := b.detDualEquiv_self ρ.primitiveGenerator
  let hp := ρ.surjective_detCharacter b
  exact ρ.binomialCenter_injective rankTwo hc hp
    (((ρ.binomialCenter rankTwo hc hp c).ker_eq_ker_iff_of_comp_eq_id
      (ρ.binomialCenter rankTwo hc hp d) (ρ.binomialCenter_comp_structureMap _ _ _ _)
      (ρ.binomialCenter_comp_structureMap _ _ _ _)).mp hker)

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

end TauCeti.Toric.Fan

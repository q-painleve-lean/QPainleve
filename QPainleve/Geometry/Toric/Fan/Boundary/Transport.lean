/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Equiv
public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.TorusAction.Center

/-!
# Transport of ordered internal blowups along fan equivalences

A fan equivalence preserving the determinant pairings preserves the orbit coordinate
of every corresponding ray. The binomial center pullback comparison identifies the two
ideals with the same parameter. The ordered lift `BlowupTower.exists_isLift_alongBoundary`
then transports the entire tower and its strict boundary.
Combining transport with center reindexing compares the two orders over `ℂ`.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower

namespace TauCeti.Toric.FanEquiv

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  (e : FanEquiv Φ Ψ) [h₀ : Nonempty Φ.cones] [h₁ : Nonempty Ψ.cones]
  (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
  (hdet : ∀ x y, b'.detDualEquiv (e.latticeEquiv x) (e.latticeEquiv y) = b.detDualEquiv x y)

include hdet in
/-- The ideals of corresponding determinant-coordinate centers have the same parameter
under restriction of the toric isomorphism to the boundary. -/
theorem comap_internalCenter_boundaryIso (ρ : Φ.Ray) (c : ℂˣ) :
    ((e.rayEquiv ρ).internalCenter b' c).val.comap (e.boundaryIso h₀ h₁).hom =
      (ρ.internalCenter b c).val := by
  rw [Fan.Ray.internalCenter_val, Fan.Ray.internalCenter_val]
  apply e.comap_ker_binomialCenterOnBoundary_boundaryIso ρ _ _ _ _ _ _ c
  ext x
  simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    primitiveGenerator_rayEquiv, AddMonoidHom.coe_ofClass] using hdet ρ.primitiveGenerator x

include hdet in
/-- A fan equivalence followed by translation identifies the corresponding center ideals
exactly when the target parameter times the translating character equals the source one. -/
theorem comap_internalCenter_toricIso_eq_iff (ρ : Φ.Ray)
    (χ : Multiplicative (N' →+ ℤ) →* ℂˣ) (c d : ℂˣ) :
    ((e.rayEquiv ρ).internalCenter b' d).val.comap
      ((e.boundaryIso h₀ h₁).hom ≫ (Ψ.boundaryTranslation χ).hom) =
        (ρ.internalCenter b c).val ↔
      d * χ (ofAdd (b'.detDualEquiv (e.rayEquiv ρ).primitiveGenerator).toAddMonoidHom) = c := by
  let a := χ (ofAdd (b'.detDualEquiv (e.rayEquiv ρ).primitiveGenerator).toAddMonoidHom)
  have ht := (e.rayEquiv ρ).comap_internalCenter_boundaryTranslation_hom b' χ (d * a)
  have ha : d * a / a = d := mul_div_cancel_right _ _
  rw [ha] at ht
  rw [Scheme.IdealSheafData.comap_comp, ht, e.comap_internalCenter_boundaryIso b b' hdet]
  exact (ρ.internalCenter_injective b).eq_iff

variable {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)

local notation "P" => Fan.internalBlowupTower b s c
local notation "P'" => Fan.internalBlowupTower b' (e.rayEquiv ∘ s) c

include hdet in
/-- The unique lift of a determinant-preserving fan equivalence through the ordered
internal blowups commutes with the blowup projections and the strict boundary embeddings,
including when centers repeat. -/
theorem existsUnique_isLift_internalBlowupTower :
    ∃! g : (P).1 ≅ (P').1,
      IsLift (asIso e.toFanHom.algebraicMap) (P).2.toTower (P').2.toTower g ∧
        (P).2.boundaryι ≫ g.hom = (e.boundaryIso h₀ h₁).hom ≫ (P').2.boundaryι := by
  let Matches (L : Σ Z, WithBoundary (Φ.boundaryIdeal h₀).subschemeι n Z)
      (R : Σ Z, WithBoundary (Ψ.boundaryIdeal h₁).subschemeι n Z) : Prop :=
    ∃! g : L.1 ≅ R.1, IsLift (asIso e.toFanHom.algebraicMap) L.2.toTower R.2.toTower g ∧
      L.2.boundaryι ≫ g.hom = (e.boundaryIso h₀ h₁).hom ≫ R.2.boundaryι
  suffices Matches (P) (P') from this
  rw [Fan.internalBlowupTower_eq_alongBoundary, Fan.internalBlowupTower_eq_alongBoundary]
  obtain ⟨g, hg, hb⟩ :=
    exists_isLift_alongBoundary (asIso e.toFanHom.algebraicMap) (e.boundaryIso h₀ h₁)
      (e.boundaryIso_hom_subschemeι h₀ h₁).symm
      (fun j ↦ (s j).internalCenter b (c j)) (fun j ↦ (e.rayEquiv (s j)).internalCenter b' (c j))
      (fun j ↦ e.comap_internalCenter_boundaryIso b b' hdet (s j) (c j))
  exact ⟨g, ⟨hg, hb⟩, fun _ h ↦ h.1.unique hg⟩

include hdet in
/-- Transporting the internal blowups after reindexing the centers gives an isomorphism
over the toric schemes that restricts to the fan equivalence on the strict boundaries.
The centers may repeat. -/
theorem exists_iso_reindex_transport_internalBlowupTower
    (σ : Equiv.Perm (Fin n)) :
    let A := Fan.internalBlowupTower b s c
    let B := Fan.internalBlowupTower b' (e.rayEquiv ∘ s ∘ σ) (c ∘ σ)
    ∃ f : A.1 ≅ B.1,
      f.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase ≫ e.toFanHom.algebraicMap ∧
      B.2.boundaryι.ker.comap f.hom = A.2.boundaryι.ker ∧
      A.2.boundaryι ≫ f.hom = (e.boundaryIso h₀ h₁).hom ≫ B.2.boundaryι := by
  dsimp only
  let A := Fan.internalBlowupTower b s c
  let B := Fan.internalBlowupTower b' (e.rayEquiv ∘ s ∘ σ) (c ∘ σ)
  obtain ⟨f, hf, hfB⟩ := Fan.exists_iso_internalBlowupTower_reindex b s c σ
  obtain ⟨f', ⟨hf', hf'B⟩, -⟩ :=
    e.existsUnique_isLift_internalBlowupTower b b' hdet (s ∘ σ) (c ∘ σ)
  have hstrict : A.2.boundaryι ≫ (f ≪≫ f').hom = (e.boundaryIso h₀ h₁).hom ≫ B.2.boundaryι := by
    rw [Iso.trans_hom, ← Category.assoc, hfB, hf'B]
  refine ⟨f ≪≫ f', ?_, ?_, hstrict⟩
  · simpa only [← Category.assoc, hf, asIso_hom, Iso.trans_hom] using
      congrArg (f.hom ≫ ·) hf'.hom_toBase
  · have hk : (A.2.boundaryι ≫ (f ≪≫ f').hom).ker = B.2.boundaryι.ker := by
      rw [hstrict, Scheme.Hom.ker_comp_of_isIso]
    rw [← hk, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]

end TauCeti.Toric.FanEquiv

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.Geometry.Toric.Fan.InternalBlowup

/-!
# Toric presentations of boundary pairs

A nodal blowup tower with a boundary-preserving comparison to an ordered internal
blowup model witnesses toric presentability. This property transports along
isomorphisms over the ground field.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower TauCeti.Toric

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X Y : Scheme} (b : Module.Basis (Fin 2) ℤ N)

local notation "S" => Spec (CommRingCat.of ℂ)

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A pair has a toric presentation if a nodal blowup tower over the pair is
isomorphic over the ground field to an ordered internal blowup model of a regular
complete fan. The isomorphism identifies the reduced total boundary with the
strict toric boundary. The center parameters may repeat. -/
def HasToricPresentation (D : X.IdealSheafData) (s : X ⟶ S)
    (b : Module.Basis (Fin 2) ℤ N) (i : N →+ V) : Prop :=
  ∃ (Φ : Fan i) (_ : Φ.IsRegular) (hc : Φ.IsComplete)
    (m : ℕ) (rays : Fin m → Φ.Ray) (c : Fin m → ℂˣ)
    (n : ℕ) (Y : Scheme) (T : BlowupTower X n Y),
    IsNodalBoundaryTower D s (𝟙 X) T ∧
    let A := Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b rays c
    ∃ e : A.1 ≅ Y,
      e.hom ≫ T.toBase ≫ s = A.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap ∧
      ((D.comap T.toBase).radical).comap e.hom = A.2.boundaryι.ker

/-- The existence of a toric presentation is witnessed by the fan, the ordered
internal centers, the nodal tower, and the boundary-preserving comparison. -/
theorem hasToricPresentation_iff (D : X.IdealSheafData) (s : X ⟶ S)
    (b : Module.Basis (Fin 2) ℤ N) (i : N →+ V) :
    D.HasToricPresentation s b i ↔
      ∃ (Φ : Fan i) (_ : Φ.IsRegular) (hc : Φ.IsComplete)
        (m : ℕ) (rays : Fin m → Φ.Ray) (c : Fin m → ℂˣ)
        (n : ℕ) (Y : Scheme) (T : BlowupTower X n Y),
        IsNodalBoundaryTower D s (𝟙 X) T ∧
        let A := Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b rays c
        ∃ e : A.1 ≅ Y,
          e.hom ≫ T.toBase ≫ s = A.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap ∧
          ((D.comap T.toBase).radical).comap e.hom = A.2.boundaryι.ker :=
  Iff.rfl

variable {b}

/-- A toric presentation transports along an isomorphism over the ground field. -/
theorem HasToricPresentation.of_comap_iso {D : X.IdealSheafData} {s : X ⟶ S} {t : Y ⟶ S}
    {e : X ≅ Y} (h : (D.comap e.inv).HasToricPresentation t b i) (he : e.hom ≫ t = s) :
    D.HasToricPresentation s b i := by
  obtain ⟨Φ, hΦ, hc, m, r, c, n, Z, U, hU, a, ha, hD⟩ := (hasToricPresentation_iff ..).mp h
  obtain ⟨W, T, f, hT, hf, hB⟩ := hU.exists_transport_of_iso he
  have he' : e.inv ≫ s = t := by rw [← he, Iso.inv_hom_id_assoc]
  refine (hasToricPresentation_iff ..).mpr ⟨Φ, hΦ, hc, m, r, c, n, W, T, hT,
    a ≪≫ f.symm, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Iso.symm_hom, hf, Category.assoc, Iso.inv_hom_id_assoc, he']
      using ha
  · simpa only [hB, Iso.trans_hom, Iso.symm_hom, ← comap_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using hD

end AlgebraicGeometry.Scheme.IdealSheafData

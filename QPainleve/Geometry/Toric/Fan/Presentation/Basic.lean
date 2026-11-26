/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.Geometry.Toric.Fan.InternalBlowup

import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Toric presentations of boundary pairs

A toric presentation records a nodal blowup tower and its boundary-preserving
comparison to an ordered internal blowup model. Toric presentability is the
existence of such a presentation and transports along isomorphisms over the ground field.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower TauCeti.Toric

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X Y : Scheme} (b : Module.Basis (Fin 2) ℤ N)

local notation "S" => Spec (CommRingCat.of ℂ)

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A toric presentation of a boundary pair in the frame `b` with `r` ordered internal centers.
The two towers are identified over the ground field, with the reduced total boundary on the
nodal side corresponding to the strict boundary on the toric side. Centers may repeat. -/
structure ToricPresentation (D : X.IdealSheafData) (s : X ⟶ S)
    (b : Module.Basis (Fin 2) ℤ N) (i : N →+ V) (r : ℕ) where
  /-- The fan of the toric model. -/
  fan : Fan i
  regular : fan.IsRegular
  complete : fan.IsComplete
  /-- The boundary ray carrying each ordered internal center. -/
  rays : Fin r → fan.Ray
  /-- The binomial parameter of each center in the frame `b`. -/
  parameters : Fin r → ℂˣ
  /-- The number of nodal blowups. -/
  nodalLength : ℕ
  /-- The surface at the top of the nodal tower. -/
  surface : Scheme
  /-- The blowup tower from the original surface to the nodal model. -/
  tower : BlowupTower X nodalLength surface
  isNodal : IsNodalBoundaryTower D s (𝟙 X) tower
  /-- The isomorphism from the internal model to the nodal model. -/
  iso : (Fan.internalBlowupTower (h₀ := complete.nonempty_cones) b rays parameters).1 ≅ surface
  iso_over :
    let A := Fan.internalBlowupTower (h₀ := complete.nonempty_cones) b rays parameters
    iso.hom ≫ tower.toBase ≫ s = A.2.toTower.toBase ≫ fan.algebraicRealizationStructureMap
  iso_boundary :
    let A := Fan.internalBlowupTower (h₀ := complete.nonempty_cones) b rays parameters
    ((D.comap tower.toBase).radical).comap iso.hom = A.2.boundaryι.ker

/-- The pair admits a toric presentation in the frame `b`. -/
def HasToricPresentation (D : X.IdealSheafData) (s : X ⟶ S)
    (b : Module.Basis (Fin 2) ℤ N) (i : N →+ V) : Prop :=
  ∃ r, Nonempty (D.ToricPresentation s b i r)

/-- Eliminate toric presentability into a presentation with its number of internal centers. -/
theorem hasToricPresentation_iff (D : X.IdealSheafData) (s : X ⟶ S)
    (b : Module.Basis (Fin 2) ℤ N) (i : N →+ V) :
    D.HasToricPresentation s b i ↔ ∃ r, Nonempty (D.ToricPresentation s b i r) :=
  Iff.rfl

/-- A specified toric presentation witnesses toric presentability. -/
theorem ToricPresentation.hasToricPresentation {D : X.IdealSheafData} {s : X ⟶ S}
    {b : Module.Basis (Fin 2) ℤ N} {r : ℕ} (P : D.ToricPresentation s b i r) :
    D.HasToricPresentation s b i :=
  ⟨r, ⟨P⟩⟩

/-- A pair identified over the ground field with a regular complete fan realization
and its toric boundary has a toric presentation with empty blowup towers. -/
theorem hasToricPresentation_of_toric_boundary {D : X.IdealSheafData}
    {s : X ⟶ S} {Φ : Fan i} (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (e : Φ.algebraicRealization ≅ X) (he : e.hom ≫ s = Φ.algebraicRealizationStructureMap)
    (hD : D.comap e.hom = Φ.boundaryIdeal hc.nonempty_cones) :
    D.HasToricPresentation s b i := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  let A := Fan.internalBlowupTower b (Fin.elim0 : Fin 0 → Φ.Ray) Fin.elim0
  suffices ∃ a : A.1 ≅ X, a.hom ≫ s = A.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap ∧
      D.radical.comap a.hom = A.2.boundaryι.ker by
    obtain ⟨a, ha, hB⟩ := this
    exact ToricPresentation.hasToricPresentation
      ⟨Φ, hΦ, hc, Fin.elim0, Fin.elim0, 0, X, .nil, .nil, a, by simpa using ha,
        by simpa only [toBase_nil, comap_id] using hB⟩
  unfold A
  rw [Fan.internalBlowupTower_zero]
  refine ⟨e, by simpa using he, ?_⟩
  simp only [← radical_comap_of_isOpenImmersion, WithBoundary.boundaryι_nil, ker_subschemeι,
    hD, Φ.boundaryIdeal_def]
  exact (isReduced_subscheme_iff_radical_eq _).mp inferInstance

variable {b}

/-- A toric presentation transports along an isomorphism over the ground field. -/
theorem HasToricPresentation.of_comap_iso {D : X.IdealSheafData} {s : X ⟶ S} {t : Y ⟶ S}
    {e : X ≅ Y} (h : (D.comap e.inv).HasToricPresentation t b i) (he : e.hom ≫ t = s) :
    D.HasToricPresentation s b i := by
  obtain ⟨_, ⟨P⟩⟩ := (hasToricPresentation_iff ..).mp h
  obtain ⟨W, T, f, hT, hf, hB⟩ := P.isNodal.exists_transport_of_iso he
  have he' : e.inv ≫ s = t := by rw [← he, Iso.inv_hom_id_assoc]
  refine ToricPresentation.hasToricPresentation
    ⟨P.fan, P.regular, P.complete, P.rays, P.parameters, P.nodalLength, W, T, hT,
      P.iso ≪≫ f.symm, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Iso.symm_hom, hf, Category.assoc, Iso.inv_hom_id_assoc, he']
      using P.iso_over
  · simpa only [hB, Iso.trans_hom, Iso.symm_hom, ← comap_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using P.iso_boundary

end AlgebraicGeometry.Scheme.IdealSheafData

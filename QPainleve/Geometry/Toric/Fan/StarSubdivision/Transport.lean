/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.StarSubdivision.NodalTower

/-!
# Toric realization of a nodal tower over an identified toric pair

When the base pair is identified with a toric surface, its specified nodal tower
is realized by a subdivision over that same base isomorphism. The top comparison
identifies the reduced total boundary.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] {N V : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {X Y : Scheme.{u}} {D : X.IdealSheafData}

local notation "S" => Spec (CommRingCat.of k)

/-- Realize a specified nodal blowup tower over a pair identified with a complete
regular toric surface. Agreement of the boundary supports at the base suffices.
The subdivision morphism agrees with the given projection, and the top
comparison identifies the reduced total boundary ideal. -/
theorem exists_toric_subdivision_of_nodal_boundary_tower_of_iso
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (hN : Module.finrank ℤ N = 2)
    {s : X ⟶ S} {n : ℕ} {T : BlowupTower X n Y}
    (hT : IsNodalBoundaryTower D s (𝟙 X) T)
    (q : Φ.finiteFanScheme k ≅ X) (hq : q.hom ≫ s = Φ.finiteFanSchemeToSpec k)
    (hD : (D.comap q.hom).support = (Φ.toricBoundaryIdeal k hc.nonempty_cones).support) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (hΨ : Ψ.IsComplete) (H : Ψ.IsSubdivision Φ)
      (r : Ψ.finiteFanScheme k ≅ Y),
      r.hom ≫ T.toBase = H.toFanHom.finiteFanSchemeHom k ≫ q.hom ∧
      ((D.comap T.toBase).radical).comap r.hom = Ψ.toricBoundaryIdeal k hΨ.nonempty_cones := by
  have hsupport : D.support = ((Φ.toricBoundaryIdeal k hc.nonempty_cones).comap q.inv).support := by
    rw [support_comap, ← hD, ← support_comap, ← comap_comp, Iso.inv_hom_id, comap_id]
  have hT' : IsNodalBoundaryTower ((Φ.toricBoundaryIdeal k hc.nonempty_cones).comap q.inv)
      s (𝟙 X) T := by
    exact hT.congr rfl (by simpa only [comap_id] using hsupport)
  obtain ⟨W, U, g, hU, hg, hboundary⟩ := hT'.exists_transport_of_iso (k := q) hq
  obtain ⟨Ψ, hreg, H, t, ht, htD, -⟩ :=
    exists_toric_subdivision_of_nodal_boundary_tower k hΦ hc hN hU
  refine ⟨Ψ, hreg, H.isComplete_iff.mpr hc, H, t ≪≫ g, ?_, ?_⟩
  · have h := congrArg (· ≫ q.hom) ((congrArg (t.hom ≫ ·) hg).symm.trans ht)
    simpa only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
  · have htotal : (D.comap T.toBase).radical =
        (((Φ.toricBoundaryIdeal k hc.nonempty_cones).comap q.inv).comap T.toBase).radical := by
      rw [← vanishingIdeal_support, ← vanishingIdeal_support, support_comap, support_comap,
        hsupport]
    rw [Iso.trans_hom, comap_comp, htotal, ← hboundary, htD]

end TauCeti.Toric.Fan

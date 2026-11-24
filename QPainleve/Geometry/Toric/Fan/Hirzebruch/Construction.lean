/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ray

import QPainleve.Geometry.Toric.Fan.Equiv
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Corner
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Hirzebruch
import QPainleve.Geometry.Toric.Fan.StarSubdivision.ProjectivePlane
import QPainleve.Geometry.Toric.Fan.TwoDimensional

/-!
# Hirzebruch fans in a prescribed basis

The Hirzebruch fan of any nonnegative index exists uniquely in a given rank-two
lattice frame. The construction uses the fan of the plane blown up at a torus
fixed point and the toric elementary transformation between successive indices.

See [Vakil, *Complex Algebraic Surfaces*, Class 17, §2][Vakil] for the role of
the Hirzebruch surfaces in the classification of minimal rational surfaces.

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf
-/

public section

open Module

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "i₂" => AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 2)
local notation "b₂" => Pi.basisFun ℤ (Fin 2)

private theorem exists_hirzebruch_fan_in_some_basis (n : ℕ) :
    ∃ (Φ : Fan i₂) (d : Basis (Fin 2) ℤ (Fin 2 → ℤ)),
      Φ.IsRegular ∧ Φ.IsComplete ∧ Set.range (Ray.primitiveGenerator (Phi := Φ)) =
        {d 0, d 1, -d 0, (n : ℤ) • d 0 - d 1} := by
  induction n with
  | zero =>
    -- Mark the other section of the plane blowup to start the link at index -1.
    let hi := isIntegralLattice_intCast 2
    let Ψ := projectiveSpace b₂ hi
    let hΨ := isRegular_projectiveSpace b₂ hi
    let σ := projectiveSpaceMaximalCone b₂ hi none
    let Γ := Ψ.starSubdivisionAlong hΨ σ.property
    obtain ⟨hσ, c, _, hc, -⟩ := exists_blowup_projectivePlane_vertex_hirzebruchOne b₂ hi none
    have hreg : Γ.IsRegular := Ψ.isRegular_starSubdivisionAlong hΨ σ.property
    have hcomp : Γ.IsComplete :=
      (Ψ.starSubdivisionAlong_isSubdivision hΨ σ.property hσ).isComplete_iff.mpr
        (isComplete_projectiveSpace b₂ hi)
    have hc' : Set.range (Ray.primitiveGenerator (Phi := Γ)) =
        {c 0, c 1, -c 0, (1 : ℤ) • c 0 - c 1} := by simpa only [one_zsmul] using hc
    obtain ⟨r, hr⟩ := exists_rayEquiv_of_hirzebruch_ray_generators c 1 hc'
    obtain ⟨d, t, ht, -⟩ := exists_hirzebruch_opposite_section_basis c 1 r hr
    have ht' : Set.range (Ray.primitiveGenerator (Phi := Γ)) =
        {d 0, d 1, -d 0, (-(1 : ℤ)) • d 0 - d 1} := by
      rw [← t.surjective.range_comp, Function.comp_def, ht]
      ext x
      simp [or_comm, or_assoc]
    obtain ⟨Φ, hΦ, _, _, _, _, v, hcomplete, _, _, _, hv, -⟩ :=
      exists_hirzebruch_toric_elementary_transformation d hreg hcomp (-1) ht'
    exact ⟨Φ, v, hΦ, hcomplete, by simpa using hv⟩
  | succ n ih =>
    obtain ⟨Φ, d, hΦ, hcomplete, hd⟩ := ih
    obtain ⟨Ψ, hΨ, _, _, _, _, c, hcomplete', _, _, _, hc, -⟩ :=
      exists_hirzebruch_toric_elementary_transformation d hΦ hcomplete n hd
    exact ⟨Ψ, c, hΨ, hcomplete', by simpa only [Nat.cast_succ] using hc⟩

/-- In a given rank-two lattice basis there is a unique complete regular fan with the
four Hirzebruch rays of index `n`. -/
theorem existsUnique_hirzebruch_fan (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i) (n : ℕ) :
    ∃! Φ : Fan i, Φ.IsRegular ∧ Φ.IsComplete ∧ Set.range (Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, (n : ℤ) • b 0 - b 1} := by
  obtain ⟨Φ, d, hΦ, hc, hr⟩ := exists_hirzebruch_fan_in_some_basis n
  let e := d.equiv b (Equiv.refl (Fin 2))
  let Ψ := Φ.mapEquiv hi e.toAddEquiv
  let f := Φ.mapEquivIso hi e.toAddEquiv
  have hΨ : Ψ.IsRegular := f.isRegular_iff.mpr hΦ
  have hΨc : Ψ.IsComplete := hc.mapEquiv hi e.toAddEquiv
  have hr' : Set.range (Ray.primitiveGenerator (Phi := Ψ)) =
      {b 0, b 1, -b 0, (n : ℤ) • b 0 - b 1} := by
    rw [← f.rayEquiv.surjective.range_comp]
    have hgen : Ray.primitiveGenerator (Phi := Ψ) ∘ f.rayEquiv =
        e ∘ Ray.primitiveGenerator := by
      funext ρ
      simp only [Function.comp_apply, FanEquiv.primitiveGenerator_rayEquiv, f,
        mapEquivIso_latticeEquiv]
      rfl
    rw [hgen, Set.range_comp, hr]
    simp only [Set.image_insert_eq, Set.image_singleton, map_sub, map_neg, map_zsmul,
      e, Basis.equiv_apply, Equiv.refl_apply]
  exact ⟨Ψ, ⟨hΨ, hΨc, hr'⟩, fun Ω hΩ ↦
    Ω.eq_of_range_primitiveGenerator_eq b hΩ.1 hΨ hΩ.2.1 hΨc (hΩ.2.2.trans hr'.symm)⟩

end TauCeti.Toric.Fan

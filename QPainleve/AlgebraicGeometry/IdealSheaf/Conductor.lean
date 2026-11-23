/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Conductor.Basic

/-!
# The conductor on spectra

For a finite map between spectra, the conductor ideal sheaf is the ideal sheaf
associated to the conductor of the corresponding ring map.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The conductor sheaf of a finite morphism of spectra is obtained from the conductor
of the ring map by the usual comparison of affine section rings. -/
theorem conductor_Spec_map {A B : CommRingCat.{u}} (f : A ⟶ B) [IsFinite (Spec.map f)] :
    (Spec.map f).conductor = IdealSheafData.ofIdealTop
      (letI := f.hom.toAlgebra
       (TauCeti.Algebra.conductor A B).map (Scheme.ΓSpecIso A).inv.hom) := by
  let := f.hom.toAlgebra
  let := (Spec.map f).appTop.hom.toAlgebra
  rw [conductor_of_isAffine]
  congr 1
  let eA := (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv
  let eB := (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv
  have hn (a : A) : algebraMap Γ(Spec A, ⊤) Γ(Spec B, ⊤) (eA.symm a) =
      eB.symm (algebraMap A B a) :=
    (congrArg (fun g : A ⟶ Γ(Spec B, ⊤) ↦ g a) (Scheme.ΓSpecIso_inv_naturality f)).symm
  have hmap : (TauCeti.Algebra.conductor A B).map (Scheme.ΓSpecIso A).inv.hom =
      (TauCeti.Algebra.conductor A B).comap eA.toRingHom :=
    Ideal.map_symm eA
  rw [hmap]
  ext r
  rw [Ideal.mem_comap, TauCeti.Algebra.mem_conductor_iff, TauCeti.Algebra.mem_conductor_iff]
  -- Evaluate the comap with the same equivalence as the naturality identity.
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  constructor
  · intro h b
    obtain ⟨c, hc⟩ := h (eB.symm b)
    refine ⟨eA c, eB.symm.injective ?_⟩
    simpa only [map_mul, ← hn, RingEquiv.symm_apply_apply] using hc
  · intro h b
    obtain ⟨c, hc⟩ := h (eB b)
    refine ⟨eA.symm c, ?_⟩
    simpa only [map_mul, ← hn, RingEquiv.symm_apply_apply] using congrArg eB.symm hc

end AlgebraicGeometry.Scheme.Hom

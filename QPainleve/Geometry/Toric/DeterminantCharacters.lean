/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.LinearAlgebra.Determinant.Dual
public import TauCeti.Geometry.Toric.Algebraic.DenseTorus

/-!
# Determinant characters of the rank-two dense torus

An ordered basis of a rank-two lattice identifies the lattice with its dual by sending `h` to
the character `u ↦ det(h, u)`. Composing this identification with Tau Ceti's zero-cone
coordinate-ring equivalence gives the monomial convention on the dense torus. The character
indexed by `h` evaluates on a ray in direction `u` as `det(h, u)`.
-/

public noncomputable section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- In rank two the real determinant character of a nonzero vector vanishes on its line. -/
theorem IsIntegralLattice.ker_realCharacter_detDualEquiv (hi : IsIntegralLattice i)
    (b : Module.Basis (Fin 2) ℤ N) {v : N} (hv : v ≠ 0) :
    (hi.realCharacter (b.detDualEquiv v).toAddMonoidHom).ker = ℝ ∙ i v := by
  let f := hi.realCharacter (b.detDualEquiv v).toAddMonoidHom
  have hf : f ≠ 0 := by
    intro hf
    have hzero : (b.detDualEquiv v).toAddMonoidHom = 0 :=
      hi.realCharacter_injective (hf.trans (map_zero hi.realCharacter).symm)
    exact hv (b.detDualEquiv.map_eq_zero_iff.mp (LinearMap.toAddMonoidHom_injective hzero))
  have := hi.finiteDimensional
  have hdim : Module.finrank ℝ V = 2 := by
    rw [← hi.finrank_eq, Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  dsimp only [f] at hker
  refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
  · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    have hvv := b.det.map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl (by decide)
    simpa [f, IsIntegralLattice.realCharacter_apply, Module.Basis.detDualEquiv_apply] using hvv
  · rw [finrank_span_singleton (fun h ↦ hv (hi.injective (h.trans (map_zero i).symm)))]
    omega

end TauCeti.Toric

namespace QPainleve.Toric

open TauCeti.Toric Multiplicative

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The dense torus coordinate ring in determinant coordinates for the ordered basis `b`. -/
def denseTorusCoordinateRingEquivDet (hi : IsIntegralLattice i) (b : Module.Basis (Fin 2) ℤ N) :
    AddMonoidAlgebra ℂ N ≃ₐ[ℂ] affineCoordinateRing hi (⊥ : PointedCone ℝ V) :=
  let e := b.detDualEquiv.trans (addMonoidHomLequivInt ℤ).symm
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ N).trans <|
    (MonoidAlgebra.domCongr ℂ ℂ e.toAddEquiv.toMultiplicative).trans
      (denseTorusCoordinateRingEquiv hi).symm

/-- A monomial of exponent `h` is the zero-cone character with values `u ↦ det(h, u)`. -/
@[simp]
theorem denseTorusCoordinateRingEquivDet_single (hi : IsIntegralLattice i)
    (b : Module.Basis (Fin 2) ℤ N) (h : N) (z : ℂ) :
    denseTorusCoordinateRingEquivDet hi b (AddMonoidAlgebra.single h z) =
      MonoidAlgebra.single
        (ofAdd ((denseTorusDualEquiv hi).symm (b.detDualEquiv h).toAddMonoidHom)) z := by
  simp [denseTorusCoordinateRingEquivDet, AddMonoidAlgebra.toMultiplicativeAlgEquiv_single,
    MonoidAlgebra.domCongr_single]

/-- A native torus monomial has exponent given by the inverse determinant pairing. -/
@[simp]
theorem denseTorusCoordinateRingEquivDet_symm_single (hi : IsIntegralLattice i)
    (b : Module.Basis (Fin 2) ℤ N) (m : dualSemigroup hi (⊥ : PointedCone ℝ V)) (z : ℂ) :
    (denseTorusCoordinateRingEquivDet hi b).symm (MonoidAlgebra.single (ofAdd m) z) =
      AddMonoidAlgebra.single (b.detDualEquiv.symm (m : N →+ ℤ).toIntLinearMap) z := by
  apply (denseTorusCoordinateRingEquivDet hi b).injective
  have hm : (m : N →+ ℤ).toIntLinearMap.toAddMonoidHom = (m : N →+ ℤ) := by
    ext u
    simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.coe_toIntLinearMap]
  rw [AlgEquiv.apply_symm_apply, denseTorusCoordinateRingEquivDet_single,
    LinearEquiv.apply_symm_apply, hm, ← denseTorusDualEquiv_apply hi m,
    AddEquiv.symm_apply_apply]

end QPainleve.Toric

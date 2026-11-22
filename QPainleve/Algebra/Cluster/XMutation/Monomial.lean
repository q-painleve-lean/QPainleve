/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.XMutation.Symmetry
public import QPainleve.Geometry.Toric.CharacterTorus.Basic

/-!
# Character monomials in cluster X coordinates

A character is the product of the coordinate powers given by its exponent vector.
Relabeling and simultaneous inversion act on these characters by permuting and negating
their exponents, respectively.
-/

public noncomputable section

namespace QPainleve.Cluster

open CharacterTorus

variable (k : Type*) [Field k] {ι κ : Type*}

/-- A character supported on one label is a power of the corresponding X coordinate. -/
@[simp]
theorem monomial_finsupp_single (i : ι) (n : ℤ) :
    monomial k (Multiplicative.ofAdd (Finsupp.single i n)) = xCoordinate k i ^ n := by
  rw [← Finsupp.smul_single_one i n, ofAdd_zsmul, map_zpow, monomial_ofAdd, ← xCoordinate_def]

/-- Relabeling acts on a character by moving each exponent to its old label. -/
@[simp]
theorem xReindex_apply_monomial (e : κ ≃ ι) (x : κ →₀ ℤ) :
    xReindex k e (monomial k (Multiplicative.ofAdd x)) =
      monomial k (Multiplicative.ofAdd (Finsupp.domCongr e x)) := by
  let f := (xReindex k e).toAlgHom.toMonoidHom.comp (monomial k)
  let g := (monomial k).comp ((Finsupp.domCongr (M := ℤ) e).toMultiplicative.toMonoidHom)
  have h : f = g := by
    apply Finsupp.mulHom_ext
    intro i n
    simp [f, g, Finsupp.domCongr_apply, Finsupp.equivMapDomain_single]
  exact DFunLike.congr_fun h (Multiplicative.ofAdd x)

/-- Simultaneous X inversion negates the exponent of every character. -/
@[simp]
theorem xInversion_apply_monomial (x : ι →₀ ℤ) :
    xInversion k ι (monomial k (Multiplicative.ofAdd x)) =
      monomial k (Multiplicative.ofAdd (-x)) := by
  let f := (xInversion k ι).toAlgHom.toMonoidHom.comp (monomial k)
  let g := (monomial k).comp ((AddEquiv.neg (ι →₀ ℤ)).toMultiplicative.toMonoidHom)
  have h : f = g := by
    apply Finsupp.mulHom_ext
    intro i n
    simp [f, g, ← Finsupp.single_neg, inv_zpow']
  exact DFunLike.congr_fun h (Multiplicative.ofAdd x)

variable [Fintype ι]

/-- In independent X coordinates, a lattice character is the product of the coordinate
powers specified by its exponent vector. -/
theorem monomial_eq_prod_zpow_xCoordinate (x : ι → ℤ) :
    monomial k (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm x)) =
      ∏ i, xCoordinate k i ^ x i := by
  classical
  rw [Finsupp.equivFunOnFinite_symm_eq_sum, ofAdd_sum, map_prod]
  simp only [monomial_finsupp_single]

end QPainleve.Cluster

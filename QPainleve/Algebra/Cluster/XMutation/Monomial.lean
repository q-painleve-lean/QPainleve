/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.XMutation.Symmetry
public import QPainleve.Geometry.Toric.CharacterTorus.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

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
  change (xReindex k e).toAlgHom (monomial k (Multiplicative.ofAdd x)) = _
  rw [xReindex, algEquivOfAlgEquiv_domCongr_toAlgHom, functionFieldMap_monomial,
    AddEquiv.coe_toAddMonoidHom]

/-- Simultaneous X inversion negates the exponent of every character. -/
@[simp]
theorem xInversion_apply_monomial (x : ι →₀ ℤ) :
    xInversion k ι (monomial k (Multiplicative.ofAdd x)) =
      monomial k (Multiplicative.ofAdd (-x)) := by
  change (xInversion k ι).toAlgHom (monomial k (Multiplicative.ofAdd x)) = _
  rw [xInversion, algEquivOfAlgEquiv_domCongr_toAlgHom, functionFieldMap_monomial,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.neg_apply]

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

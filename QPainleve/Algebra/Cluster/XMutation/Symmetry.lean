/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.XMutation.Basic

/-!
# Inversion and relabeling of cluster X coordinates

Simultaneous inversion and relabeling act on the field of independent X
coordinates by changing Laurent exponents. Inversion commutes with relabeling
and intertwines mutation for an exchange column with mutation for the opposite
column. Relabeling transports both the mutation direction and the exchange column.

The signed inversion is the operation of Bershtein, Gavrylenko and Marshakov,
*Cluster integrable systems, q-Painlevé equations and their quantization*, §3.1.
The field maps use `AddMonoidAlgebra.domCongr` and
`IsFractionRing.algEquivOfAlgEquiv`.
-/

public noncomputable section

namespace QPainleve.Cluster

variable (k : Type*) [Field k] {ι κ ρ : Type*}

local notation:max "Laurent" ι:arg => AddMonoidAlgebra k (ι →₀ ℤ)
local notation:max "Functions" ι:arg => FractionRing (AddMonoidAlgebra k (ι →₀ ℤ))

/-- Pullback for simultaneous inversion of all independent cluster X coordinates. -/
@[expose]
def xInversion (ι : Type*) : Functions ι ≃ₐ[k] Functions ι :=
  IsFractionRing.algEquivOfAlgEquiv (AddMonoidAlgebra.domCongr k k (AddEquiv.neg (ι →₀ ℤ)))

/-- Simultaneous inversion sends each coordinate to its reciprocal. -/
@[simp] theorem xInversion_apply_xCoordinate (i : ι) :
    xInversion k ι (xCoordinate k i) = (xCoordinate k i)⁻¹ := by
  rw [xInversion, xCoordinate_def, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    AddMonoidAlgebra.domCongr_single]
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← map_one (algebraMap (Laurent ι) (Functions ι))]
  simp [AddMonoidAlgebra.one_def]

/-- Simultaneous inversion is its own inverse. -/
@[simp] theorem xInversion_symm (ι : Type*) : (xInversion k ι).symm = xInversion k ι := by
  simp [xInversion, IsFractionRing.algEquivOfAlgEquiv_symm, AddMonoidAlgebra.domCongr_symm]

/-- Applying simultaneous inversion twice gives the identity pullback. -/
@[simp] theorem xInversion_trans_xInversion (ι : Type*) :
    (xInversion k ι).trans (xInversion k ι) = AlgEquiv.refl := by
  simpa only [xInversion_symm] using AlgEquiv.self_trans_symm (xInversion k ι)

/-- Pullback along relabeling, where `e` sends each new label to its old label. -/
@[expose]
def xReindex (e : κ ≃ ι) : Functions κ ≃ₐ[k] Functions ι :=
  IsFractionRing.algEquivOfAlgEquiv (AddMonoidAlgebra.domCongr k k (Finsupp.domCongr (M := ℤ) e))

/-- A coordinate pulls back to the coordinate of its old label. -/
@[simp] theorem xReindex_apply_xCoordinate (e : κ ≃ ι) (i : κ) :
    xReindex k e (xCoordinate k i) = xCoordinate k (e i) := by
  simp [xReindex, xCoordinate_def, IsFractionRing.algEquivOfAlgEquiv_algebraMap]

/-- The inverse of a relabeling pullback uses the reverse label equivalence. -/
@[simp] theorem xReindex_symm (e : κ ≃ ι) : (xReindex k e).symm = xReindex k e.symm := by
  simp [xReindex, IsFractionRing.algEquivOfAlgEquiv_symm, AddMonoidAlgebra.domCongr_symm]

/-- The pullback for the identity relabeling is the identity equivalence. -/
@[simp] theorem xReindex_refl (ι : Type*) :
    xReindex k (Equiv.refl ι) = AlgEquiv.refl := by
  apply algEquiv_ext_xCoordinate k
  intro i
  simp

/-- Composition of relabeling pullbacks composes the maps from new labels to old labels. -/
@[simp] theorem xReindex_trans (e : ρ ≃ κ) (f : κ ≃ ι) :
    (xReindex k e).trans (xReindex k f) = xReindex k (e.trans f) := by
  apply algEquiv_ext_xCoordinate k
  intro i
  simp

/-- Inversion commutes with relabeling of the independent X coordinates. -/
theorem xInversion_trans_xReindex (e : κ ≃ ι) :
    (xInversion k κ).trans (xReindex k e) = (xReindex k e).trans (xInversion k ι) := by
  apply algEquiv_ext_xCoordinate k
  intro i
  simp

/-- Relabeling intertwines the mutations at corresponding labels and with corresponding columns. -/
theorem xMutation_trans_xReindex (e : κ ≃ ι) (p : κ) (a : ι → ℤ) :
    (xMutation k p (a ∘ e)).trans (xReindex k e) =
      (xReindex k e).trans (xMutation k (e p) a) := by
  apply algEquiv_ext_xCoordinate k
  intro i
  by_cases hi : i = p
  · subst i
    simp
  · simp [xMutation_apply_of_ne, hi, e.injective.ne hi]

/-- Inversion intertwines mutation for an exchange column with mutation for its negative.
Here `AlgEquiv.trans` composes pullbacks in their order of application to functions. -/
theorem xMutation_trans_xInversion (p : ι) (a : ι → ℤ) :
    (xMutation k p (-a)).trans (xInversion k ι) =
      (xInversion k ι).trans (xMutation k p a) := by
  apply algEquiv_ext_xCoordinate k
  intro i
  by_cases hi : i = p
  · subst i
    simp
  simp only [AlgEquiv.trans_apply, xMutation_apply_of_ne _ _ _ hi, xInversion_apply_xCoordinate,
    map_mul, map_add, map_one, map_zpow₀, map_inv₀, Pi.neg_apply, neg_neg, mul_inv_rev, ← zpow_neg]
  have hBinomial : 1 + (xCoordinate k p)⁻¹ = (xCoordinate k p)⁻¹ * (1 + xCoordinate k p) := by
    simp [mul_add, add_comm]
  simp only [hBinomial, mul_zpow, inv_zpow']
  have hExp : -max (-a i) 0 + -a i = -max (a i) 0 := by omega
  calc
    _ = (xCoordinate k i)⁻¹ *
        ((xCoordinate k p) ^ (-max (-a i) 0) * (xCoordinate k p) ^ (-a i)) *
        (1 + xCoordinate k p) ^ a i := by ac_rfl
    _ = _ := by
      rw [← zpow_add₀ (xCoordinate_ne_zero k p), hExp]
      simp only [mul_comm, mul_left_comm]

end QPainleve.Cluster

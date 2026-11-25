/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Word
public import QPainleve.Geometry.Toric.Fan.Charge

/-!
# Exchange matrices of labeled toric rays

An ordered rank-two lattice basis and a finite labeled family of rays determine
the exchange matrix used for cluster words. The same ray charges realize any
skew exchange matrix with these determinant entries.
-/

public noncomputable section

open Module QPainleve.Cluster

namespace TauCeti.Toric.Fan

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Fintype ι] [DecidableEq ι]

/-- The skew exchange matrix of the primitive charges of the labeled rays,
paired by the determinant in the given lattice frame. -/
def rayExchangeMatrix (b : Basis (Fin 2) ℤ N) (s : ι → Φ.Ray) : SkewExchangeMatrix ι :=
  .ofMatrix (chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s))
    (isSkewSymmetrizer_chargeExchangeMatrix _ b.detDualEquiv_self _)

/-- The underlying integer matrix pairs the ray charges in the given frame. -/
@[simp]
theorem rayExchangeMatrix_matrix (b : Basis (Fin 2) ℤ N) (s : ι → Φ.Ray) :
    (rayExchangeMatrix b s).matrix =
      chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s) :=
  SkewExchangeMatrix.matrix_ofMatrix _ _

/-- Realize a skew exchange matrix with the given determinant entries by the labeled ray charges. -/
def rayChargeSeed (b : Basis (Fin 2) ℤ N) (s : ι → Φ.Ray) {E : SkewExchangeMatrix ι}
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s)) :
    ChargeSeed E N :=
  ⟨b.detDualEquiv.toLinearMap, rayChargeMap s, b.detDualEquiv_self, hE.symm⟩

/-- The pairing of a ray charge seed is the determinant in its lattice frame. -/
@[simp]
theorem rayChargeSeed_form (b : Basis (Fin 2) ℤ N) (s : ι → Φ.Ray) {E : SkewExchangeMatrix ι}
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s)) :
    (rayChargeSeed b s hE).form = b.detDualEquiv.toLinearMap :=
  (rfl)

/-- The charge map of a ray charge seed sends basis vectors to the primitive ray generators. -/
@[simp]
theorem rayChargeSeed_charge (b : Basis (Fin 2) ℤ N) (s : ι → Φ.Ray) {E : SkewExchangeMatrix ι}
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s)) :
    (rayChargeSeed b s hE).charge = rayChargeMap s :=
  (rfl)

end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.ModularGroup

import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Relabeling signed loop pullbacks

Changing the label type conjugates the signed loop pullback subgroup by the
corresponding renaming of the independent X coordinates. The path comparison
`Quiver.Path.xPullback_reindex` identifies the conjugated pullback with the
pullback of the relabeled loop.
-/

public noncomputable section

namespace QPainleve.Cluster

open Quiver

variable (k : Type*) [Field k] {ι κ : Type*}
  [DecidableEq ι] [DecidableEq κ]

private theorem autCongr_xPullback {B : SkewExchangeMatrix ι} (e : ι ≃ κ) (w : Word B B) :
    (xReindex k e).autCongr (w.xPullback k) =
      ((SkewExchangeMatrix.reindexPrefunctor e).mapPath w).xPullback k := by
  ext x
  apply (xReindex k e.symm).injective
  have h := DFunLike.congr_fun (w.xPullback_reindex k e) x
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, xReindex_symm] at h ⊢
  simpa only [← xReindex_symm k e, AlgEquiv.symm_apply_apply] using h.symm

private theorem autCongr_mem_signedLoopPullbacks {B : SkewExchangeMatrix ι} (e : ι ≃ κ)
    {f} (hf : f ∈ signedLoopPullbacks k B) :
    (xReindex k e).autCongr f ∈ signedLoopPullbacks k (B.reindex e) := by
  obtain ⟨w, rfl⟩ := (mem_signedLoopPullbacks_iff k B f).mp hf
  have hw := (autCongr_xPullback k e w).symm
  simpa only [SkewExchangeMatrix.reindexPrefunctor_obj] using
    (mem_signedLoopPullbacks_iff k _ _).mpr ⟨_, hw⟩

private theorem map_signedLoopPullbacks_reindex (B : SkewExchangeMatrix ι) (e : ι ≃ κ) :
    (signedLoopPullbacks k B).map (xReindex k e).autCongr.toMonoidHom =
      signedLoopPullbacks k (B.reindex e) := by
  ext f
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro h
    exact (xReindex k e).autCongr.apply_symm_apply f ▸ autCongr_mem_signedLoopPullbacks k e h
  · intro h
    rw [AlgEquiv.autCongr_symm, xReindex_symm]
    simpa only [SkewExchangeMatrix.reindex_trans, Equiv.self_trans_symm,
      SkewExchangeMatrix.reindex_refl] using autCongr_mem_signedLoopPullbacks k e.symm h

/-- Renaming the exchange matrix labels identifies the signed pullback groups
by conjugation on the field of independent X coordinates. -/
def signedLoopPullbacksReindex (B : SkewExchangeMatrix ι) (e : ι ≃ κ) :
    signedLoopPullbacks k B ≃* signedLoopPullbacks k (B.reindex e) :=
  TauCeti.Subgroup.congrOfMapEq (xReindex k e).autCongr (map_signedLoopPullbacks_reindex k B e)

/-- A relabeled pullback acts by the original pullback in the renamed coordinates. -/
@[simp]
theorem signedLoopPullbacksReindex_apply (B : SkewExchangeMatrix ι) (e : ι ≃ κ)
    (f : signedLoopPullbacks k B) (x : FractionRing (AddMonoidAlgebra k (κ →₀ ℤ))) :
    (signedLoopPullbacksReindex k B e f).val x = xReindex k e (f.val (xReindex k e.symm x)) := by
  have h := TauCeti.Subgroup.coe_congrOfMapEq_apply (xReindex k e).autCongr
    (map_signedLoopPullbacks_reindex k B e) f
  simpa only [signedLoopPullbacksReindex, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    xReindex_symm] using
    DFunLike.congr_fun h x

end QPainleve.Cluster

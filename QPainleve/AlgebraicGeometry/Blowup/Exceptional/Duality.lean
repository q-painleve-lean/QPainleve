/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Point.CanonicalCohomology
public import QPainleve.AlgebraicGeometry.Cohomology.TracePairing

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.GlobalSections
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.SecondCohomology
import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Top-degree duality for exceptional twists of coefficient at most one

For a point blowup of a smooth projective surface, the exceptional twist by `mE`
with `m ≤ 1` preserves top cohomology. The canonical complement has exceptional
coefficient `1 - m`, so its global sections are preserved as well. Consequently
perfection of the top-degree trace pairing is equivalent for the base line bundle
and its exceptional twist on the blowup.

The canonical coefficient comes from Hacking's point blowup formula
([*583C Lecture notes*, Proposition 7.2][Hacking]). The cohomology comparisons
use the exceptional Cartier quotients of [Stacks, Lemma 54.3.4][Stacks].

[Hacking]: https://paulhacking.github.io/surfaces.pdf#page=35
[Stacks]: https://stacks.math.columbia.edu/tag/0AGS
-/

public noncomputable section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {p : X} (k : Type u) [Field k] [PerfectField k]
  [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "J" => vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
local notation "Y" => blowup J
local notation "π" => blowupToBase J
local notation "S" => Spec (CommRingCat.of k)
local notation "K[" W "]" => QPainleve.canonicalBundle k W 2

variable (hp : IsClosed ({p} : Set X))

/-- The space of sections of the canonical complement of an exceptional twist of coefficient
`m ≤ 1` is linearly isomorphic to that of the canonical complement on the base. -/
theorem nonempty_cohomologyZero_canonicalComplement_pointBlowup
    (L : InvertibleSheaf X) (M : InvertibleSheaf Y) {m : ℤ}
    (hM : LineBundleClass.mk M =
      LineBundleClass.pullback π (LineBundleClass.mk L) * (J).blowupExceptionalClass ^ m)
    (hm : m ≤ 1) :
    let : (Y).Over S := ⟨π ≫ X ↘ S⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ S) hp
    Nonempty (Cohomology (K[X].tensorProduct L.dual).obj 0 ≃ₗ[k]
      Cohomology (K[Y].tensorProduct M.dual).obj 0) := by
  let : (Y).Over S := ⟨π ≫ X ↘ S⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
    smoothOfRelativeDimension_blowup_closed_point (X ↘ S) hp
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ S)
  have : IsRegularLocalRing (X.presheaf.stalk p) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ S) p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (X ↘ S) 2).mp
    inferInstance).2 p hp
  let n : ℕ := (1 - m).toNat
  have hn : (n : ℤ) = 1 - m := Int.toNat_of_nonneg (by omega)
  let A := K[X].tensorProduct L.dual
  let B := K[Y].tensorProduct M.dual
  have hB : LineBundleClass.mk B =
      LineBundleClass.pullback π (LineBundleClass.mk A) * (J).blowupExceptionalClass ^ (n : ℤ) := by
    dsimp only [A, B]
    open LineBundleClass in
    rw [hn, mk_tensorProduct, ← inv_mk, hM, mk_canonicalBundle_pointBlowup k hp,
      mul_inv_rev, ← zpow_neg, mk_tensorProduct, ← inv_mk, pullback_mul, pullback_inv,
      sub_eq_add_neg, zpow_add, zpow_one]
    ac_rfl
  -- The exceptional twist comparison presents the closed center as a residue-field kernel.
  have compare (I : X.IdealSheafData) (hI : I = (X.fromSpecResidueField p).ker)
      (F : InvertibleSheaf I.blowup)
      (hF : LineBundleClass.mk F =
        LineBundleClass.pullback I.blowupToBase (LineBundleClass.mk A) *
          I.blowupExceptionalClass ^ (n : ℤ)) :
      letI : I.blowup.Over S := ⟨I.blowupToBase ≫ X ↘ S⟩
      Cohomology A.obj 0 ≃ₗ[k] Cohomology F.obj 0 := by
    subst I
    refine cohomologyZeroPointBlowupExceptionalTwistLinearEquiv p k hp hdim A n F ?_
    simpa only [blowupExceptionalClass_def, inv_zpow'] using hF
  exact ⟨compare _ (X.ker_fromSpecResidueField_eq_vanishingIdeal p).symm B hB⟩

variable [Infinite k] [IsIntegral X] [X.IsProjectiveOver k]

/-- For an exceptional twist with coefficient `m ≤ 1`, the top-degree trace pairing on
the blowup is perfect exactly when the pairing on the base line bundle is perfect.
The trace on the blowup is transported by pullback of top differential forms. -/
theorem isPerfPair_cohomologyTracePairing_of_exceptional_twist_le_one
    (L : InvertibleSheaf X) (M : InvertibleSheaf Y) {m : ℤ}
    (hM : LineBundleClass.mk M =
      LineBundleClass.pullback π (LineBundleClass.mk L) * (J).blowupExceptionalClass ^ m)
    (hm : m ≤ 1) (tr : Cohomology K[X].obj 2 →ₗ[k] k) (htr : tr ≠ 0) :
    let : (Y).Over S := ⟨π ≫ X ↘ S⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ S) hp
    let trY := tr.comp (cohomologyCanonicalBundlePointBlowupLinearEquiv k hp 2).symm.toLinearMap
    (cohomologyTracePairing (M := M.obj) k 2 trY).IsPerfPair ↔
      (cohomologyTracePairing (M := L.obj) k 2 tr).IsPerfPair := by
  intro _ _ trY
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ S)
  have : IsRegularLocalRing (X.presheaf.stalk p) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ S) p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (X ↘ S) 2).mp
    inferInstance).2 p hp
  have : IsIntegral Y := isIntegral_blowup_closed_point (X ↘ S) hp
  have : (Y).IsProjectiveOver k := (J).isProjectiveOver_blowup_of_isNoetherianRing k
  have compare (I : X.IdealSheafData) (hI : I = (X.fromSpecResidueField p).ker)
      (F : InvertibleSheaf I.blowup)
      (hF : LineBundleClass.mk F =
        LineBundleClass.pullback I.blowupToBase (LineBundleClass.mk L) *
          I.blowupExceptionalClass ^ m) :
      let : I.blowup.Over S := ⟨I.blowupToBase ≫ X ↘ S⟩
      Nonempty (Cohomology L.obj 2 ≃ₗ[k] Cohomology F.obj 2) := by
    subst I
    exact nonempty_cohomologyTwoPointBlowupExceptionalTwistLinearEquiv k hp hdim F L hF hm
  obtain ⟨e₂⟩ := compare _ (X.ker_fromSpecResidueField_eq_vanishingIdeal p).symm M hM
  obtain ⟨e₀⟩ := nonempty_cohomologyZero_canonicalComplement_pointBlowup k hp L M hM hm
  let e := (L.sectionsInternalHomLinearEquiv k K[X]).trans
    (e₀.trans (M.sectionsInternalHomLinearEquiv k K[Y]).symm)
  have htrY : trY ≠ 0 := by
    intro h
    apply htr
    ext x
    simpa only [trY, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.zero_apply] using
      DFunLike.congr_fun h (cohomologyCanonicalBundlePointBlowupLinearEquiv k hp 2 x)
  rw [M.isPerfPair_cohomologyTracePairing_iff_finrank k K[Y]
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ S) (n := 2)).le trY htrY,
    L.isPerfPair_cohomologyTracePairing_iff_finrank k K[X]
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)).le tr htr]
  exact ⟨fun h ↦ e₂.finrank_eq.trans (h.trans e.finrank_eq.symm),
    fun h ↦ e₂.finrank_eq.symm.trans (h.trans e.finrank_eq)⟩

end AlgebraicGeometry.Scheme.IdealSheafData

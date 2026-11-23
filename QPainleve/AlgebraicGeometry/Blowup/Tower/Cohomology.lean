/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import TauCeti.AlgebraicGeometry.LineBundle.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import QPainleve.AlgebraicGeometry.Blowup.PointCohomology
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.LineBundle.Pullback
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Cohomology along towers of point blowups

The cohomology of a finite locally free sheaf on a smooth surface agrees in each degree
with that of its pullback along an ordered tower of closed point blowups. Two such
towers to a common surface compare the structure-sheaf cohomology of their bases.
The comparison iterates `Scheme.IdealSheafData.pointBlowupCohomologyLinearEquiv`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y W : Scheme.{u}} {m n : ℕ}
variable (k : Type u) [Field k] [PerfectField k]
  [X.Over (Spec (.of k))]

private theorem nonempty_cohomologyPullbackLinearEquiv_of_comp
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    (g : Y ⟶ Spec (.of k)) (hg : g = T.toBase ≫ X ↘ Spec (.of k))
    (E : FiniteLocallyFreeSheaf X) (i : ℕ) :
    let : Y.Over (Spec (.of k)) := ⟨g⟩
    Nonempty (Cohomology E.obj i ≃ₗ[k] Cohomology ((pullback T.toBase).obj E.obj) i) := by
  induction hT with
  | nil =>
    rw [toBase_nil, Category.id_comp] at hg
    subst g
    intros
    rw [toBase_nil]
    exact ⟨cohomologyBaseLinearEquivOfIso k ((pullbackId X).app E.obj).symm i⟩
  | @snoc _ Z S I hS p hp hI ih =>
    have hcenter := hI.trans (Z.ker_fromSpecResidueField_eq_vanishingIdeal p)
    clear hI
    subst I
    rw [toBase_snoc, Category.assoc] at hg
    subst g
    intros
    let : Z.Over (Spec (.of k)) := ⟨S.toBase ≫ X ↘ Spec (.of k)⟩
    have hd : SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k)) :=
      hS.smoothOfRelativeDimension (X ↘ Spec (.of k))
    have : Smooth (Z ↘ Spec (.of k)) := hd.smooth 2 _
    have : IsRegular Z := IsRegular.of_smooth (Z ↘ Spec (.of k))
    have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
      (Z ↘ Spec (.of k)) 2).mp hd).2 p hp
    obtain ⟨e⟩ := ih (Z ↘ Spec (.of k)) rfl
    let P := (FiniteLocallyFreeSheaf.pullback S.toBase).obj E
    let J := Scheme.IdealSheafData.vanishingIdeal
      (X := Z) ⟨closure ({p} : Set Z), isClosed_closure⟩
    have eStep : Cohomology ((pullback S.toBase).obj E.obj) i ≃ₗ[k]
        Cohomology ((pullback J.blowupToBase).obj ((pullback S.toBase).obj E.obj)) i := by
      rw [← FiniteLocallyFreeSheaf.pullback_obj_obj S.toBase E]
      exact Scheme.IdealSheafData.pointBlowupCohomologyLinearEquiv k hp hdim P i
    rw [toBase_snoc]
    exact ⟨e.trans (eStep.trans (cohomologyBaseLinearEquivOfIso k
      ((pullbackComp J.blowupToBase S.toBase).app E.obj) i))⟩

variable [Y.Over (Spec (.of k))]

/-- Pullback along a tower of closed point blowups preserves all cohomology of finite
locally free sheaves, as vector spaces over the base field. -/
theorem nonempty_cohomologyPullbackLinearEquiv
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    [T.toBase.IsOver (Spec (.of k))] (E : FiniteLocallyFreeSheaf X) (i : ℕ) :
    Nonempty (Cohomology E.obj i ≃ₗ[k] Cohomology ((pullback T.toBase).obj E.obj) i) :=
  hT.nonempty_cohomologyPullbackLinearEquiv_of_comp k (Y ↘ Spec (.of k))
    (comp_over T.toBase (Spec (.of k))).symm E i

variable [W.Over (Spec (.of k))]
  {T : BlowupTower X m W} {U : BlowupTower Y n W}
  [T.toBase.IsOver (Spec (.of k))] [U.toBase.IsOver (Spec (.of k))]

/-- A common resolution by closed point blowups identifies the structure-sheaf
cohomology of the two smooth surfaces in every degree. -/
theorem nonempty_cohomologyTrivialLinearEquiv_of_common_resolution
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U) (i : ℕ) :
    Nonempty (Cohomology (InvertibleSheaf.trivial X).obj i ≃ₗ[k]
      Cohomology (InvertibleSheaf.trivial Y).obj i) := by
  obtain ⟨eT⟩ := hT.nonempty_cohomologyPullbackLinearEquiv k
    ((InvertibleSheaf.toFiniteLocallyFree X).obj (InvertibleSheaf.trivial X)) i
  obtain ⟨eU⟩ := hU.nonempty_cohomologyPullbackLinearEquiv k
    ((InvertibleSheaf.toFiniteLocallyFree Y).obj (InvertibleSheaf.trivial Y)) i
  let t := cohomologyBaseLinearEquivOfIso k (InvertibleSheaf.pullbackTrivialObjIso T.toBase) i
  let u := cohomologyBaseLinearEquivOfIso k (InvertibleSheaf.pullbackTrivialObjIso U.toBase) i
  exact ⟨eT.trans (t.trans (u.symm.trans eU.symm))⟩

/-- For a common resolution by closed point blowups, the structure sheaves of the two
smooth surfaces have equal Euler characteristics at every cutoff. -/
theorem eulerCharBelow_trivial_eq_of_common_resolution
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U) (q : ℕ) :
    LineBundleClass.eulerCharBelow k (1 : LineBundleClass X) q =
      LineBundleClass.eulerCharBelow k (1 : LineBundleClass Y) q := by
  simp only [← LineBundleClass.mk_trivial, LineBundleClass.eulerCharBelow_mk]
  induction q with
  | zero => simp only [eulerCharBelow_zero]
  | succ i ih =>
    obtain ⟨e⟩ := hT.nonempty_cohomologyTrivialLinearEquiv_of_common_resolution k hU i
    simp only [eulerCharBelow_succ, ih, e.finrank_eq]

end QPainleve.BlowupTower.IsClosedPointTower

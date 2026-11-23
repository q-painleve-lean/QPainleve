/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Canonical
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.GlobalSections
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Pluricanonical sections under point blowups

The spaces of global sections of each nonnegative tensor power of the canonical bundle are
isomorphic before and after a closed point blowup of a smooth surface. The canonical bundle formula
expresses the tensor power on the blowup as a pullback with a nonnegative exceptional twist.
The comparison for one blowup then iterates along towers and compares two surfaces with a
common resolution.

The canonical class formula is [Hacking, *Compact Complex Surfaces*, Proposition 7.2][Hacking].
The bicanonical case gives the space used in [Vakil, *Complex Algebraic Surfaces*, Class 16][Vakil].

[Hacking]: https://paulhacking.github.io/surfaces.pdf#page=35
[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass16A.pdf
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open QPainleve

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (k : Type u) [Field k] [PerfectField k]
  [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

/-- A point blowup of a smooth surface preserves the space of sections of each
nonnegative tensor power of the relative canonical bundle. -/
noncomputable def cohomologyZeroPluricanonicalLinearEquiv {p : X}
    (hp : IsClosed ({p} : Set X)) (m : ℕ) :
    let I := vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
    letI : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ X ↘ Spec (.of k)⟩
    letI : SmoothOfRelativeDimension 2 (I.blowup ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
    Cohomology ((canonicalBundle k X 2).tensorPow m).obj 0 ≃ₗ[k]
      Cohomology ((canonicalBundle k I.blowup 2).tensorPow m).obj 0 := by
  let I := vanishingIdeal (X := X) (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
  letI : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ X ↘ Spec (.of k)⟩
  haveI : SmoothOfRelativeDimension 2 (I.blowup ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    (X ↘ Spec (.of k)) 2).mp inferInstance).2 p hp
  let L := (canonicalBundle k X 2).tensorPow m
  let M := (canonicalBundle k I.blowup 2).tensorPow m
  have hM : LineBundleClass.mk M =
      LineBundleClass.pullback I.blowupToBase (LineBundleClass.mk L) *
        I.blowupExceptionalClass ^ m := by
    dsimp only [L, M]
    rw [LineBundleClass.mk_tensorPow, LineBundleClass.mk_tensorPow,
      mk_canonicalBundle_pointBlowup k hp, mul_pow, LineBundleClass.pullback_pow]
  -- The exceptional-twist comparison presents the same center as a residue-field kernel.
  have compare (J : X.IdealSheafData) (hJ : J = (X.fromSpecResidueField p).ker) :
      ∀ (N : InvertibleSheaf J.blowup),
        LineBundleClass.mk N = LineBundleClass.pullback J.blowupToBase (LineBundleClass.mk L) *
          J.blowupExceptionalClass ^ m →
        letI : J.blowup.Over (Spec (.of k)) := ⟨J.blowupToBase ≫ X ↘ Spec (.of k)⟩
        Cohomology L.obj 0 ≃ₗ[k] Cohomology N.obj 0 := by
    subst J
    intro N hN
    refine cohomologyZeroPointBlowupExceptionalTwistLinearEquiv p k hp hdim L m N ?_
    simpa only [blowupExceptionalClass_def, inv_pow, zpow_neg, zpow_natCast] using hN
  exact compare I (X.ker_fromSpecResidueField_eq_vanishingIdeal p).symm M hM

end AlgebraicGeometry.Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y Z : Scheme.{u}} {n d : ℕ} {T : BlowupTower X n Z}
  (k : Type u) [Field k] [PerfectField k] [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

private theorem nonempty_cohomologyZero_pluricanonicalLinearEquiv_of_comp
    (hT : IsClosedPointTower X T) (m : ℕ) (g : Z ⟶ Spec (.of k))
    (hg : g = T.toBase ≫ X ↘ Spec (.of k)) (hgSmooth : SmoothOfRelativeDimension 2 g) :
    letI : Z.Over (Spec (.of k)) := ⟨g⟩
    letI : SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k)) := hgSmooth
    Nonempty (Cohomology ((canonicalBundle k X 2).tensorPow m).obj 0 ≃ₗ[k]
      Cohomology ((canonicalBundle k Z 2).tensorPow m).obj 0) := by
  induction hT with
  | nil =>
    rw [toBase_nil, Category.id_comp] at hg
    subst g
    exact ⟨LinearEquiv.refl k _⟩
  | @snoc _ W S I hS p hp hI ih =>
    have hcenter := hI.trans (W.ker_fromSpecResidueField_eq_vanishingIdeal p)
    clear hI
    subst I
    rw [toBase_snoc, Category.assoc] at hg
    subst g
    let : W.Over (Spec (.of k)) := ⟨S.toBase ≫ X ↘ Spec (.of k)⟩
    have : SmoothOfRelativeDimension 2 (W ↘ Spec (.of k)) :=
      hS.smoothOfRelativeDimension (X ↘ Spec (.of k))
    obtain ⟨e⟩ := ih (W ↘ Spec (.of k)) rfl inferInstance
    exact ⟨e.trans (Scheme.IdealSheafData.cohomologyZeroPluricanonicalLinearEquiv k hp m)⟩

variable [Z.Over (Spec (.of k))]

/-- A tower of closed point blowups of a smooth surface preserves each pluricanonical
space. The comparison applies to towers with infinitely near centers. -/
theorem nonempty_cohomologyZero_pluricanonicalLinearEquiv
    [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
    (hT : IsClosedPointTower X T) [T.toBase.IsOver (Spec (.of k))] (m : ℕ) :
    Nonempty (Cohomology ((canonicalBundle k X 2).tensorPow m).obj 0 ≃ₗ[k]
      Cohomology ((canonicalBundle k Z 2).tensorPow m).obj 0) :=
  nonempty_cohomologyZero_pluricanonicalLinearEquiv_of_comp k hT m (Z ↘ Spec (.of k))
    (comp_over T.toBase (Spec (.of k))).symm inferInstance

variable [Y.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  {U : BlowupTower Y d Z}

/-- Two smooth surfaces with a common resolution by closed point blowups have isomorphic
spaces of global sections of every nonnegative tensor power of their canonical bundles. -/
theorem nonempty_cohomologyZero_pluricanonicalLinearEquiv_of_common_resolution
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U)
    [T.toBase.IsOver (Spec (.of k))] [U.toBase.IsOver (Spec (.of k))] (m : ℕ) :
    Nonempty (Cohomology ((canonicalBundle k X 2).tensorPow m).obj 0 ≃ₗ[k]
      Cohomology ((canonicalBundle k Y 2).tensorPow m).obj 0) := by
  have : SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k)) := by
    rw [← comp_over T.toBase (Spec (.of k))]
    exact hT.smoothOfRelativeDimension (X ↘ Spec (.of k))
  obtain ⟨eT⟩ := hT.nonempty_cohomologyZero_pluricanonicalLinearEquiv k m
  obtain ⟨eU⟩ := hU.nonempty_cohomologyZero_pluricanonicalLinearEquiv k m
  exact ⟨eT.trans eU.symm⟩

end QPainleve.BlowupTower.IsClosedPointTower

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Point.CanonicalCohomology
public import QPainleve.AlgebraicGeometry.Cohomology.TracePairing

/-!
# The canonical trace pairing under point blowup

Pulling back a line bundle and its canonical-valued sections preserves the values
of the trace pairing when the trace is transported by the comparison on top
forms. The equality uses the natural cohomology comparison for the pullback and
the map on canonical bundles.
-/

public noncomputable section

open CategoryTheory MonoidalClosed TopologicalSpace QPainleve
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} {p : X} (k : Type u) [Field k] [PerfectField k]
  [X.Over (Spec (CommRingCat.of k))] [SmoothOfRelativeDimension 2 (X ↘ Spec (CommRingCat.of k))]

local notation "Iₚ" => vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
local notation "Y" => blowup Iₚ
local notation "π" => blowupToBase Iₚ
local notation "S" => Spec (CommRingCat.of k)
local notation "K[" W "]" => canonicalBundle k W 2
local notation "V[" L "]" => Functor.obj (InvertibleSheaf.toFiniteLocallyFree X) L

/-- Pulling back a class and its canonical-valued section along a point blowup
preserves the trace pairing. The section is pulled back as a map of sheaves and
then composed with pullback of top differential forms. -/
theorem cohomologyTracePairing_pointBlowup
    (hp : IsClosed ({p} : Set X)) (L : InvertibleSheaf X)
    (q : ℕ) (tr : Cohomology K[X].obj q →ₗ[k] k)
    (x : Cohomology L.obj q) (s : Γ((ihom L.obj).obj K[X].obj, ⊤)) :
    let : (Y).Over S := ⟨π ≫ X ↘ S⟩
    let : (π).IsOver S := ⟨rfl⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ S) hp
    let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ S)
    let : IsRegularLocalRing (X.presheaf.stalk p) :=
      isRegularLocalRing_stalk_of_smooth (X ↘ S) p
    let hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
      (X ↘ S) 2).mp inferInstance).2 p hp
    let d := topDifferentialFormsMap k π 2
    let e := cohomologyCanonicalBundlePointBlowupLinearEquiv k hp q
    let trY := tr.comp e.symm.toLinearMap
    cohomologyTracePairing k q trY (pointBlowupCohomologyLinearEquiv k hp hdim V[L] q x)
        (internalHomSectionsEquiv.symm ((pullback π).map (internalHomSectionsEquiv s) ≫ d)) =
      cohomologyTracePairing k q tr x s := by
  intro _ _ _ _ _ _ hdim d e trY
  simp only [cohomologyTracePairing_apply, Equiv.apply_symm_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, trY]
  let a := internalHomSectionsEquiv s
  let y := pointBlowupCohomologyLinearEquiv k hp hdim V[L] q x
  let z := cohomologyMapBaseLinear k X a q x
  have hcomp := DFunLike.congr_fun
    (cohomologyMapBaseLinear_comp k Y ((pullback π).map a) d q) y
  have h := pointBlowupCohomologyLinearEquiv_naturality k hp hdim
    (E := V[L]) (F := V[K[X]]) a q x
  have he := cohomologyCanonicalBundlePointBlowupLinearEquiv_apply k hp q z
  have heval := hcomp.trans
    ((congrArg (cohomologyMapBaseLinear k Y d q) h.symm).trans he.symm)
  exact (congrArg (fun t ↦ tr (e.symm t)) heval).trans (congrArg tr (e.symm_apply_apply z))

end AlgebraicGeometry.Scheme.IdealSheafData

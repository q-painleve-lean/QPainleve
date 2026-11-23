/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Restriction
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf
import TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic

/-!
# Cohomology of the once-twisted exceptional quotient

The Cartier quotient for a pulled-back line bundle twisted by one copy of the
exceptional divisor is the direct image of `𝒪(-1)` on the exceptional projective
line. Its cohomology vanishes in every degree.

See the Cartier quotients in the blowup filtration of [Stacks, Lemma 54.3.4][Stacks].

[Stacks]: https://stacks.math.columbia.edu/tag/0AGS
-/

public section

open CategoryTheory MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} {p : X}

local notation "Iₚ" => vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
local notation "Y" => blowup Iₚ
local notation "π" => blowupToBase Iₚ
local notation "E" => comap Iₚ π

/-- The `𝒪(-1)` exceptional quotient of a once-twisted pulled-back line bundle is acyclic.
The assertion holds for any residue field at the closed point. -/
theorem subsingleton_cohomology_pointBlowup_exceptional_quotient_of_twist_one
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (a : LineBundleClass X) (M : InvertibleSheaf Y)
    (hM : LineBundleClass.mk M = LineBundleClass.pullback π a * (Iₚ).blowupExceptionalClass)
    (q : ℕ) : Subsingleton (Cohomology (M.obj ⊗ (E).pushforwardSubscheme) q) := by
  have compare (I : X.IdealSheafData) (hI : I = (X.fromSpecResidueField p).ker)
      (M : InvertibleSheaf I.blowup)
      (hM : LineBundleClass.mk M =
        LineBundleClass.pullback I.blowupToBase a * I.blowupExceptionalClass) :
      Subsingleton (Cohomology (M.obj ⊗ (I.comap I.blowupToBase).pushforwardSubscheme) q) := by
    subst I
    let J := (X.fromSpecResidueField p).ker
    let D := J.comap J.blowupToBase
    let ι := D.subschemeι
    let κ := X.residueField p
    obtain ⟨e, -, htwist⟩ := exists_iso_projectiveLine_residueField_exceptional_twist p hp hdim
    obtain ⟨t⟩ := htwist a 1 M (by simpa only [zpow_neg, zpow_one,
      blowupExceptionalClass_def] using hM)
    let N := (Scheme.Modules.pullback ι).obj M.obj
    have h : M.obj ⊗ D.pushforwardSubscheme ≅ (pushforward ι).obj N := by
      simpa only [N, FiniteLocallyFreeSheaf.pullback_obj_obj, ObjectProperty.ιOfLE_obj_obj] using
        D.tensorPushforwardSubschemeIso ((InvertibleSheaf.toFiniteLocallyFree J.blowup).obj M)
    let c := (cohomologyFunctor _ q).mapIso h ≪≫ cohomologyPushforwardIso ι N q
    let c' := (cohomologyFunctor _ q).mapIso ((e.hom.pullbackIsoPushforwardInv).app N) ≪≫
      cohomologyPushforwardIso (inv e.hom) N q
    let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule κ (Fin 2 → κ)
    -- Compare the restricted line bundle with the negative twist on the residue-field line.
    let eN := ((Scheme.Modules.pullbackComp e.hom ι).app M.obj) ≪≫ t
    let d := (cohomologyFunctor _ q).mapIso eN
    have hz : Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 (-1)) q) := by
      cases q with
      | zero =>
        exact TauCeti.SymmetricAlgebra.subsingleton_cohomology_zero_twistingSheaf_of_neg
          (by decide : (-1 : ℤ) < 0) (Pi.basisFun κ (Fin 2))
      | succ q =>
        exact (Pi.basisFun κ (Fin 2)).subsingleton_cohomology_twistingSheaf_of_neg_card_lt
          (m := -1) (by decide) (Nat.succ_pos q)
    exact @Function.Injective.subsingleton _ _ _
      (c ≪≫ c'.symm ≪≫ d).addCommGroupIsoToAddEquiv.injective hz
  exact compare (Iₚ) (X.ker_fromSpecResidueField_eq_vanishingIdeal p).symm M hM

end AlgebraicGeometry.Scheme.IdealSheafData

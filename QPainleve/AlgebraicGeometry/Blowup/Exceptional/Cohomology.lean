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
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Restriction
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf
import TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic

/-!
# Cohomology of exceptional Cartier quotients

The Cartier quotient for a pulled-back line bundle twisted by `mE` has the
cohomology of `𝒪(-m)` on the projective line over the residue field of the center.
In particular, the once-twisted quotient is acyclic.

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

/-- The exceptional Cartier quotient of the twist by `mE` has the cohomology of
`𝒪(-m)` on the projective line over the residue field of the center. -/
theorem nonempty_cohomologyAddEquiv_pointBlowup_exceptional_quotient
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (a : LineBundleClass X) (m : ℤ) (M : InvertibleSheaf ((X.fromSpecResidueField p).ker.blowup))
    (hM : LineBundleClass.mk M = LineBundleClass.pullback
      (X.fromSpecResidueField p).ker.blowupToBase a *
        (X.fromSpecResidueField p).ker.blowupExceptionalClass ^ m)
    (q : ℕ) :
    let J := (X.fromSpecResidueField p).ker
    let κ := X.residueField p
    Nonempty (Cohomology (M.obj ⊗ (J.comap J.blowupToBase).pushforwardSubscheme) q ≃+
      Cohomology (Proj.twistingSheaf
        (TauCeti.SymmetricAlgebra.homogeneousSubmodule κ (Fin 2 → κ)) (-m)) q) := by
  let J := (X.fromSpecResidueField p).ker
  let D := J.comap J.blowupToBase
  let ι := D.subschemeι
  obtain ⟨e, -, htwist⟩ := exists_iso_projectiveLine_residueField_exceptional_twist p hp hdim
  obtain ⟨t⟩ := htwist a m M (by
    simpa only [blowupExceptionalClass_def, inv_zpow'] using hM)
  let N := (Scheme.Modules.pullback ι).obj M.obj
  have h : M.obj ⊗ D.pushforwardSubscheme ≅ (pushforward ι).obj N := by
    simpa only [N, FiniteLocallyFreeSheaf.pullback_obj_obj, ObjectProperty.ιOfLE_obj_obj] using
      D.tensorPushforwardSubschemeIso ((InvertibleSheaf.toFiniteLocallyFree J.blowup).obj M)
  let c := (cohomologyFunctor _ q).mapIso h ≪≫ cohomologyPushforwardIso ι N q
  let c' := (cohomologyFunctor _ q).mapIso ((e.hom.pullbackIsoPushforwardInv).app N) ≪≫
    cohomologyPushforwardIso (inv e.hom) N q
  let d := (cohomologyFunctor _ q).mapIso (((Scheme.Modules.pullbackComp e.hom ι).app M.obj) ≪≫ t)
  exact ⟨(c ≪≫ c'.symm ≪≫ d).addCommGroupIsoToAddEquiv⟩

/-- The once-twisted exceptional quotient is acyclic, over any residue field. -/
theorem subsingleton_cohomology_pointBlowup_exceptional_quotient_of_twist_one
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (a : LineBundleClass X) (M : InvertibleSheaf Y)
    (hM : LineBundleClass.mk M = LineBundleClass.pullback π a * (Iₚ).blowupExceptionalClass)
    (q : ℕ) : Subsingleton (Cohomology (M.obj ⊗ (E).pushforwardSubscheme) q) := by
  generalize hI : Iₚ = I at M hM ⊢
  have hJ := (X.ker_fromSpecResidueField_eq_vanishingIdeal p).trans hI
  clear hI
  subst I
  obtain ⟨e⟩ := nonempty_cohomologyAddEquiv_pointBlowup_exceptional_quotient hp hdim a 1 M
    (by simpa only [zpow_one] using hM) q
  let b := Pi.basisFun (X.residueField p) (Fin 2)
  refine @Function.Injective.subsingleton _ _ _ e.injective ?_
  cases q with
  | zero =>
    exact TauCeti.SymmetricAlgebra.subsingleton_cohomology_zero_twistingSheaf_of_neg
      (by decide : (-1 : ℤ) < 0) b
  | succ q =>
    exact b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt
      (m := -1) (by decide) (Nat.succ_pos q)

end AlgebraicGeometry.Scheme.IdealSheafData

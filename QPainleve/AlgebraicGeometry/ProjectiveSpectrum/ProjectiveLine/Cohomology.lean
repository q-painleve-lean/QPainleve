/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic

import QPainleve.AlgebraicGeometry.Cohomology.CartierPairing
import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine

/-!
# Cohomology on a projective-line subscheme

The cohomology of a line bundle restricted to a projective-line subscheme
agrees with the cohomology of the twist of the same degree on the projective
line. In particular, first cohomology vanishes in degrees at least `-1`.
-/

public section

open CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open LineBundleClass

variable {X : Scheme.{u}} {E : X.IdealSheafData}

/-- Restricting a line bundle to a projective-line subscheme and viewing it on the
ambient scheme gives the base-linear cohomology of the twist of the same degree. -/
noncomputable def cohomologyTensorPushforwardSubschemeEquivTwistingSheaf
    (E : X.IdealSheafData)
    {k : Type u} [Field k] [X.Over (Spec (.of k))]
    (e : projectiveLine k ≅ E.subscheme) [e.hom.IsOver (Spec (.of k))]
    (M : InvertibleSheaf X) (q : ℕ) :
    Cohomology (M.obj ⊗ E.pushforwardSubscheme) q ≃ₗ[k]
      Cohomology (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k))
        (intersectionNumber k (e.hom ≫ E.subschemeι) (LineBundleClass.mk M))) q := by
  let i := E.subschemeι
  let N := (Scheme.Modules.pullback i).obj M.obj
  let P := (InvertibleSheaf.pullback (e.hom ≫ i)).obj M
  let d := intersectionNumber k (e.hom ≫ i) (LineBundleClass.mk M)
  have hP : InvertibleSheaf.eulerDegree k P = d := by
    simp only [d, P, intersectionNumber_def, pullback_mk, eulerDegree_mk]
  let t := ((projectiveLine.nonempty_iso_twistingSheaf_iff k P d).mpr hP).some
  let t' := (Scheme.Modules.pullbackComp e.hom i).app M.obj ≪≫
    eqToIso (InvertibleSheaf.pullback_obj_obj (e.hom ≫ i) M).symm ≪≫ t
  exact (E.cohomologyTensorRestrictionEquiv k M q).trans <|
    (e.hom.cohomologyPullbackBaseLinearEquivOfIsIso k N q).symm.trans <|
    cohomologyBaseLinearEquivOfIso k t' q

/-- The restriction of a line bundle of degree at least `-1` to a projective-line
subscheme has no first cohomology, also when viewed as a sheaf on the ambient scheme. -/
theorem subsingleton_cohomology_one_tensor_pushforwardSubscheme_of_projectiveLine
    (M : InvertibleSheaf X) {κ : Type u} [Field κ] (e : projectiveLine κ ≅ E.subscheme)
    (hdeg : -1 ≤ intersectionNumber κ (e.hom ≫ E.subschemeι) (LineBundleClass.mk M)) :
    Subsingleton (Cohomology (M.obj ⊗ E.pushforwardSubscheme) 1) := by
  let i := E.subschemeι
  let N := (Scheme.Modules.pullback i).obj M.obj
  let P := (InvertibleSheaf.pullback (e.hom ≫ i)).obj M
  let d := intersectionNumber κ (e.hom ≫ i) (LineBundleClass.mk M)
  have hP : InvertibleSheaf.eulerDegree κ P = d := by
    simp only [d, P, intersectionNumber_def, pullback_mk, eulerDegree_mk]
  obtain ⟨t⟩ := (projectiveLine.nonempty_iso_twistingSheaf_iff κ P d).mpr hP
  let t' := ((Scheme.Modules.pullbackComp e.hom i).app M.obj) ≪≫
    eqToIso (InvertibleSheaf.pullback_obj_obj (e.hom ≫ i) M).symm ≪≫ t
  have := E.isIso_tensorRestrictionHom M
  let c := (cohomologyFunctor _ 1).mapIso (asIso (E.tensorRestrictionHom M)) ≪≫
    cohomologyPushforwardIso i N 1
  let c' := (cohomologyFunctor _ 1).mapIso ((e.hom.pullbackIsoPushforwardInv).app N) ≪≫
    cohomologyPushforwardIso (inv e.hom) N 1
  let b := Pi.basisFun κ (Fin 2)
  have hd : -1 ≤ d := hdeg
  have hz : Subsingleton (Cohomology (Proj.twistingSheaf
      (TauCeti.SymmetricAlgebra.homogeneousSubmodule κ (Fin 2 → κ)) d) 1) :=
    b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt (by omega : -2 < d)
      Nat.one_pos
  let h := c ≪≫ c'.symm ≪≫ (cohomologyFunctor _ 1).mapIso t'
  exact @Function.Injective.subsingleton _ _ _ h.addCommGroupIsoToAddEquiv.injective hz

end AlgebraicGeometry.Scheme.IdealSheafData

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Splitting
public import QPainleve.AlgebraicGeometry.RelativeProj.Isomorphism
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.Quasicoherent

/-!
# Split projective bundles over the projective line

The projectivization of a rank-two bundle on the projective line is isomorphic
over the base to the relative projective spectrum of the symmetric algebra of
a direct sum of two twists. This expresses the ruled surface in terms of the
splitting degrees of its bundle.
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.projectiveLine

universe u

variable {k : Type u} [Field k]

local notation "P" => projectiveLine k
local notation "L" => Proj.symmetricAlgebraTwistingBundle k (Fin 2 → k)
local notation "F[" E "]" =>
  Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent P) (ObjectProperty.FullSubcategory.obj E)
local notation "A[" E "]" =>
  Functor.obj (gradedSymmetricAlgebra P) F[E]
local notation "line[" a "]" => Functor.obj (InvertibleSheaf.toFixedRankOne P) (L a)
local notation "split[" a "," b "]" =>
  FiniteLocallyFreeSheaf.FixedRank.biprod line[a] line[b]

/-- The quotient-convention projectivization of a rank-two bundle over `ℙ¹`
is a split projective bundle over `ℙ¹`, with summand degrees `a ≥ b`. -/
theorem exists_relativeProj_iso_biprod_twistingSheaf (E : FiniteLocallyFreeSheaf.FixedRank P 2) :
    let A := A[E]
    ∃ (a b : ℤ), b ≤ a ∧
      let B := A[split[a,b]]
      ∃ e : A.obj.relativeProj ≅ B.obj.relativeProj,
        e.hom ≫ B.obj.relativeProjToBase = A.obj.relativeProjToBase := by
  obtain ⟨a, b, hba, ⟨s⟩⟩ := exists_iso_biprod_twistingSheaf E
  let B := split[a,b]
  have s' : E.obj.obj ≅ line[a].obj.obj ⊞ line[b].obj.obj := by
    simpa only [InvertibleSheaf.toFixedRankOne_obj_obj, ObjectProperty.ιOfLE_obj_obj,
      Proj.symmetricAlgebraTwistingBundle_obj] using s
  let e : B.obj ≅ E.obj := ObjectProperty.isoMk _
    (line[a].biprodObjIso line[b] ≪≫ s'.symm)
  let eSym := (gradedSymmetricAlgebra P).mapIso
    ((FiniteLocallyFreeSheaf.toQuasicoherent P).mapIso e)
  let eAlg := (ObjectProperty.ι _).mapIso eSym
  exact ⟨a, b, hba, CommMon.relativeProjMapIso eAlg,
    CommMon.relativeProjMapIso_hom_relativeProjToBase _⟩

end TauCeti.AlgebraicGeometry.projectiveLine

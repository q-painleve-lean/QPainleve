/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.Surjective

import QPainleve.AlgebraicGeometry.Modules.GradedAlgebra.DirectSum
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Pullback of graded symmetric algebras

Pullback along a scheme morphism commutes with the graded symmetric algebra of a
quasicoherent sheaf. The comparison extends the canonical map on degree-one
generators. Keeping the grading makes the comparison available to relative Proj.

The proof uses Tau Ceti's ungraded comparison
`toQuasicoherentAlgebra_map_gradedSymmetricAlgebraLift_pullback`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.AlgebraicGeometry

universe u

open GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

local notation "Sym" => gradedSymmetricAlgebra

private def pullbackGradedSymmetricAlgebraDegreeOneIso (F : QuasicoherentSheaf X) :
    degreeOne.obj ((GradedQuasicoherentAlgebra.pullback f).obj ((Sym X).obj F)) ≅
      (QuasicoherentSheaf.pullback f).obj F :=
  (pullbackDegreeIso f 1).app ((Sym X).obj F) ≪≫
    (QuasicoherentSheaf.pullback f).mapIso ((gradedSymmetricAlgebraDegreeOneIso X).app F)

private theorem isIso_lift_id_pullback_gradedSymmetricAlgebra (F : QuasicoherentSheaf X) :
    IsIso (gradedSymmetricAlgebraLift
      (𝟙 (degreeOne.obj ((GradedQuasicoherentAlgebra.pullback f).obj ((Sym X).obj F))))) := by
  let A := (Sym X).obj F
  have : IsIso (gradedSymmetricAlgebraLift (𝟙 (degreeOne.obj A))) := by
    rw [← gradedSymmetricAlgebraAdjunction_counit_app]
    exact (gradedSymmetricAlgebraAdjunction X).isIso_counit_app_of_iso (Iso.refl A)
  have h : IsIso (toQuasicoherentAlgebra.map (gradedSymmetricAlgebraLift
      (𝟙 (degreeOne.obj ((GradedQuasicoherentAlgebra.pullback f).obj A))))) := by
    rw [toQuasicoherentAlgebra_map_gradedSymmetricAlgebraLift_pullback]
    infer_instance
  exact isIso_of_reflects_iso _ toQuasicoherentAlgebra

/-- The graded symmetric algebra of a pulled-back quasicoherent sheaf identifies
with the pullback of its graded symmetric algebra. -/
def pullbackGradedSymmetricAlgebraIso (F : QuasicoherentSheaf X) :
    (Sym Y).obj ((QuasicoherentSheaf.pullback f).obj F) ≅
      (GradedQuasicoherentAlgebra.pullback f).obj ((Sym X).obj F) := by
  have := isIso_lift_id_pullback_gradedSymmetricAlgebra f F
  exact (Sym Y).mapIso (pullbackGradedSymmetricAlgebraDegreeOneIso f F).symm ≪≫
    asIso (gradedSymmetricAlgebraLift (𝟙 _))

/-- The pullback comparison is the graded algebra map extending the canonical
identification of degree-one generators. -/
theorem pullbackGradedSymmetricAlgebraIso_hom (F : QuasicoherentSheaf X) :
    (pullbackGradedSymmetricAlgebraIso f F).hom = gradedSymmetricAlgebraLift
      ((QuasicoherentSheaf.pullback f).map ((gradedSymmetricAlgebraDegreeOneIso X).inv.app F) ≫
        (pullbackDegreeIso f 1).inv.app ((Sym X).obj F)) := by
  rw [pullbackGradedSymmetricAlgebraIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    gradedSymmetricAlgebra_map_comp_lift, Category.comp_id]
  rfl

/-- The pullback comparison is natural in the quasicoherent sheaf. -/
def pullbackGradedSymmetricAlgebraNatIso :
    QuasicoherentSheaf.pullback f ⋙ Sym Y ≅ Sym X ⋙ GradedQuasicoherentAlgebra.pullback f :=
  NatIso.ofComponents (pullbackGradedSymmetricAlgebraIso f) fun {F G} g ↦ by
    simp only [Functor.comp_map, pullbackGradedSymmetricAlgebraIso_hom,
      gradedSymmetricAlgebra_map_comp_lift, gradedSymmetricAlgebraLift_comp, Category.assoc]
    congr 1
    have h := (pullbackDegreeIso f 1).inv.naturality ((Sym X).map g)
    simp only [Functor.comp_map] at h
    rw [← h]
    have h' := (gradedSymmetricAlgebraDegreeOneIso X).inv.naturality g
    simp only [Functor.id_map, Functor.comp_map] at h'
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, h']

/-- Each component of the natural comparison is the graded pullback isomorphism. -/
@[simp]
theorem pullbackGradedSymmetricAlgebraNatIso_app (F : QuasicoherentSheaf X) :
    (pullbackGradedSymmetricAlgebraNatIso f).app F = pullbackGradedSymmetricAlgebraIso f F :=
  (rfl)

end TauCeti.AlgebraicGeometry

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeProj.Map

import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Maps

/-!
# Relative projective spectra of isomorphic graded algebras

Applying `CategoryTheory.CommMon.relativeProjMap` to both directions of a graded
algebra isomorphism gives a relative projective isomorphism over the base. On each
affine chart it is induced by the isomorphism on graded sections.
-/

public noncomputable section

open AlgebraicGeometry

namespace CategoryTheory.CommMon

universe u

variable {X : Scheme.{u}} {A B : CommMon (GradedObject ℕ X.Modules)}

/-- The image of the irrelevant ideal under the graded section map of an
isomorphism contains the target irrelevant ideal. -/
theorem irrelevant_le_map_gradedSectionsGradedHom_of_iso (e : A ≅ B) (U : X.Opens) :
    HomogeneousIdeal.irrelevant (B.gradedSectionsGrading U) ≤
      (HomogeneousIdeal.irrelevant (A.gradedSectionsGrading U)).map
        (gradedSectionsGradedHom e.hom U) := by
  apply HomogeneousIdeal.irrelevant_le_map_of_surjective
  intro b
  exact ⟨gradedSectionsGradedHom e.inv U b, by
    rw [← GradedRingHom.comp_apply, ← gradedSectionsGradedHom_comp, e.inv_hom_id,
      gradedSectionsGradedHom_id, GradedRingHom.id_apply]⟩

variable [∀ n, (A.X n).IsQuasicoherent] [∀ n, (B.X n).IsQuasicoherent]

private theorem relativeProjMap_eq_id {f : A ⟶ A} (hf : f = 𝟙 A)
    (h : ∀ U : X.Opens, IsAffineOpen U →
      HomogeneousIdeal.irrelevant (A.gradedSectionsGrading U) ≤
        (HomogeneousIdeal.irrelevant (A.gradedSectionsGrading U)).map
          (gradedSectionsGradedHom f U)) :
    relativeProjMap f h = 𝟙 A.relativeProj := by
  subst f
  exact relativeProjMap_id h

/-- Relative `Proj` sends a graded algebra isomorphism to the contravariant isomorphism
of schemes given by the graded map on each affine chart. -/
def relativeProjMapIso (e : A ≅ B) : B.relativeProj ≅ A.relativeProj where
  hom := relativeProjMap e.hom fun U _ ↦ irrelevant_le_map_gradedSectionsGradedHom_of_iso e U
  inv := relativeProjMap e.inv fun U _ ↦ irrelevant_le_map_gradedSectionsGradedHom_of_iso e.symm U
  hom_inv_id := by
    rw [← relativeProjMap_comp e.inv e.hom _ _
      (fun U _ ↦ irrelevant_le_map_gradedSectionsGradedHom_of_iso (e.symm ≪≫ e) U)]
    exact relativeProjMap_eq_id e.inv_hom_id _
  inv_hom_id := by
    rw [← relativeProjMap_comp e.hom e.inv _ _
      (fun U _ ↦ irrelevant_le_map_gradedSectionsGradedHom_of_iso (e ≪≫ e.symm) U)]
    exact relativeProjMap_eq_id e.hom_inv_id _

/-- The inverse projective comparison is induced by the inverse graded isomorphism. -/
@[simp]
theorem relativeProjMapIso_symm (e : A ≅ B) :
    (relativeProjMapIso e).symm = relativeProjMapIso e.symm := by
  apply Iso.ext
  rfl

/-- On the chart over an affine open, the isomorphism is induced by the map
on graded sections there. -/
@[reassoc]
theorem relativeProjCover_f_relativeProjMapIso_hom (e : A ≅ B) (U : X.AffineZariskiSite) :
    B.relativeProjCover.f U ≫ (relativeProjMapIso e).hom =
      Proj.map (gradedSectionsGradedHom e.hom U.toOpens)
        (irrelevant_le_map_gradedSectionsGradedHom_of_iso e U.toOpens) ≫
        A.relativeProjCover.f U := by
  rw [relativeProjMapIso, relativeProjCover_f_relativeProjMap, relativeProjFunctorMap_app]
  rfl

/-- The relative projective isomorphism is over the base scheme. -/
@[reassoc (attr := simp)]
theorem relativeProjMapIso_hom_relativeProjToBase (e : A ≅ B) :
    (relativeProjMapIso e).hom ≫ A.relativeProjToBase = B.relativeProjToBase :=
  relativeProjMap_relativeProjToBase _ _

end CategoryTheory.CommMon

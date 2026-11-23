/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus

/-!
# Ratios of sections of a line bundle

A nowhere vanishing section is a frame for an invertible sheaf. Its section
ratios commute with restriction and give units for changes of frame.
-/

public noncomputable section

open CategoryTheory
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]

/-- The coefficient of a local section in the frame given by a nowhere vanishing
section over the same open. -/
def sectionRatio {U : X.Opens} (t s : Γ(M, U)) (hs : U ≤ M.nonvanishingLocus s) :
    Γ(X, U) :=
  (M.surjective_smul_of_le_nonvanishingLocus hs t).choose

/-- Multiplying the ratio by its denominator recovers the numerator. -/
@[simp]
theorem sectionRatio_smul {U : X.Opens} (t s : Γ(M, U))
    (hs : U ≤ M.nonvanishingLocus s) : M.sectionRatio t s hs • s = t :=
  (M.surjective_smul_of_le_nonvanishingLocus hs t).choose_spec

/-- A ratio is characterized by multiplication by its denominator. -/
theorem sectionRatio_eq_iff {U : X.Opens} {t s : Γ(M, U)}
    (hs : U ≤ M.nonvanishingLocus s) {a : Γ(X, U)} :
    M.sectionRatio t s hs = a ↔ a • s = t := by
  constructor
  · rintro rfl
    exact M.sectionRatio_smul t s hs
  · intro ha
    exact M.injective_smul_of_le_nonvanishingLocus hs ((M.sectionRatio_smul t s hs).trans ha.symm)

/-- The ratio of a frame to itself is one. -/
@[simp]
theorem sectionRatio_self {U : X.Opens} (s : Γ(M, U))
    (hs : U ≤ M.nonvanishingLocus s) : M.sectionRatio s s hs = 1 :=
  (M.sectionRatio_eq_iff hs).mpr (one_smul _ _)

/-- Restriction commutes with taking ratios. -/
theorem map_sectionRatio {U V : X.Opens} (i : V ⟶ U) (t s : Γ(M, U))
    (hs : U ≤ M.nonvanishingLocus s) :
    X.presheaf.map i.op (M.sectionRatio t s hs) =
      M.sectionRatio (M.presheaf.map i.op t) (M.presheaf.map i.op s)
        (by rw [M.nonvanishingLocus_map]; exact le_inf le_rfl (i.le.trans hs)) := by
  symm
  apply (M.sectionRatio_eq_iff _).mpr
  rw [← M.map_smul, M.sectionRatio_smul]

/-- The ratio of two frames is a unit. -/
theorem isUnit_sectionRatio {U : X.Opens} (t s : Γ(M, U))
    (ht : U ≤ M.nonvanishingLocus t) (hs : U ≤ M.nonvanishingLocus s) :
    IsUnit (M.sectionRatio t s hs) := by
  refine .of_mul_eq_one (M.sectionRatio s t ht) ?_
  apply M.injective_smul_of_le_nonvanishingLocus hs
  simp only [mul_comm (M.sectionRatio t s hs), mul_smul, M.sectionRatio_smul, one_smul]

/-- Ratios multiply through an intermediate frame. -/
theorem sectionRatio_mul_sectionRatio {U : X.Opens} (t s r : Γ(M, U))
    (hs : U ≤ M.nonvanishingLocus s) (hr : U ≤ M.nonvanishingLocus r) :
    M.sectionRatio s r hr * M.sectionRatio t s hs = M.sectionRatio t r hr := by
  symm
  apply (M.sectionRatio_eq_iff hr).mpr
  rw [mul_comm, mul_smul, sectionRatio_smul, sectionRatio_smul]

end AlgebraicGeometry.Scheme.Modules

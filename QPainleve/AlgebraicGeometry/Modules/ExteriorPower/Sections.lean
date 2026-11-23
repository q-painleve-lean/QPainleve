/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Localization
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Basic
import TauCeti.AlgebraicGeometry.Modules.LocallyBijective

/-!
# Sections of exterior powers

The sheafification map takes wedges of sections to sections of the exterior power
sheaf. For a quasicoherent sheaf on an affine open this map is bijective. The proof
uses Tau Ceti's exterior-power localization theorem and follows its comparison for
sections of symmetric powers in `Modules.SymmetricPower.Sections`.
-/

public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}

private abbrev exteriorPresheaf (n : ℕ) :=
  (PresheafOfModulesOfCommRing.exteriorPower (R := X.presheaf) n).obj M.val

/-- A section of the sectionwise exterior power gives a section of the exterior power sheaf. -/
def exteriorPowerSections (U : X.Opens) (n : ℕ) :
    (PresheafOfModulesOfCommRing.obj (R := X.presheaf) M.val (op U)).exteriorPower n ⟶
      (sectionsFunctor U).obj ((SheafOfModules.exteriorPower X.sheaf n).obj M) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (exteriorPresheaf M n)).app' (op U) ≫
    (sectionsFunctor U).map (SheafOfModules.exteriorPowerIso n M).inv

/-- For a quasicoherent module the comparison on every affine open is bijective. -/
theorem bijective_exteriorPowerSections [M.IsQuasicoherent] (hU : IsAffineOpen U) (n : ℕ) :
    Function.Bijective (M.exteriorPowerSections U n) := by
  refine (ConcreteCategory.bijective_of_isIso
    ((sectionsFunctor U).mapIso (SheafOfModules.exteriorPowerIso n M).symm).hom).comp ?_
  exact hU.bijective_sheafificationAdjunction_unit_app_of_isLocalizedModule _
    fun f ↦ M.isLocalizedModule_exteriorPower_map_basicOpen hU f n

/-- Restriction sends the section determined by a wedge to the wedge of the restrictions. -/
theorem restrict_exteriorPowerSections_mk (i : V ⟶ U) (n : ℕ) (m : Fin n → Γ(M, U)) :
    ((SheafOfModules.exteriorPower X.sheaf n).obj M).val.map i.op
        (M.exteriorPowerSections U n (ModuleCat.exteriorPower.mk m)) =
      M.exteriorPowerSections V n
        (ModuleCat.exteriorPower.mk (fun j ↦ M.val.map i.op (m j))) := by
  simp only [exteriorPowerSections]
  erw [← PresheafOfModules.naturality_apply (SheafOfModules.exteriorPowerIso n M).inv.val,
    ← PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (exteriorPresheaf M n)), PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk]
  rfl

end AlgebraicGeometry.Scheme.Modules

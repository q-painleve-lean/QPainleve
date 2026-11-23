/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.InternalHom.GlobalSections
public import TauCeti.AlgebraicGeometry.Modules.Sections

/-!
# Global sections of internal Hom sheaves

The unit-section equivalence and the closed monoidal adjunction identify global sections
of the internal Hom with sheaf morphisms. Addition and multiplication by global functions
correspond to the additive and scalar operations on morphisms.
-/

public noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed
open TauCeti

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Sections of the internal Hom correspond to morphisms of module sheaves. -/
def internalHomSectionsEquiv : Γ((ihom M).obj N, ⊤) ≃ (M ⟶ N) :=
  (unitHomEquivTop ((ihom M).obj N)).symm.trans (curryHomEquiv' (X := M) (Y := N)).symm

/-- The represented morphism is the uncurried global section. -/
theorem internalHomSectionsEquiv_apply (s : Γ((ihom M).obj N, ⊤)) :
    internalHomSectionsEquiv s =
      uncurry' (C := X.Modules) ((unitHomEquivTop ((ihom M).obj N)).symm s) :=
  (rfl)

@[simp]
theorem internalHomSectionsEquiv_zero : internalHomSectionsEquiv (M := M) (N := N) 0 = 0 := by
  let : MonoidalPreadditive X.Modules := TauCeti.SheafOfModules.monoidalPreadditive X.sheaf
  let e : (𝟙_ X.Modules ⟶ (ihom M).obj N) ≃ Γ((ihom M).obj N, ⊤) := unitHomEquivTop _
  have h : e.symm 0 = 0 := e.symm_apply_eq.mpr (unitHomEquivTop_zero _).symm
  rw [internalHomSectionsEquiv_apply]
  -- Use the same bundled morphism type for the unit as in the zero calculation.
  change uncurry' (C := X.Modules) (e.symm 0) = 0
  rw [h]
  simp [uncurry', uncurry_eq]

@[simp]
theorem internalHomSectionsEquiv_add (s t : Γ((ihom M).obj N, ⊤)) :
    internalHomSectionsEquiv (s + t) = internalHomSectionsEquiv s + internalHomSectionsEquiv t := by
  let : MonoidalPreadditive X.Modules := TauCeti.SheafOfModules.monoidalPreadditive X.sheaf
  let e : (𝟙_ X.Modules ⟶ (ihom M).obj N) ≃ Γ((ihom M).obj N, ⊤) := unitHomEquivTop _
  have hAdd (f g : 𝟙_ X.Modules ⟶ (ihom M).obj N) : e (f + g) = e f + e g := by
    exact (unitHomEquivTop_apply ((ihom M).obj N) (f + g)).trans
      (congrArg₂ (· + ·) (unitHomEquivTop_apply ((ihom M).obj N) f).symm
        (unitHomEquivTop_apply ((ihom M).obj N) g).symm)
  have h : e.symm (s + t) = e.symm s + e.symm t := by
    apply e.injective
    simp only [Equiv.apply_symm_apply, hAdd]
  simp only [internalHomSectionsEquiv_apply]
  -- Use the monoidal unit in the source of every morphism before rewriting the sum.
  change uncurry' (C := X.Modules) (e.symm (s + t)) =
    uncurry' (C := X.Modules) (e.symm s) + uncurry' (C := X.Modules) (e.symm t)
  rw [h]
  simp [uncurry', uncurry_eq, MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp,
    Preadditive.comp_add]

/-- Multiplication of a section by a global function scales the represented morphism. -/
theorem internalHomSectionsEquiv_smul (r : Γ(X, ⊤)) (s : Γ((ihom M).obj N, ⊤)) :
    internalHomSectionsEquiv (r • s) = internalHomSectionsEquiv s ≫ N.globalSectionsSmul r := by
  let H : X.Modules := (ihom M).obj N
  let e := unitHomEquivTop H
  have h : e.symm (r • s) = e.symm s ≫ H.globalSectionsSmul r := by
    apply e.injective
    simp only [e, Equiv.apply_symm_apply, unitHomEquivTop_comp]
    have htop : (⊤ : X.Opens).leTop.op = 𝟙 _ := Subsingleton.elim _ _
    simp [globalSectionsSmul_app, htop]
  simp only [internalHomSectionsEquiv_apply]
  rw [h]
  dsimp only [H]
  rw [← ihom_map_globalSectionsSmul]
  simp only [uncurry', Category.assoc]
  exact congrArg ((ρ_ M).inv ≫ ·)
    (uncurry_natural_right (C := X.Modules) (e.symm s) (N.globalSectionsSmul r))

end AlgebraicGeometry.Scheme.Modules

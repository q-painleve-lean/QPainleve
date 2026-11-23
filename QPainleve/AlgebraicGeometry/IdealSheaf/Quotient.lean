/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
import TauCeti.AlgebraicGeometry.Modules.SchemeTheoreticSupport

/-!
# Quotients of ideals by products

The quotient of an ideal sheaf by its product with another ideal sheaf
is the direct image of its restriction to the closed subscheme of the
second ideal. This describes the graded pieces of a filtration by products.
-/

public section

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

noncomputable section

/-- The inclusion of one ideal sheaf into a larger ideal sheaf. -/
def sheafHomOfLE {I J : X.IdealSheafData} (h : I ≤ J) : I.sheaf ⟶ J.sheaf :=
  J.sheafLift I.sheafι fun U s ↦ sections_mono h U (I.sheafι_app_mem U s)

/-- Composing the ideal-sheaf inclusion with the inclusion into the structure sheaf
recovers the inclusion of the smaller ideal. -/
@[simp]
theorem sheafHomOfLE_sheafι {I J : X.IdealSheafData} (h : I ≤ J) :
    sheafHomOfLE h ≫ (J.sheafι : J.sheaf ⟶ Scheme.Modules.unit X) = I.sheafι :=
  J.sheafLift_ι _ _

instance {I J : X.IdealSheafData} (h : I ≤ J) : Mono (sheafHomOfLE h) :=
  mono_of_mono_fac (sheafHomOfLE_sheafι h)

/-- The quotient of an ideal sheaf by its product with a second ideal is the
direct image of its restriction to the closed subscheme defined by the second
ideal. -/
theorem isIso_unit_app_cokernel_sheafHomOfLE_mul (I J : X.IdealSheafData) :
    IsIso ((pullbackPushforwardAdjunction J.subschemeι).unit.app
      (cokernel (sheafHomOfLE (mul_le_of_le_one_right' (a := I) (b := J) le_top)))) := by
  let j := sheafHomOfLE (mul_le_of_le_one_right' (a := I) (b := J) le_top)
  let q := cokernel.π j
  apply isIso_unit_app_of_ker_ideal_le_annihilator
  intro U
  rw [J.ker_subschemeι]
  intro a ha
  refine Module.mem_annihilator.mpr fun t ↦ ?_
  obtain ⟨s, rfl⟩ := Hom.app_surjective_of_epi_of_isAffineOpen q U.val U.property t
  let b : Γ(X, U) := I.sheafι.app U s
  have hb : b ∈ I.sections U := I.sheafι_app_mem U s
  have hmem : a * b ∈ (I * J).sections U := by
    rw [I.sections_eq_ideal U] at hb
    rw [sections_eq_ideal, ideal_mul, Pi.mul_apply]
    exact (mul_comm b a) ▸ Ideal.mul_mem_mul hb ha
  let w := (I * J).sectionMk (a * b) hmem
  have hw : j.app U w = a • s := by
    apply I.sheafι_app_injective U
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f : (I * J).sheaf ⟶ Scheme.Modules.unit X ↦ Scheme.Modules.Hom.app f U)
        (sheafHomOfLE_sheafι (mul_le_of_le_one_right' (a := I) (b := J) le_top))) w
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, sheafι_app_sectionMk] at h
    exact h.trans ((I.sheafι.app_smul a s).trans rfl).symm
  rw [← q.app_smul, ← hw]
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f : (I * J).sheaf ⟶ cokernel j ↦ Scheme.Modules.Hom.app f U)
      (cokernel.condition j)) w
  simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app,
    ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply] using h

end

end AlgebraicGeometry.Scheme.IdealSheafData

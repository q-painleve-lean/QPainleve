/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.InternalHom.Sections
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Pullback of sections of internal Hom

An isomorphism of schemes identifies sections of internal Hom by pulling back the
represented morphisms. Isomorphisms of the two coefficient sheaves allow this
comparison to use any specified models for the pulled-back sheaves.
-/

public noncomputable section

open CategoryTheory MonoidalClosed TauCeti

namespace AlgebraicGeometry.Scheme.Hom

universe u

open Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
  (R : Type u) [CommRing R] [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  [f.IsOver (Spec (.of R))] {M N : Y.Modules} {M' N' : X.Modules}
  (a : (pullback f).obj M ≅ M') (b : (pullback f).obj N ≅ N')

/-- The linear equivalence on internal Hom sections induced by an isomorphism
of schemes and the specified identifications of its pulled-back sheaves. -/
def pullbackInternalHomSectionsLinearEquiv :
    Γ((ihom M).obj N, ⊤) ≃ₗ[R] Γ((ihom M').obj N', ⊤) := by
  let h := (Functor.FullyFaithful.ofFullyFaithful (pushforward (inv f))).ofIso
    (f.pullbackIsoPushforwardInv).symm
  let e := internalHomSectionsEquiv.trans
    (h.homEquiv.trans ((a.homCongr b).trans internalHomSectionsEquiv.symm))
  have he (s : Γ((ihom M).obj N, ⊤)) :
      internalHomSectionsEquiv (e s) =
        a.inv ≫ (pullback f).map (internalHomSectionsEquiv s) ≫ b.hom := by
    simp [e]
  refine { toEquiv := e, map_add' := ?_, map_smul' := ?_ }
  · intro s t
    apply internalHomSectionsEquiv.injective
    simp [he, Preadditive.add_comp, Preadditive.comp_add]
  · intro r s
    apply internalHomSectionsEquiv.injective
    have hr : f.appTop (baseRingToGlobalSections R Y r) = baseRingToGlobalSections R X r := by
      rw [baseRingToGlobalSections_apply, baseRingToGlobalSections_apply,
        ← comp_over f (Spec (.of R)), Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
    simp only [Equiv.toFun_as_coe, he, base_smul_globalSections, internalHomSectionsEquiv_smul,
      RingHom.id_apply, Functor.map_comp, pullback_map_globalSectionsSmul, hr, Category.assoc]
    rw [globalSectionsSmul_naturality]

/-- Under pullback, an internal Hom section represents the pullback of its morphism
conjugated by the coefficient isomorphisms. -/
@[simp]
theorem internalHomSectionsEquiv_pullbackInternalHomSectionsLinearEquiv
    (s : Γ((ihom M).obj N, ⊤)) :
    internalHomSectionsEquiv (f.pullbackInternalHomSectionsLinearEquiv R a b s) =
      a.inv ≫ (pullback f).map (internalHomSectionsEquiv s) ≫ b.hom := by
  simp [pullbackInternalHomSectionsLinearEquiv]

end AlgebraicGeometry.Scheme.Hom

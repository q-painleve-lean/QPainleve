/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.ZeroLocus
public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence

/-!
# Cokernels of embeddings of line bundles

Twisting an embedding by the dual of its target gives an embedding into the structure sheaf.
Its cokernel is the structure sheaf of its image ideal's zero scheme. Twisting back describes
the original cokernel, including when the zero scheme is empty.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

open CategoryTheory.Limits

/-- The cokernel of an embedding of line bundles is the target line bundle
restricted to the zero scheme of the corresponding functional. -/
def cokernelIsoTensorPushforwardImageIdeal {X : Scheme.{u}}
    (L K : InvertibleSheaf X) (f : L.obj ⟶ K.obj) [Mono f] :
    cokernel f ≅ K.obj ⊗ (L.twistedToUnit K f).imageIdealSheaf.pushforwardSubscheme := by
  let φ := L.twistedToUnit K f
  let I := φ.imageIdealSheaf
  let e : cokernel φ ≅ I.pushforwardSubscheme :=
    cokernel.mapIso φ I.sheafι φ.imageIdealSheafIso (Iso.refl _)
        (by simpa only [Iso.refl_hom, Category.comp_id] using φ.imageIdealSheafIso_hom_ι.symm) ≪≫
      (cokernelIsCokernel _).coconePointUniqueUpToIso
        I.shortExact_toPushforwardSubscheme.gIsCokernel
  let t := tensorRightDualEquivalence K
  let h : (t.functor ⋙ t.inverse).obj (cokernel f) =
      (cokernel f ⊗ (dual K).obj) ⊗ K.obj := by
    simp only [t, Functor.comp_obj, tensorRightDualEquivalence_functor,
      tensorRightDualEquivalence_inverse]
    rfl
  exact t.unitIso.app (cokernel f) ≪≫ eqToIso h ≪≫
    (tensorRight K.obj).mapIso ((L.cokernelTwistedToUnitIso K f).symm ≪≫ e) ≪≫ β_ _ _

end TauCeti.AlgebraicGeometry.InvertibleSheaf

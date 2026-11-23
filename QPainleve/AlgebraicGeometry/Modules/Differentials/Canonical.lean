/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Forms
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Ramification
public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Pullback.Quasicoherent
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.ZeroLocus
import TauCeti.AlgebraicGeometry.LineBundle.Hom
import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Image
import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Invertible
import QPainleve.AlgebraicGeometry.VectorBundle.FittingIdeal

/-!
# Ramification ideals and canonical bundles

For a morphism between smooth schemes of the same relative dimension, the ramification
ideal is the ideal of the induced map on top differential forms. In particular, an
effective Cartier ramification ideal on an integral source gives the canonical class
formula. For a blowup this identifies the canonical correction once the ramification
ideal has been computed on its charts.

The construction uses Tau Ceti's `cotangentMap`, `differentialForms` and exterior power
pullback comparison. It extends the invertible-differentials comparison in Tau Ceti's
`ramificationIdealSheaf_eq_imageIdealSheaf_twistedToUnit` to equal relative dimension.
-/

public section

open AlgebraicGeometry CategoryTheory Limits TauCeti.AlgebraicGeometry

namespace QPainleve

universe u

noncomputable section

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of R))]

/-- The canonical bundle of a smooth scheme of relative dimension `n`, as an
invertible sheaf of top differential forms. -/
def canonicalBundle (X : Scheme.{u}) [X.Over (Spec (.of R))] (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] : InvertibleSheaf X :=
  ⟨differentialForms R (X ↘ Spec (.of R)) n, isInvertible_differentialForms R X n⟩

/-- The underlying sheaf of the canonical bundle is the sheaf of top forms. -/
@[simp]
theorem canonicalBundle_obj (X : Scheme.{u}) [X.Over (Spec (.of R))] (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] :
    (canonicalBundle R X n).obj = differentialForms R (X ↘ Spec (.of R)) n := (rfl)

variable (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of R))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (.of R))]

/-- Pullback on the canonical bundles, induced by the top exterior power of the cotangent map. -/
def topDifferentialFormsMap :
    ((InvertibleSheaf.pullback f).obj (canonicalBundle R Y n)).obj ⟶
      (canonicalBundle R X n).obj :=
  eqToHom (by rw [InvertibleSheaf.pullback_obj_obj, canonicalBundle_obj,
    differentialForms_def]; rfl) ≫
    (Scheme.Modules.pullbackExteriorPowerComparison f n).app (Y.relativeDifferentials R) ≫
    (SheafOfModules.exteriorPower X.sheaf n).map (cotangentMap R f) ≫
    eqToHom (by rw [canonicalBundle_obj, differentialForms_def])

/-- The pullback on canonical bundles is the exterior-power comparison followed by the exterior
power of the cotangent map, transported along the underlying sheaf identifications. -/
theorem topDifferentialFormsMap_def :
    topDifferentialFormsMap R f n =
      eqToHom (by rw [InvertibleSheaf.pullback_obj_obj, canonicalBundle_obj,
        differentialForms_def]; rfl) ≫
        (Scheme.Modules.pullbackExteriorPowerComparison f n).app (Y.relativeDifferentials R) ≫
        (SheafOfModules.exteriorPower X.sheaf n).map (cotangentMap R f) ≫
        eqToHom (by rw [canonicalBundle_obj, differentialForms_def]) := (rfl)

private theorem fittingIdeal_zero_cokernel_topDifferentialFormsMap :
    letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    (cokernel (topDifferentialFormsMap R f n)).fittingIdeal
      (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.val U.property) 0 =
        ramificationIdealSheaf R f := by
  let L := (InvertibleSheaf.pullback f).obj (canonicalBundle R Y n)
  let K := canonicalBundle R X n
  let d := topDifferentialFormsMap R f n
  let Λ : X.Modules ⥤ X.Modules := SheafOfModules.exteriorPower X.sheaf n
  have := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  have := SmoothOfRelativeDimension.smooth n (Y ↘ Spec (.of R))
  let E := (FiniteLocallyFreeSheaf.pullback f).obj
    (FiniteLocallyFreeSheaf.relativeDifferentials R Y)
  let F := FiniteLocallyFreeSheaf.relativeDifferentials R X
  have hE : E.obj = (Scheme.Modules.pullback f).obj (Y.relativeDifferentials R) := by
    rw [FiniteLocallyFreeSheaf.pullback_obj_obj, FiniteLocallyFreeSheaf.relativeDifferentials_obj]
  have hF : F.obj = X.relativeDifferentials R :=
    FiniteLocallyFreeSheaf.relativeDifferentials_obj R X
  let c : E.obj ⟶ F.obj := eqToHom hE ≫ cotangentMap R f ≫ eqToHom hF.symm
  have hE_rank (x : X) : E.rank x = n :=
    (FiniteLocallyFreeSheaf.rank_pullback_apply f _ x).trans
      (FiniteLocallyFreeSheaf.rank_relativeDifferentials_apply R n (f x))
  have hF_rank (x : X) : F.rank x = n :=
    FiniteLocallyFreeSheaf.rank_relativeDifferentials_apply R n x
  let eCot := cokernel.mapIso c (cotangentMap R f) (eqToIso hE) (eqToIso hF) (by simp [c])
  let P := (Scheme.Modules.pullbackExteriorPowerComparison f n).app (Y.relativeDifferentials R)
  let hL : L.obj = ((SheafOfModules.exteriorPower Y.sheaf n ⋙
      Scheme.Modules.pullback f).obj (Y.relativeDifferentials R)) := by
    rw [InvertibleSheaf.pullback_obj_obj, canonicalBundle_obj, differentialForms_def]
    rfl
  let hK : Λ.obj (X.relativeDifferentials R) = K.obj := by
    rw [canonicalBundle_obj, differentialForms_def]
  let eL : L.obj ≅ Λ.obj E.obj := eqToIso hL ≪≫ asIso P ≪≫ Λ.mapIso (eqToIso hE.symm)
  let eK : K.obj ≅ Λ.obj F.obj := eqToIso hK.symm ≪≫ Λ.mapIso (eqToIso hF.symm)
  let eForms := cokernel.mapIso d (Λ.map c) eL eK (by
    -- Restate the square in scheme modules so that both occurrences of the exterior
    -- power map have the same category instances.
    change (eqToHom hL ≫ P ≫ Λ.map (cotangentMap R f) ≫ eqToHom hK) ≫
        eqToHom hK.symm ≫ Λ.map (eqToHom hF.symm) =
      (eqToHom hL ≫ P ≫ Λ.map (eqToHom hE.symm)) ≫ Λ.map c
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    have hc : eqToHom hE.symm ≫ c = cotangentMap R f ≫ eqToHom hF.symm := by simp [c]
    exact congrArg (fun k : Λ.obj ((Scheme.Modules.pullback f).obj
      (Y.relativeDifferentials R)) ⟶ Λ.obj F.obj ↦ eqToHom hL ≫ P ≫ k)
      ((Λ.map_comp _ _).symm.trans
        ((congrArg (fun k ↦ Λ.map k) hc.symm).trans (Λ.map_comp _ _))))
  have hFit := Scheme.Modules.fittingIdeal_zero_cokernel_exteriorPower c hE_rank hF_rank
  rw [ramificationIdealSheaf_eq_fittingIdeal_cokernel]
  exact (Scheme.Modules.fittingIdeal_congr _ eForms 0).trans
    (hFit.trans (Scheme.Modules.fittingIdeal_congr _ eCot 0))

/-- The ramification ideal of a morphism between smooth schemes of the same relative
dimension is the image of the map on canonical bundles twisted by the dual of
the source scheme's canonical bundle. -/
theorem ramificationIdealSheaf_eq_imageIdealSheaf_topDifferentialFormsMap :
    letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    ramificationIdealSheaf R f =
      (InvertibleSheaf.twistedToUnit
        ((InvertibleSheaf.pullback f).obj (canonicalBundle R Y n))
        (canonicalBundle R X n) (topDifferentialFormsMap R f n)).imageIdealSheaf := by
  let L := (InvertibleSheaf.pullback f).obj (canonicalBundle R Y n)
  let K := canonicalBundle R X n
  let d := topDifferentialFormsMap R f n
  let φ := InvertibleSheaf.twistedToUnit L K d
  -- The image comparison views the functional as a morphism of scheme modules.
  erw [Scheme.Modules.Hom.imageIdealSheaf_eq_fittingIdeal_cokernel φ]
  calc
    _ = _ := (fittingIdeal_zero_cokernel_topDifferentialFormsMap R f n).symm
    _ = _ := (Scheme.Modules.fittingIdeal_tensor_of_isInvertible (cokernel d)
      (InvertibleSheaf.dual K).obj 0).symm
    _ = _ := (Scheme.Modules.fittingIdeal_congr _
      (InvertibleSheaf.cokernelTwistedToUnitIso L K d) 0).symm

/-- On an integral source, an effective Cartier ramification ideal supplies the
canonical class correction for a map between smooth schemes of equal relative dimension. -/
theorem mk_canonicalBundle_eq_pullback_mul_inv_ramification [IsIntegral X] :
    letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    ∀ hI : (ramificationIdealSheaf R f).IsEffectiveCartier,
      LineBundleClass.mk (canonicalBundle R X n) =
        LineBundleClass.pullback f (LineBundleClass.mk (canonicalBundle R Y n)) *
          (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ := by
  intro hI
  have := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  let L := (InvertibleSheaf.pullback f).obj (canonicalBundle R Y n)
  let K := canonicalBundle R X n
  let T := InvertibleSheaf.tensorProduct L (InvertibleSheaf.dual K)
  let φ := InvertibleSheaf.twistedToUnit L K (topDifferentialFormsMap R f n)
  have hEq : ramificationIdealSheaf R f = φ.imageIdealSheaf :=
    ramificationIdealSheaf_eq_imageIdealSheaf_topDifferentialFormsMap R f n
  have hφ : φ ≠ 0 := by
    intro hzero
    have hbot := le_bot_iff.mp (φ.imageIdealSheaf_le_of_factor ⊥ 0 (by erw [hzero, zero_comp]))
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨U, hx, a, ha, hUa⟩ :=
      (Scheme.IdealSheafData.isEffectiveCartier_iff _).mp hI x
    have : Nonempty U.val := ⟨⟨x, hx⟩⟩
    have hspan : Ideal.span {a} = ⊥ := by
      rw [← hUa, hEq, hbot, Scheme.IdealSheafData.ideal_bot]
      rfl
    exact ha.isLeftRegular.ne_zero (Ideal.span_singleton_eq_bot.mp hspan)
  have : Mono φ := T.mono_of_ne_zero_to_unit φ hφ
  have hclass : LineBundleClass.mk hI.toInvertibleSheaf =
      LineBundleClass.mk T := by
    -- Rewrite the actual Cartier ideal, then identify its invertible sheaf with the domain of φ.
    suffices ∀ h : (ramificationIdealSheaf R f).IsEffectiveCartier,
        LineBundleClass.mk h.toInvertibleSheaf = LineBundleClass.mk T from this hI
    rw [hEq]
    intro _
    exact T.mk_toInvertibleSheaf_imageIdealSheaf φ
  rw [hclass, LineBundleClass.mk_tensorProduct, ← LineBundleClass.inv_mk,
    ← LineBundleClass.pullback_mk, mul_inv_rev, inv_inv,
    mul_comm _ (LineBundleClass.pullback f _)⁻¹, mul_inv_cancel_left]

end

end QPainleve

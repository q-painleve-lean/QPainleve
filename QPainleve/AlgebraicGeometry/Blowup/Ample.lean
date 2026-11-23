/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
public import TauCeti.AlgebraicGeometry.LineBundle.RelativelyAmple
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.TwistingSheaf
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.LineBundle.RelativelyAmple
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample

/-!
# Ample twists on a blowup

The inverse of the exceptional divisor class is relatively ample on a quasi-compact blowup.
It restricts on each affine Rees chart to the positive twisting sheaf. Thus the pullback of
a sufficiently large ample power, tensored with the exceptional ideal, is ample. In additive
Picard notation this is the class `n • π*H - E`.

See [Stacks Project, Lemma 31.33.13](https://stacks.math.columbia.edu/tag/02NS).
-/

public section

open AlgebraicGeometry CategoryTheory Filter TopologicalSpace
open TauCeti.AlgebraicGeometry reesAlgebra

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData) [QuasiCompact I.blowupToBase]

/-- The ideal of the exceptional divisor is relatively ample on a quasi-compact blowup. -/
theorem isRelativelyAmple_inv_blowupExceptionalClass :
    (I.blowupExceptionalClass⁻¹).IsRelativelyAmple I.blowupToBase := by
  constructor
  intro U hU
  let V := I.blowupToBase ⁻¹ᵁ U
  let J := I.ideal ⟨U, hU⟩
  let c := I.blowupChart hU
  have hc : c.opensRange = V := I.opensRange_blowupChart hU
  let e := IsOpenImmersion.isoOfRangeEq c V.ι (by
    rw [← Scheme.Hom.coe_opensRange, hc, Scheme.Opens.range_ι])
  have he : e.hom ≫ V.ι = c := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU.isCompact
  have : CompactSpace V.toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (I.blowupToBase ∣_ U)
  have : CompactSpace (Proj (grade J)) := QuasiCompact.compactSpace_of_compactSpace e.hom
  let E := I.isEffectiveCartier_comap_blowupToBase
  let F := E.comap c
  have hF : (I.comap I.blowupToBase).comap c = affineBlowupExceptionalIdeal _ J := by
    rw [I.comap_blowupChart_comap_blowupToBase hU, affineBlowupExceptionalIdeal_def,
      ← toSpecCoeff_reesAlgebra]
    rfl
  have hcover : (⨆ a : J, Proj.basicOpen (grade J) (monomialDegreeOne a.property)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _
      (irrelevant_eq_span_monomialDegreeOne (s := fun a : J ↦ (a : Γ(X, U))) (by simp)).le
  let O : InvertibleSheaf (Proj (grade J)) :=
    ⟨Proj.twistingSheaf (grade J) 1, Proj.isInvertible_twistingSheaf_of_iSup_eq_top _
      (fun a : J ↦ monomialDegreeOne_mem_grade a.property) hcover _⟩
  have hO : LineBundleClass.mk F.toInvertibleSheaf = LineBundleClass.mk O :=
    LineBundleClass.mk_eq_mk_iff.mpr
      ⟨eqToIso (IsEffectiveCartier.toInvertibleSheaf_obj F) ≪≫
        eqToIso (congrArg Scheme.IdealSheafData.sheaf hF) ≪≫
        QPainleve.affineBlowupExceptionalIdealIsoTwistingSheaf _ J⟩
  have hample : (LineBundleClass.pullback c (LineBundleClass.mk E.toInvertibleSheaf)).IsAmple := by
    rw [E.pullback_mk_toInvertibleSheaf F, hO]
    exact Proj.isAmple_twistingSheaf _ (fun a : J ↦ monomialDegreeOne_mem_grade a.property)
      hcover Nat.one_pos
  have h := hample.pullback_of_isAffineHom e.inv
  rw [LineBundleClass.pullback_comp, ← he, Iso.inv_hom_id_assoc] at h
  simpa only [blowupExceptionalClass_def, inv_inv] using h

/-- If `H` is ample on the base of a quasi-compact blowup, then `n • π*H - E` is ample
for every sufficiently large `n`. The exceptional class is that of the actual inverse image
of the center. -/
theorem eventually_isAmple_pullback_pow_mul_inv_blowupExceptionalClass
    {H : LineBundleClass X} (hH : H.IsAmple) :
    ∀ᶠ n : ℕ in atTop,
      (LineBundleClass.pullback I.blowupToBase H ^ n * I.blowupExceptionalClass⁻¹).IsAmple := by
  simpa only [mul_comm] using
    I.isRelativelyAmple_inv_blowupExceptionalClass.eventually_isAmple_mul_pullback_pow hH

end AlgebraicGeometry.Scheme.IdealSheafData

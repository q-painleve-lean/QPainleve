/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.Blowup.Submodule.Projective

/-!
# Projective presentations of affine blowups

The projectivized Rees algebra of an ideal spanned by `F` is isomorphic over the base
to Tau Ceti's `submoduleBlowup R F`. The induced closed embedding pulls back the coordinate
open indexed by `f ∈ F` to the standard open of `f T`.
For a finitely generated ideal this proves projectivity. Over an affine scheme the same
presentation applies to the native scheme blowup of an ideal sheaf.

## References

* The Stacks Project, Section 31.33, *Blowing up*.
* Tau Ceti's `submoduleBlowup.projectiveEmbedding` and `Proj.mapIso`.
-/

public section

open CategoryTheory AlgebraicGeometry
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace reesAlgebra

variable {R : Type u} [CommRing R] {I : Ideal R} {F : Set R}

local notation "𝒜" => grade I
local notation "ℬ" => submoduleBlowup.gradedRing R F
local notation "𝒫" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R (F →₀ R)

private noncomputable def spanCoeffEquiv (hF : Ideal.span F = I) :
    reesAlgebra I ≃ₐ[R] coeffSubalgebra (fun n ↦ Submodule.span R F ^ n) :=
  Subalgebra.equivOfEq _ _ <| by
    rw [reesAlgebra_eq_coeffSubalgebra, Ideal.submodule_span_eq, hF]

private theorem coe_spanCoeffEquiv (hF : Ideal.span F = I) (a : reesAlgebra I) :
    (spanCoeffEquiv hF a : Polynomial R) = a :=
  congrArg Subtype.val (Subalgebra.equivOfEq_apply _ _ _ a)

private theorem spanCoeffEquiv_mem_grade_iff (hF : Ideal.span F = I) (n : ℕ)
    (a : reesAlgebra I) : spanCoeffEquiv hF a ∈ ℬ n ↔ a ∈ 𝒜 n := by
  rw [coeffSubalgebra.mem_grade_iff_monomial_coeff, reesAlgebra.mem_grade_iff_monomial_coeff,
    coe_spanCoeffEquiv]

private noncomputable def spanGradedHom (hF : Ideal.span F = I) : 𝒜 →+*ᵍ ℬ where
  __ := (spanCoeffEquiv hF).toRingHom
  map_mem {n a} ha := (spanCoeffEquiv_mem_grade_iff hF n a).mpr ha

private noncomputable def spanGradedHomInv (hF : Ideal.span F = I) : ℬ →+*ᵍ 𝒜 where
  __ := (spanCoeffEquiv hF).symm.toRingHom
  map_mem {n a} ha := (spanCoeffEquiv_mem_grade_iff hF n _).mp
    ((spanCoeffEquiv hF).apply_symm_apply a ▸ ha)

private theorem spanGradedHomInv_rightInverse (hF : Ideal.span F = I) :
    Function.RightInverse (spanGradedHom hF) (spanGradedHomInv hF) :=
  (spanCoeffEquiv hF).symm_apply_apply

private theorem spanGradedHomInv_leftInverse (hF : Ideal.span F = I) :
    Function.LeftInverse (spanGradedHom hF) (spanGradedHomInv hF) :=
  (spanCoeffEquiv hF).apply_symm_apply

private theorem spanGradedHomInv_zero_algebraMap (hF : Ideal.span F = I) (r : R) :
    (spanGradedHomInv hF).gradedZeroRingHom (algebraMap R (ℬ 0) r) =
      algebraMap R (𝒜 0) r :=
  Subtype.ext <| by
    rw [GradedRingHom.gradedZeroRingHom_apply_coe, SetLike.GradeZero.coe_algebraMap,
      SetLike.GradeZero.coe_algebraMap]
    exact (spanCoeffEquiv hF).symm.commutes r

/-- The Rees projective spectrum and the submodule blowup for any generating set of the
ideal are isomorphic by identifying their graded pieces. -/
noncomputable def projIsoSubmoduleBlowup (hF : Ideal.span F = I) :
    Proj 𝒜 ≅ submoduleBlowup R F :=
  Proj.mapIso (spanGradedHomInv hF) (spanGradedHom hF)
    (spanGradedHomInv_rightInverse hF) (spanGradedHomInv_leftInverse hF)

/-- The comparison of Rees and submodule blowups commutes with the coefficient morphisms. -/
@[reassoc (attr := simp)]
theorem projIsoSubmoduleBlowup_hom_toSpec (hF : Ideal.span F = I) :
    (projIsoSubmoduleBlowup hF).hom ≫ submoduleBlowup.toSpec R F = Proj.toSpecCoeff 𝒜 := by
  rw [projIsoSubmoduleBlowup, Proj.mapIso_hom, submoduleBlowup.toSpec_def, ← Proj.toSpecCoeff_def]
  exact Proj.map_toSpecCoeff _ _ _ (spanGradedHomInv_zero_algebraMap hF)

private theorem spanGradedHomInv_monomialDegreeOne (hF : Ideal.span F = I) (f : F) :
    spanGradedHomInv hF (submoduleBlowup.monomialDegreeOne R f.property) =
      monomialDegreeOne (show (f : R) ∈ I from hF ▸ Ideal.subset_span f.property) := by
  apply (spanCoeffEquiv hF).injective
  -- Read the graded map as the inverse of the polynomial coefficient identification.
  change spanCoeffEquiv hF ((spanCoeffEquiv hF).symm
    (submoduleBlowup.monomialDegreeOne R f.property)) = spanCoeffEquiv hF _
  rw [(spanCoeffEquiv hF).apply_symm_apply]
  apply Subtype.ext
  simp only [submoduleBlowup.coe_monomialDegreeOne, coe_spanCoeffEquiv, coe_monomialDegreeOne]

/-- The comparison pulls each degree-one basic open back to the corresponding Rees chart. -/
@[simp]
theorem projIsoSubmoduleBlowup_hom_preimage_basicOpen (hF : Ideal.span F = I) (f : F) :
    (projIsoSubmoduleBlowup hF).hom ⁻¹ᵁ
        Proj.basicOpen ℬ (submoduleBlowup.monomialDegreeOne R f.property) =
      Proj.basicOpen 𝒜
        (monomialDegreeOne (show (f : R) ∈ I from hF ▸ Ideal.subset_span f.property)) := by
  rw [projIsoSubmoduleBlowup, Proj.mapIso_hom, Proj.map_preimage_basicOpen,
    spanGradedHomInv_monomialDegreeOne]

/-- The closed projective presentation of the affine blowup with one coordinate for each
element of an ideal generating set. -/
noncomputable def projectiveEmbedding (hF : Ideal.span F = I) :
    Proj 𝒜 ⟶ Proj 𝒫 :=
  (projIsoSubmoduleBlowup hF).hom ≫ submoduleBlowup.projectiveEmbedding R F

/-- The affine Rees embedding is the submodule blowup embedding under the comparison. -/
theorem projectiveEmbedding_def (hF : Ideal.span F = I) :
    projectiveEmbedding hF =
      (projIsoSubmoduleBlowup hF).hom ≫ submoduleBlowup.projectiveEmbedding R F :=
  (rfl)

instance isClosedImmersion_projectiveEmbedding (hF : Ideal.span F = I) :
    IsClosedImmersion (projectiveEmbedding hF) :=
  inferInstanceAs (IsClosedImmersion
    ((projIsoSubmoduleBlowup hF).hom ≫ submoduleBlowup.projectiveEmbedding R F))

/-- The projective presentation is over the affine base of the blowup. -/
@[reassoc (attr := simp)]
theorem projectiveEmbedding_projToSpec (hF : Ideal.span F = I) :
    projectiveEmbedding hF ≫ TauCeti.SymmetricAlgebra.projToSpec R (F →₀ R) =
      Proj.toSpecCoeff 𝒜 := by
  simp only [projectiveEmbedding_def, Category.assoc,
    submoduleBlowup.projectiveEmbedding_projToSpec, projIsoSubmoduleBlowup_hom_toSpec]

/-- The nonvanishing open of the projective coordinate indexed by `f` pulls back to the
Rees chart where `f T` is nonvanishing. -/
@[simp]
theorem projectiveEmbedding_preimage_basicOpen (hF : Ideal.span F = I) (f : F) :
    projectiveEmbedding hF ⁻¹ᵁ
        Proj.basicOpen 𝒫 (_root_.SymmetricAlgebra.ι R (F →₀ R) (Finsupp.single f 1)) =
      Proj.basicOpen 𝒜
        (monomialDegreeOne (show (f : R) ∈ I from hF ▸ Ideal.subset_span f.property)) := by
  simp only [projectiveEmbedding_def, Scheme.Hom.comp_preimage,
    submoduleBlowup.projectiveEmbedding_preimage_basicOpen,
    projIsoSubmoduleBlowup_hom_preimage_basicOpen]

/-- The Rees projective spectrum of a finitely generated ideal is projective over its
coefficient ring. -/
theorem isProjectiveOver_proj_reesAlgebra (hI : I.FG) :
    let : (Proj 𝒜).Over (Spec (.of R)) := ⟨Proj.toSpecCoeff 𝒜⟩
    (Proj 𝒜).IsProjectiveOver R := by
  obtain ⟨F, hfinite, hF⟩ := Submodule.fg_def.mp hI
  have : (submoduleBlowup R F).IsProjectiveOver R :=
    submoduleBlowup.isProjectiveOver R F hfinite
  have hspan : Ideal.span F = I := (Ideal.submodule_span_eq (s := F)).symm.trans hF
  let : (Proj 𝒜).Over (Spec (.of R)) := ⟨Proj.toSpecCoeff 𝒜⟩
  let e := projIsoSubmoduleBlowup hspan
  have : e.hom.IsOver (Spec (.of R)) := ⟨projIsoSubmoduleBlowup_hom_toSpec _⟩
  exact Scheme.IsProjectiveOver.of_isClosedImmersion R e.hom

end reesAlgebra

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData) [IsAffine X]

/-- Over an affine scheme, the affine Rees chart on the whole base is the entire blowup. -/
theorem isIso_blowupChart_top : IsIso (I.blowupChart (isAffineOpen_top X)) := by
  have : IsIso (isAffineOpen_top X).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  exact (I.isPullback_blowupChart_fromSpec (isAffineOpen_top X)).isIso_snd_of_isIso

/-- The blowup of an affine scheme in a finitely generated ideal is projective over the
ring of global sections, through the native blowup projection. -/
theorem isProjectiveOver_blowup_of_isAffine (hI : (I.ideal ⟨⊤, isAffineOpen_top X⟩).FG) :
    let : I.blowup.Over (Spec Γ(X, ⊤)) := ⟨I.blowupToBase ≫ (X.isoSpec).hom⟩
    I.blowup.IsProjectiveOver Γ(X, ⊤) := by
  let hU := isAffineOpen_top X
  let J := I.ideal ⟨⊤, hU⟩
  let π := Proj.toSpecCoeff (reesAlgebra.grade J)
  let j := I.blowupChart hU
  let : (Proj (reesAlgebra.grade J)).Over (Spec Γ(X, ⊤)) := ⟨π⟩
  let : I.blowup.Over (Spec Γ(X, ⊤)) := ⟨I.blowupToBase ≫ (X.isoSpec).hom⟩
  have : IsIso j := I.isIso_blowupChart_top
  have hj : j ≫ I.blowupToBase ≫ (X.isoSpec).hom = π := by
    rw [I.blowupChart_blowupToBase_assoc, IsAffineOpen.fromSpec_top, Iso.inv_hom_id,
      Category.comp_id]
  have : (inv j).IsOver (Spec Γ(X, ⊤)) := ⟨(IsIso.inv_comp_eq j).mpr hj.symm⟩
  have : (Proj (reesAlgebra.grade J)).IsProjectiveOver Γ(X, ⊤) :=
    reesAlgebra.isProjectiveOver_proj_reesAlgebra hI
  exact Scheme.IsProjectiveOver.of_isClosedImmersion Γ(X, ⊤) (inv j)

end AlgebraicGeometry.Scheme.IdealSheafData

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
public import QPainleve.Geometry.Toric.Fan.TorusAction.Translation

import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Translating toric boundary centers

Torus translation preserves the reduced boundary and rescales the coordinate of each
binomial point by the value of its primitive character. The parameter of that point
therefore transforms by the inverse character value. This gives the ideal-sheaf
comparison used to transport ordered internal blowups, as in Gross, Hacking and Keel,
*Moduli of surfaces with an anti-canonical cycle*, Proposition 2.9.

The affine calculation uses `MonoidAlgebra.charTwist` and the restriction of monomials
along `faceAffineCoordinateRingMap`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Multiplicative
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]

local notation "Chars" => (Multiplicative (N →+ ℤ) →* ℂˣ)
local notation "boundary" => Φ.boundaryIdeal h₀

/-- Translation preserves the reduced closed complement of the dense torus. -/
@[simp]
theorem comap_boundaryIdeal_torusTranslation_hom (χ : Chars) :
    (boundary).comap (Φ.torusTranslation χ).hom = boundary := by
  let t := (Φ.torusTranslation χ).hom
  let j := Φ.denseTorusι h₀
  let q := Spec.map (CommRingCat.ofHom (MonoidAlgebra.charTwist
    (χ.comp (denseTorusDualEquiv Φ.lattice).toMultiplicative.toMonoidHom)).toAlgHom.toRingHom)
  have hq : IsIso q := (Scheme.Spec.mapIso
    (MonoidAlgebra.charTwist (χ.comp
      (denseTorusDualEquiv Φ.lattice).toMultiplicative.toMonoidHom)).toRingEquiv.toCommRingCatIso.op
    ).isIso_hom
  have hcomp : ⇑(j ≫ t) = ⇑t ∘ ⇑j := funext (Scheme.Hom.comp_apply j t)
  have hrange : t '' Set.range j = Set.range j := by
    rw [← Set.range_comp, ← hcomp,
      Φ.denseTorusι_comp_torusTranslation_hom χ]
    exact q.homeomorph.surjective.range_comp j
  have hpre : t ⁻¹' Set.range j = Set.range j := by
    exact (congrArg (Set.preimage t) hrange.symm).trans
      (t.homeomorph.injective.preimage_image (Set.range j))
  rw [boundaryIdeal_def, comap_vanishingIdeal_of_isOpenImmersion]
  apply congrArg vanishingIdeal
  apply SetLike.coe_injective
  -- The two closed sets are given by their carriers in the same fan scheme.
  change t ⁻¹' (Set.range j)ᶜ = (Set.range j)ᶜ
  rw [Set.preimage_compl, hpre]

private theorem boundaryIdeal_le_map_torusTranslation_hom (χ : Chars) :
    boundary ≤ (boundary).map (Φ.torusTranslation χ).hom :=
  le_map_iff_comap_le.mpr (comap_boundaryIdeal_torusTranslation_hom χ).le

/-- The restriction of torus translation to the reduced toric boundary. -/
def boundaryTranslation (χ : Chars) : (boundary).subscheme ≅ (boundary).subscheme := by
  let t := (Φ.torusTranslation χ).hom
  let g := subschemeMap boundary boundary t (boundaryIdeal_le_map_torusTranslation_hom χ)
  have hs : IsPullback (boundary).subschemeι g t (boundary).subschemeι :=
    isPullback_of_isClosedImmersion (boundary).subschemeι (boundary).subschemeι g t
      (subschemeMap_subschemeι _ _ _ _).symm
      (by simp [t])
  have := hs.isIso_snd_of_isIso
  exact asIso g

/-- Boundary translation agrees with the ambient translation under the closed immersion. -/
@[reassoc, simp]
theorem boundaryTranslation_hom_subschemeι (χ : Chars) :
    (boundaryTranslation (Φ := Φ) χ).hom ≫ (boundary).subschemeι =
      (boundary).subschemeι ≫ (Φ.torusTranslation χ).hom :=
  subschemeMap_subschemeι _ _ _ (boundaryIdeal_le_map_torusTranslation_hom χ)

/-- The boundary translation is an isomorphism over the ground field. -/
instance isOver_boundaryTranslation_hom (χ : Chars) :
    (boundaryTranslation (Φ := Φ) χ).hom.IsOver (Spec (.of ℂ)) := ⟨by
  rw [(boundary).over_eq_subschemeι_comp, boundaryTranslation_hom_subschemeι_assoc, comp_over]⟩

/-- Unit translation restricts to the identity of the boundary. -/
@[simp]
theorem boundaryTranslation_one :
    boundaryTranslation (Φ := Φ) (1 : Chars) = Iso.refl (boundary).subscheme := by
  apply Iso.ext
  apply (cancel_mono (boundary).subschemeι).mp
  simp

/-- Boundary translations compose by multiplying the translating characters. -/
theorem boundaryTranslation_trans (χ ψ : Chars) :
    boundaryTranslation (Φ := Φ) χ ≪≫ boundaryTranslation ψ = boundaryTranslation (χ * ψ) := by
  apply Iso.ext
  apply (cancel_mono (boundary).subschemeι).mp
  simpa only [Iso.trans_hom, Category.assoc, boundaryTranslation_hom_subschemeι,
    boundaryTranslation_hom_subschemeι_assoc] using
    congrArg (fun g : Φ.algebraicRealization ≅ Φ.algebraicRealization ↦
      (boundary).subschemeι ≫ g.hom) (Φ.torusTranslation_trans χ ψ)

/-- The inverse boundary translation comes from the inverse character. -/
@[simp]
theorem boundaryTranslation_symm (χ : Chars) :
    (boundaryTranslation (Φ := Φ) χ).symm = boundaryTranslation χ⁻¹ := by
  apply Iso.ext
  apply (cancel_mono (boundary).subschemeι).mp
  apply (cancel_epi (boundaryTranslation (Φ := Φ) χ).hom).mp
  rw [Iso.symm_hom, Iso.hom_inv_id_assoc, ← Category.assoc, ← Iso.trans_hom,
    boundaryTranslation_trans, (mul_inv_cancel χ : χ * χ⁻¹ = 1), boundaryTranslation_one,
    Iso.refl_hom,
    Category.id_comp]

namespace Ray

variable {V : Type} [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (ρ : Φ.Ray) {m : N →+ ℤ}

local notation "chartEquiv" => (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ
  (dualSemigroup Φ.lattice ρ.toCone.val))

local notation "chartEval(" hdim ", " hm ", " hprim ", " c ")" =>
  (AlgHom.comp (binomialCenterEval ρ ℂ hdim hm hprim c)
    (AlgEquiv.toAlgHom (AlgEquiv.symm chartEquiv)))

private theorem binomialCenterEval_comp_charTwist (χ : Chars)
    (hdim : Module.finrank ℤ N = 2) (hm : m ρ.primitiveGenerator = 0)
    (hprim : Function.Surjective m) (c : ℂˣ) :
    (chartEval(hdim, hm, hprim, c)).comp (MonoidAlgebra.charTwist
      (χ.comp (dualSemigroup Φ.lattice ρ.toCone.val).subtype.toMultiplicative)).toAlgHom =
      chartEval(hdim, hm, hprim, (c / χ (ofAdd m))) := by
  let R := affineChartRing ℂ Φ.lattice ρ.toCone.val
  let e := ρ.binomialCenterEval ℂ hdim hm hprim c
  let dst := ρ.binomialCenterEval ℂ hdim hm hprim (c / χ (ofAdd m))
  let twist := MonoidAlgebra.charTwist
    (χ.comp (dualSemigroup Φ.lattice ρ.toCone.val).subtype.toMultiplicative)
  let src := (chartEval(hdim, hm, hprim, c)).comp (twist.toAlgHom.comp (chartEquiv).toAlgHom)
  have hmon (a : dualSemigroup Φ.lattice ρ.toCone.val) :
      src (AddMonoidAlgebra.single a 1) =
        (χ (ofAdd (a : N →+ ℤ)) : ℂ) * e (AddMonoidAlgebra.single a 1) := by
    simp only [src, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, twist,
      AddMonoidAlgebra.toMultiplicativeAlgEquiv_single, MonoidAlgebra.charTwist_single,
      MonoidHom.comp_apply, AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd,
      AddSubmonoid.coe_subtype, mul_one, AddMonoidAlgebra.toMultiplicativeAlgEquiv_symm_single]
    simpa only [AddMonoidAlgebra.smul_single', mul_one, smul_eq_mul] using
      (map_smul e (χ (ofAdd (a : N →+ ℤ)) : ℂ) (AddMonoidAlgebra.single a 1))
  have hker : RingHom.ker dst ≤ RingHom.ker src := by
    dsimp only [dst]
    rw [ρ.ker_binomialCenterEval, sup_le_iff]
    constructor
    · apply (rayChartIdeal_le_iff _ _ _ _ _).mpr
      intro a ha
      have hle : rayChartIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
          (Ray.toToricRay Φ ρ ρ.toCone le_rfl) ℂ ≤ RingHom.ker e := by
        dsimp only [e]
        rw [ρ.ker_binomialCenterEval]
        exact le_sup_left
      have hz := RingHom.mem_ker.mp ((rayChartIdeal_le_iff _ _ _ _ _).mp hle a ha)
      exact RingHom.mem_ker.mpr ((hmon a).trans (by rw [hz, mul_zero]))
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      apply RingHom.mem_ker.mpr
      rw [map_add, map_one, map_mul, src.commutes, hmon, ρ.coe_chartCharacter]
      rw [ρ.binomialCenterEval_character]
      have hprod : (c / χ (ofAdd m)) * (χ (ofAdd m) * c⁻¹) = 1 := by
        rw [← mul_assoc, div_mul_cancel, mul_inv_cancel]
      rw [Algebra.algebraMap_self_apply, mul_neg, mul_neg, ← Units.val_mul, ← Units.val_mul,
        hprod, Units.val_one, add_neg_cancel]
  have h : src = dst := by
    apply AlgHom.ext
    intro x
    have hx : x - algebraMap ℂ R (dst x) ∈ RingHom.ker dst :=
      RingHom.mem_ker.mpr (by rw [map_sub, dst.commutes, Algebra.algebraMap_self_apply, sub_self])
    have h := RingHom.mem_ker.mp (hker hx)
    rwa [map_sub, src.commutes, Algebra.algebraMap_self_apply, sub_eq_zero] at h
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := (chartEquiv).surjective x
  simpa only [src, dst, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using
    congrArg (fun f : R →ₐ[ℂ] ℂ ↦ f y) h

variable [Nonempty Φ.cones]

/-- Translation on the fan scheme carries the binomial point with parameter `c` to the
point with parameter `c / χ(m)`. -/
@[reassoc]
theorem binomialCenter_comp_torusTranslation_hom (χ : Chars)
    (hdim : Module.finrank ℤ N = 2) (hm : m ρ.primitiveGenerator = 0)
    (hprim : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenter hdim hm hprim c ≫ (Φ.torusTranslation χ).hom =
      ρ.binomialCenter hdim hm hprim (c / χ (ofAdd m)) := by
  have heq := ρ.binomialCenterEval_comp_charTwist χ hdim hm hprim c
  rw [binomialCenter_def, Category.assoc, Φ.affineToricChartι_comp_torusTranslation_hom,
    ← Category.assoc, ← Spec.map_comp, ρ.binomialCenter_def]
  congr 2
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom heq)

/-- The actual boundary ideal of an internal center pulls back along translation to the
center with the original parameter. -/
theorem comap_internalCenter_boundaryTranslation_hom (b : Module.Basis (Fin 2) ℤ N)
    (χ : Chars) (c : ℂˣ) :
    (ρ.internalCenter b
      (c / χ (ofAdd (b.detDualEquiv ρ.primitiveGenerator).toAddMonoidHom))).val.comap
        (boundaryTranslation (Φ := Φ) χ).hom = (ρ.internalCenter b c).val := by
  let hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let m := (b.detDualEquiv ρ.primitiveGenerator).toAddMonoidHom
  have hm : m ρ.primitiveGenerator = 0 := b.detDualEquiv_self _
  let hprim := ρ.surjective_detCharacter b
  let d := c / χ (ofAdd (b.detDualEquiv ρ.primitiveGenerator).toAddMonoidHom)
  have h : ρ.binomialCenterOnBoundary hdim hm hprim c ≫ (boundaryTranslation χ).hom =
      ρ.binomialCenterOnBoundary hdim hm hprim d := by
    apply (cancel_mono (Φ.boundaryIdeal inferInstance).subschemeι).mp
    rw [Category.assoc, boundaryTranslation_hom_subschemeι, ← Category.assoc,
      ρ.binomialCenterOnBoundary_comp_subschemeι hdim hm hprim c,
      ρ.binomialCenterOnBoundary_comp_subschemeι hdim hm hprim d]
    exact ρ.binomialCenter_comp_torusTranslation_hom χ hdim hm hprim c
  rw [internalCenter_val, internalCenter_val]
  exact (congrArg (fun f ↦ f.ker.comap (boundaryTranslation χ).hom) h).symm.trans
    (Scheme.Hom.comap_ker_comp_of_isClosedImmersion _ _)

end Ray

end TauCeti.Toric.Fan

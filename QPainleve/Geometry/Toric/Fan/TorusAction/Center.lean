/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
public import QPainleve.Geometry.Toric.BaseChange.Translation

import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Translating toric boundary centers

Torus translation preserves the reduced boundary and rescales the coordinate of each
binomial point by the value of its primitive character. The parameter of that point
therefore transforms by the inverse character value. This gives the ideal-sheaf
comparison used to transport ordered internal blowups, as in Gross, Hacking and Keel,
*Moduli of surfaces with an anti-canonical cycle*, Proposition 2.9.

The affine calculation uses the effect of `AddMonoidAlgebra.charTwist` on each monomial.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra Multiplicative
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

universe u

section Boundary

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]

local notation "Chars" => (Multiplicative (N →+ ℤ) →* Rˣ)
local notation "boundary" => Φ.toricBoundaryIdeal R h₀

/-- Translation preserves the reduced closed complement of the dense torus. -/
@[simp]
theorem comap_boundaryIdeal_torusTranslation_hom (χ : Chars) :
    (boundary).comap (Φ.torusTranslationIso R χ).hom = boundary := by
  let t := (Φ.torusTranslationIso R χ).hom
  let σ : Φ.cones := ⟨⊥, Φ.bot_mem h₀.some.property⟩
  let j := Φ.affineChartι R σ
  have hpre := Φ.preimage_range_affineChartι_torusTranslationIso R χ σ
  rw [toricBoundaryIdeal_def, comap_vanishingIdeal_of_isOpenImmersion]
  apply congrArg vanishingIdeal
  apply SetLike.coe_injective
  -- The two closed sets are given by their carriers in the same fan scheme.
  change t ⁻¹' (Set.range j)ᶜ = (Set.range j)ᶜ
  rw [Set.preimage_compl, hpre]

private theorem boundaryIdeal_le_map_torusTranslation_hom (χ : Chars) :
    boundary ≤ (boundary).map (Φ.torusTranslationIso R χ).hom :=
  le_map_iff_comap_le.mpr (comap_boundaryIdeal_torusTranslation_hom R χ).le

/-- The restriction of torus translation to the reduced toric boundary. -/
def boundaryTranslation (χ : Chars) : (boundary).subscheme ≅ (boundary).subscheme := by
  let t := (Φ.torusTranslationIso R χ).hom
  let g := subschemeMap boundary boundary t (boundaryIdeal_le_map_torusTranslation_hom R χ)
  have hs : IsPullback (boundary).subschemeι g t (boundary).subschemeι :=
    isPullback_of_isClosedImmersion (boundary).subschemeι (boundary).subschemeι g t
      (subschemeMap_subschemeι _ _ _ _).symm
      (by simp [t])
  have := hs.isIso_snd_of_isIso
  exact asIso g

/-- Boundary translation agrees with the ambient translation under the closed immersion. -/
@[reassoc, simp]
theorem boundaryTranslation_hom_subschemeι (χ : Chars) :
    (boundaryTranslation R (Φ := Φ) χ).hom ≫ (boundary).subschemeι =
      (boundary).subschemeι ≫ (Φ.torusTranslationIso R χ).hom :=
  subschemeMap_subschemeι _ _ _ (boundaryIdeal_le_map_torusTranslation_hom R χ)

/-- The boundary translation is an isomorphism over the ground field. -/
instance isOver_boundaryTranslation_hom (χ : Chars) :
    (boundaryTranslation R (Φ := Φ) χ).hom.IsOver (Spec (.of R)) := ⟨by
  rw [(boundary).over_eq_subschemeι_comp, boundaryTranslation_hom_subschemeι_assoc, comp_over]⟩

/-- Unit translation restricts to the identity of the boundary. -/
@[simp]
theorem boundaryTranslation_one :
    boundaryTranslation R (Φ := Φ) (1 : Chars) = Iso.refl (boundary).subscheme := by
  apply Iso.ext
  apply (cancel_mono (boundary).subschemeι).mp
  simp

/-- Boundary translations compose by multiplying the translating characters. -/
theorem boundaryTranslation_trans (χ ψ : Chars) :
    boundaryTranslation R (Φ := Φ) χ ≪≫ boundaryTranslation R ψ =
      boundaryTranslation R (χ * ψ) := by
  apply Iso.ext
  apply (cancel_mono (boundary).subschemeι).mp
  simpa only [Iso.trans_hom, Category.assoc, boundaryTranslation_hom_subschemeι,
    boundaryTranslation_hom_subschemeι_assoc] using
    congrArg (fun g : Φ.finiteFanScheme R ≅ Φ.finiteFanScheme R ↦
      (boundary).subschemeι ≫ g.hom) (Φ.torusTranslationIso_trans R χ ψ)

/-- The inverse boundary translation comes from the inverse character. -/
@[simp]
theorem boundaryTranslation_symm (χ : Chars) :
    (boundaryTranslation R (Φ := Φ) χ).symm = boundaryTranslation R χ⁻¹ := by
  apply Iso.ext
  apply (cancel_mono (boundary).subschemeι).mp
  apply (cancel_epi (boundaryTranslation R (Φ := Φ) χ).hom).mp
  rw [Iso.symm_hom, Iso.hom_inv_id_assoc, ← Category.assoc, ← Iso.trans_hom,
    boundaryTranslation_trans, (mul_inv_cancel χ : χ * χ⁻¹ = 1), boundaryTranslation_one,
    Iso.refl_hom,
    Category.id_comp]

end Boundary

namespace Ray

variable (k : Type u) [Field k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (ρ : Φ.Ray) {m : N →+ ℤ}

local notation "Chars" => (Multiplicative (N →+ ℤ) →* kˣ)

private theorem binomialCenterEval_comp_charTwist (χ : Chars)
    (hdim : Module.finrank ℤ N = 2) (hm : m ρ.primitiveGenerator = 0)
    (hprim : Function.Surjective m) (c : kˣ) :
    (ρ.binomialCenterEval k hdim hm hprim c).comp (AddMonoidAlgebra.charTwist
      (χ.comp (dualSemigroup Φ.lattice ρ.toCone.val).subtype.toMultiplicative)).toAlgHom =
      ρ.binomialCenterEval k hdim hm hprim (c / χ (ofAdd m)) := by
  let R := affineChartRing k Φ.lattice ρ.toCone.val
  let e := ρ.binomialCenterEval k hdim hm hprim c
  let dst := ρ.binomialCenterEval k hdim hm hprim (c / χ (ofAdd m))
  let twist := AddMonoidAlgebra.charTwist
    (χ.comp (dualSemigroup Φ.lattice ρ.toCone.val).subtype.toMultiplicative)
  let src := e.comp twist.toAlgHom
  have hmon (a : dualSemigroup Φ.lattice ρ.toCone.val) :
      src (single a 1) = (χ (ofAdd a.val) : k) * e (single a 1) := by
    dsimp only [src, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, twist]
    rw [AddMonoidAlgebra.charTwist_single, ← AddMonoidAlgebra.smul_single', map_smul]
    rfl
  have hker : RingHom.ker dst ≤ RingHom.ker src := by
    dsimp only [dst]
    rw [ρ.ker_binomialCenterEval k, sup_le_iff]
    constructor
    · apply (rayChartIdeal_le_iff _ _ _ _ _).mpr
      intro a ha
      have hle : rayChartIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
          (Ray.toToricRay Φ ρ ρ.toCone le_rfl) k ≤ RingHom.ker e := by
        dsimp only [e]
        rw [ρ.ker_binomialCenterEval k]
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
  apply AlgHom.ext
  intro x
  have hx : x - algebraMap k R (dst x) ∈ RingHom.ker dst :=
    RingHom.mem_ker.mpr (by rw [map_sub, dst.commutes, Algebra.algebraMap_self_apply, sub_self])
  have h := RingHom.mem_ker.mp (hker hx)
  rwa [map_sub, src.commutes, Algebra.algebraMap_self_apply, sub_eq_zero] at h

/-- Translation on the fan scheme carries the binomial point with parameter `c` to the
point with parameter `c / χ(m)`. -/
@[reassoc]
theorem binomialCenter_comp_torusTranslation_hom (χ : Chars)
    (hdim : Module.finrank ℤ N = 2) (hm : m ρ.primitiveGenerator = 0)
    (hprim : Function.Surjective m) (c : kˣ) :
    ρ.binomialCenter k hdim hm hprim c ≫ (Φ.torusTranslationIso k χ).hom =
      ρ.binomialCenter k hdim hm hprim (c / χ (ofAdd m)) := by
  have heq := ρ.binomialCenterEval_comp_charTwist k χ hdim hm hprim c
  rw [binomialCenter_def, Category.assoc, Φ.affineChartι_comp_torusTranslationIso_hom k,
    ← Category.assoc, ← Spec.map_comp, ρ.binomialCenter_def]
  congr 2
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom heq)

variable [Nonempty Φ.cones]

/-- The actual boundary ideal of an internal center pulls back along translation to the
center with the original parameter. -/
theorem comap_internalCenter_boundaryTranslation_hom (b : Module.Basis (Fin 2) ℤ N)
    (χ : Chars) (c : kˣ) :
    (ρ.internalCenter k b
      (c / χ (ofAdd (b.detDualEquiv ρ.primitiveGenerator).toAddMonoidHom))).val.comap
        (boundaryTranslation k (Φ := Φ) χ).hom = (ρ.internalCenter k b c).val := by
  let hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let m := (b.detDualEquiv ρ.primitiveGenerator).toAddMonoidHom
  have hm : m ρ.primitiveGenerator = 0 := b.detDualEquiv_self _
  let hprim := ρ.surjective_detCharacter b
  let d := c / χ (ofAdd (b.detDualEquiv ρ.primitiveGenerator).toAddMonoidHom)
  have h : ρ.binomialCenterOnBoundary k hdim hm hprim c ≫ (boundaryTranslation k χ).hom =
      ρ.binomialCenterOnBoundary k hdim hm hprim d := by
    apply (cancel_mono (Φ.toricBoundaryIdeal k inferInstance).subschemeι).mp
    rw [Category.assoc, boundaryTranslation_hom_subschemeι, ← Category.assoc,
      ρ.binomialCenterOnBoundary_comp_subschemeι k hdim hm hprim c,
      ρ.binomialCenterOnBoundary_comp_subschemeι k hdim hm hprim d]
    exact ρ.binomialCenter_comp_torusTranslation_hom k χ hdim hm hprim c
  rw [internalCenter_val, internalCenter_val]
  exact (congrArg (fun f ↦ f.ker.comap (boundaryTranslation k χ).hom) h).symm.trans
    (Scheme.Hom.comap_ker_comp_of_isClosedImmersion _ _)

end Ray

end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
public import QPainleve.Geometry.Toric.Fan.TorusAction.Chart

import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Torus translations of toric boundary centers

Translations preserve the reduced toric boundary. On a ray orbit, translating by
the point with character values `χ` sends the center with equation `1 + c * z^m = 0`
to the center with parameter `c / χ(m)`. The comparison is on the actual closed
point ideals, as needed to lift translations to ordered internal blowups.

The center action is the one used in Gross, Hacking and Keel, *Moduli of surfaces
with an anti-canonical cycle*, Proposition 2.6.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Multiplicative

namespace TauCeti.Toric.Fan

section ReducedBoundary

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]

local notation "Chars" => (Multiplicative (N →+ ℤ) →* ℂˣ)
local notation "boundary" => Φ.boundaryIdeal h₀

/-- Translation preserves the ideal sheaf of the reduced toric boundary. -/
@[simp]
theorem comap_boundaryIdeal_torusTranslation_hom (χ : Chars) :
    (boundary).comap (Φ.torusTranslation χ).hom = boundary := by
  let j := Φ.denseTorusι h₀
  let t := Φ.torusTranslation χ
  let e := MonoidAlgebra.charTwist (k := ℂ)
    (χ.comp (denseTorusDualEquiv Φ.lattice).toMultiplicative.toMonoidHom)
  let q := Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  have hcomp : j ≫ t.hom = q.hom ≫ j := Φ.denseTorusι_comp_torusTranslation_hom χ
  have hset : t.hom ⁻¹' Set.range j = Set.range j := by
    apply Set.image_injective.mpr t.hom.isClosedEmbedding.injective
    rw [Set.image_preimage_eq _ t.hom.surjective, ← Set.range_comp]
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      q.hom.surjective.range_eq, Set.image_univ] using
      (congrArg (fun f : Φ.denseTorus ⟶ Φ.algebraicRealization ↦ Set.range f) hcomp).symm
  rw [Φ.boundaryIdeal_def, Scheme.IdealSheafData.comap_vanishingIdeal_of_isOpenImmersion]
  congr 1
  apply TopologicalSpace.Closeds.ext
  -- Compare the underlying closed sets so the closedness proofs play no role.
  change t.hom ⁻¹' (Set.range j)ᶜ = (Set.range j)ᶜ
  rw [Set.preimage_compl, hset]

/-- The restriction of a torus translation to the reduced boundary. -/
def boundaryTranslation (χ : Chars) : (boundary).subscheme ≅ (boundary).subscheme := by
  open Scheme.IdealSheafData in
  let t := Φ.torusTranslation χ
  let J := (boundary).comap t.hom
  have h : J = boundary := Φ.comap_boundaryIdeal_torusTranslation_hom χ
  let e : (boundary).subscheme ≅ J.subscheme :=
    ⟨inclusion h.le, inclusion h.ge, by simp [inclusion_comp], by simp [inclusion_comp]⟩
  exact e ≪≫ (boundary).comapIso t.hom ≪≫ asIso (pullback.snd t.hom (boundary).subschemeι)

/-- The restricted translation agrees with the ambient translation on the boundary. -/
@[reassoc]
theorem boundaryι_comp_torusTranslation_hom (χ : Chars) :
    (boundary).subschemeι ≫ (Φ.torusTranslation χ).hom =
      (boundaryTranslation χ).hom ≫ (boundary).subschemeι := by
  simp [boundaryTranslation]

/-- Translation by the unit point induces the identity on the boundary. -/
@[simp]
theorem boundaryTranslation_one :
    boundaryTranslation (Φ := Φ) 1 = Iso.refl (boundary).subscheme := by
  apply Iso.ext
  apply (cancel_mono (boundary).subschemeι).mp
  simp [← boundaryι_comp_torusTranslation_hom]

/-- Restricting to the boundary preserves composition of translations. -/
theorem boundaryTranslation_trans (χ ψ : Chars) :
    boundaryTranslation (Φ := Φ) χ ≪≫ boundaryTranslation ψ = boundaryTranslation (χ * ψ) := by
  apply Iso.ext
  apply (cancel_mono (boundary).subschemeι).mp
  calc
    _ = (boundary).subschemeι ≫ ((Φ.torusTranslation χ) ≪≫ (Φ.torusTranslation ψ)).hom := by
      simp only [Iso.trans_hom, Category.assoc, boundaryι_comp_torusTranslation_hom_assoc,
        boundaryι_comp_torusTranslation_hom]
    _ = _ := by rw [Φ.torusTranslation_trans, boundaryι_comp_torusTranslation_hom]

end ReducedBoundary

namespace Ray

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (ρ : Φ.Ray)

local notation "Chars" => (Multiplicative (N →+ ℤ) →* ℂˣ)

local notation "S" => dualSemigroup Φ.lattice ρ.toCone.val
local notation "R" => affineCoordinateRing Φ.lattice ρ.toCone.val
local notation "twist(" χ ")" =>
  MonoidAlgebra.charTwist (k := ℂ)
    (MonoidHom.comp χ (AddMonoidHom.toMultiplicative (AddSubmonoid.subtype S)))

private theorem binomialCenterEval_comp_charTwist (χ : Chars) {m : N →+ ℤ}
    (hdim : Module.finrank ℤ N = 2) (hm : m ρ.primitiveGenerator = 0)
    (hprim : Function.Surjective m) (c : ℂˣ) :
    (ρ.binomialCenterEval hdim hm hprim c).comp (twist(χ)).toAlgHom =
      ρ.binomialCenterEval hdim hm hprim (c / χ (ofAdd m)) := by
  let f := ρ.binomialCenterEval hdim hm hprim c
  let g := f.comp (twist(χ)).toAlgHom
  let d := ρ.binomialCenterEval hdim hm hprim (c / χ (ofAdd m))
  -- The twist preserves the ray equations and transports the rescaled binomial.
  have hker : RingHom.ker d.toRingHom ≤ RingHom.ker g.toRingHom := by
    refine (ρ.ker_binomialCenterEval hdim hm hprim (c / χ (ofAdd m))).trans_le ?_
    rw [sup_le_iff]
    constructor
    · refine (rayIdeal_le_iff _ _ _ _).mpr fun a ha ↦ ?_
      have hf := (ρ.ker_binomialCenterEval hdim hm hprim c).ge
        (Ideal.mem_sup_left (monomial_mem_rayIdeal _ _ _ a ha))
      have hzero : f (MonoidAlgebra.of ℂ _ (ofAdd a)) = 0 := RingHom.mem_ker.mp hf
      apply RingHom.mem_ker.mpr
      suffices g (MonoidAlgebra.of ℂ _ (ofAdd a)) = 0 from this
      dsimp only [g]
      rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, MonoidAlgebra.charTwist_of,
        Algebra.smul_def, map_mul, hzero, mul_zero]
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      have hcancel : (χ (ofAdd m) : ℂ) * ((c : ℂ) / (χ (ofAdd m) : ℂ)) = c := by
        rw [mul_comm, div_mul_cancel₀ _ (Units.ne_zero _)]
      simp only [g, f, AlgHom.toRingHom_eq_coe, Units.val_div_eq_div_val,
        MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id,
        Function.comp_apply, id_eq, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
        one_mul, mul_one, RingHom.coe_coe, map_add, map_one, AlgHom.comp_apply,
        AlgEquiv.coe_toAlgHom, MonoidAlgebra.charTwist_single, MonoidHom.comp_apply,
        AddMonoidHom.coe_toMultiplicative, toAdd_ofAdd, AddSubmonoid.coe_subtype,
        ρ.coe_chartCharacter, hcancel]
      rw [MonoidAlgebra.single_eq_algebraMap_mul_of, map_mul, AlgHom.commutes,
        Algebra.algebraMap_self_apply, MonoidAlgebra.of_apply, ρ.binomialCenterEval_character]
      simp only [mul_neg, ← Units.val_mul, mul_inv_cancel, Units.val_one, add_neg_cancel]
  -- Subtract the scalar specified by the target evaluation before using its kernel.
  apply AlgHom.ext
  intro x
  have hx : x - algebraMap ℂ R (d x) ∈ RingHom.ker d.toRingHom := by
    apply RingHom.mem_ker.mpr
    exact (map_sub d _ _).trans (by rw [d.commutes, Algebra.algebraMap_self_apply, sub_self])
  have hz : g (x - algebraMap ℂ R (d x)) = 0 := RingHom.mem_ker.mp (hker hx)
  rwa [map_sub, g.commutes, Algebra.algebraMap_self_apply, sub_eq_zero] at hz

/-- Translation multiplies the orbit coordinate by its character value, so the
parameter of the image center is divided by that value. -/
@[reassoc]
theorem binomialCenter_comp_torusTranslation_hom [Nonempty Φ.cones] (χ : Chars) {m : N →+ ℤ}
    (hdim : Module.finrank ℤ N = 2) (hm : m ρ.primitiveGenerator = 0)
    (hprim : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenter hdim hm hprim c ≫ (Φ.torusTranslation χ).hom =
      ρ.binomialCenter hdim hm hprim (c / χ (ofAdd m)) := by
  rw [ρ.binomialCenter_def, Category.assoc, Φ.affineToricChartι_comp_torusTranslation_hom,
    ← Category.assoc, ← Spec.map_comp, ρ.binomialCenter_def]
  congr 2
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom
    (ρ.binomialCenterEval_comp_charTwist χ hdim hm hprim c))

variable [h₀ : Nonempty Φ.cones] (b : Module.Basis (Fin 2) ℤ N)

local notation "boundary" => Φ.boundaryIdeal h₀
local notation "m" => LinearMap.toAddMonoidHom (b.detDualEquiv ρ.primitiveGenerator)

/-- The ideal of an internal center on the reduced boundary transforms by the
determinant character of its ray. -/
theorem comap_internalCenter_boundaryTranslation_hom (χ : Chars) (c : ℂˣ) :
    ((ρ.internalCenter b c).val).comap (boundaryTranslation χ).hom =
      (ρ.internalCenter b (c * χ (ofAdd m))).val := by
  let e := boundaryTranslation (Φ := Φ) χ
  let t := Φ.torusTranslation χ
  let J := (ρ.internalCenter b (c * χ (ofAdd m))).val
  let J' := (ρ.internalCenter b c).val
  have himage : (J.map (boundary).subschemeι).map t.hom = J'.map (boundary).subschemeι := by
    dsimp only [J, J', t]
    rw [ρ.map_internalCenter_subschemeι, ρ.map_internalCenter_subschemeι,
      Scheme.IdealSheafData.map_ker]
    exact congrArg Scheme.Hom.ker (by
      simpa only [mul_div_cancel_right] using
        ρ.binomialCenter_comp_torusTranslation_hom χ _
          (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b)
          (c * χ (ofAdd m)))
  have hboundary : J.map e.hom = J' := by
    rw [← Scheme.IdealSheafData.map_comp, boundaryι_comp_torusTranslation_hom,
      Scheme.IdealSheafData.map_comp] at himage
    simpa only [Scheme.IdealSheafData.comap_map_of_isClosedImmersion] using
      congrArg (fun K : Φ.algebraicRealization.IdealSheafData ↦
        K.comap (boundary).subschemeι) himage
  simpa only [Scheme.IdealSheafData.comap_map_of_isClosedImmersion] using
    congrArg (fun K ↦ Scheme.IdealSheafData.comap K e.hom) hboundary.symm

end Ray
end TauCeti.Toric.Fan

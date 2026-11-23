/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import QPainleve.Geometry.Toric.Fan.TorusAction.Translation

import QPainleve.Geometry.Toric.Fan.Separated
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Boundary-fixing toric automorphisms

On a regular complete fan scheme, an automorphism fixing every ray divisor acts on
rational characters by multiplication by the values of a single torus point. This is
the toric-model step of Gross–Hacking–Keel, *Moduli of surfaces with an anti-canonical
cycle*, Proposition 2.6.

The boundary orders recover the exponent from its values on all primitive ray
generators. The classification of rational functions with zero order on the dense
torus comes from `Fan.exists_eq_const_mul_character`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open TauCeti.AlgebraicGeometry (CodimensionOnePoint)
open TauCeti.AlgebraicGeometry.Scheme (ord_functionFieldMap)

namespace TauCeti.Toric.Fan

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

local notation "X" => Φ.algebraicRealization
local notation "C" => algebraMap ℂ Φ.algebraicRealization.functionField

/-- An automorphism preserves a ray divisor exactly when it fixes its generic point. -/
theorem comap_rayBoundaryIdeal_eq_iff (hΦ : Φ.IsRegular) (e : X ≅ X) (ρ : Φ.Ray) :
    (Φ.rayBoundaryIdeal hΦ ρ).comap e.hom = Φ.rayBoundaryIdeal hΦ ρ ↔
      e.hom (Φ.rayBoundaryPoint hΦ ρ).val = (Φ.rayBoundaryPoint hΦ ρ).val := by
  let x := (Φ.rayBoundaryPoint hΦ ρ).val
  constructor
  · intro he
    have h := congrArg (fun J : (X).IdealSheafData ↦ (J.support : Set X)) he
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Φ.coe_support_rayBoundaryIdeal] at h
    have himage := congrArg (Set.image e.hom) h
    rw [Set.image_preimage_eq _ (fun y ↦ ⟨e.inv y, by simp [← Scheme.Hom.comp_apply]⟩)] at himage
    have h' := (isGenericPoint_closure (x := x)).image e.hom.continuous
    rw [← himage, closure_closure] at h'
    exact h'.eq isGenericPoint_closure
  · intro he
    simpa only [x, he, Φ.rayBoundaryIdeal_def] using
      Scheme.IdealSheafData.comap_vanishingIdeal_closure_singleton_apply e.hom x

variable [Nonempty Φ.cones]

private theorem functionFieldMap_character_eq_const_mul (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (e : X ≅ X) (he : ∀ ρ, e.hom (Φ.rayBoundaryPoint hΦ ρ).val = (Φ.rayBoundaryPoint hΦ ρ).val)
    (m : N →+ ℤ) :
    ∃ c : ℂˣ, e.hom.functionFieldMap (Φ.character (ofAdd m)) =
      C (c : ℂ) * Φ.character (ofAdd m) := by
  let T := Φ.denseTorus
  let j := Φ.denseTorusι inferInstance
  have : IsLocallyNoetherian T := isLocallyNoetherian_of_isOpenImmersion j
  let z := Units.map e.hom.functionFieldMap.hom.toMonoidHom (Φ.character.toHomUnits (ofAdd m))
  have hz (y : CodimensionOnePoint T) :
      T.ord (j.functionFieldMap (z : (X).functionField)) y.val = 0 := by
    let y' := CodimensionOnePoint.mapOfIsOpenImmersion (j ≫ e.hom) y
    have hy : y'.val ∈ Set.range j := by
      by_contra h
      obtain ⟨ρ, hr⟩ : y' ∈ Set.range (Φ.rayBoundaryPoint hΦ) :=
        (Φ.range_rayBoundaryPoint hΦ inferInstance).symm ▸ h
      have hx : e.hom (Φ.rayBoundaryPoint hΦ ρ).val = e.hom (j y.val) :=
        (he ρ).trans ((congrArg Subtype.val hr).trans (by
          rw [CodimensionOnePoint.coe_mapOfIsOpenImmersion, Scheme.Hom.comp_apply]))
      exact Φ.rayBoundaryPoint_notMem_range_denseTorusι hΦ ρ
        ⟨y.val, (e.hom.isOpenEmbedding.injective hx).symm⟩
    rw [ord_functionFieldMap j]
    -- The unit is the pullback of the rational character along the automorphism.
    change (X).ord (e.hom.functionFieldMap (Φ.character (ofAdd m))) (j y.val) = 0
    rw [ord_functionFieldMap e.hom]
    simpa only [y', CodimensionOnePoint.coe_mapOfIsOpenImmersion, Scheme.Hom.comp_apply] using
      Φ.ord_character_eq_zero_of_mem_range_denseTorusι m hy
  obtain ⟨c, m', h⟩ := Φ.exists_eq_const_mul_character z hz
  have hpull : e.hom.functionFieldMap (Φ.character (ofAdd m)) =
      C (c : ℂ) * Φ.character (ofAdd m') := h
  have hval (ρ : Φ.Ray) : m' ρ.primitiveGenerator = m ρ.primitiveGenerator := by
    have hρ := congrArg (fun f ↦ (X).ord f (Φ.rayBoundaryPoint hΦ ρ).val) hpull
    rw [ord_functionFieldMap e.hom, he ρ, Φ.ord_rayBoundaryPoint_character hΦ,
      Φ.ord_rayBoundaryPoint_mul_character hΦ] at hρ
    exact hρ.symm
  have hzero := Φ.character_eq_zero_of_nonneg_primitiveGenerator hc (m' - m)
    (fun ρ ↦ by simp [hval ρ])
  exact ⟨c, (sub_eq_zero.mp hzero) ▸ hpull⟩

/-- An automorphism fixing every ray divisor of a regular complete fan scales its
rational characters by the values of a unique torus point. -/
private theorem existsUnique_functionFieldMap_character (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (e : X ≅ X)
    (he : ∀ ρ, (Φ.rayBoundaryIdeal hΦ ρ).comap e.hom = Φ.rayBoundaryIdeal hΦ ρ) :
    ∃! χ : Multiplicative (N →+ ℤ) →* ℂˣ, ∀ m,
      e.hom.functionFieldMap (Φ.character m) = C (χ m : ℂ) * Φ.character m := by
  have hex (m : Multiplicative (N →+ ℤ)) := Φ.functionFieldMap_character_eq_const_mul hΦ hc e
    (fun ρ ↦ (Φ.comap_rayBoundaryIdeal_eq_iff hΦ e ρ).mp (he ρ)) m.toAdd
  choose c h using hex
  simp only [ofAdd_toAdd] at h
  have hcanc (m : Multiplicative (N →+ ℤ)) {u v : ℂˣ}
      (huv : C (u : ℂ) * Φ.character m = C (v : ℂ) * Φ.character m) : u = v :=
    Units.ext ((C).injective (mul_right_cancel₀ (Group.isUnit m |>.map Φ.character).ne_zero huv))
  let χ : Multiplicative (N →+ ℤ) →* ℂˣ :=
    { toFun := c
      map_one' := hcanc 1 (by
        calc
          _ = e.hom.functionFieldMap (Φ.character 1) := (h 1).symm
          _ = _ := by simp only [map_one, Units.val_one, one_mul])
      map_mul' := fun m n ↦ hcanc (m * n) (by
        calc
          _ = e.hom.functionFieldMap (Φ.character (m * n)) := (h (m * n)).symm
          _ = _ := by
            rw [map_mul Φ.character, map_mul, h m, h n, Units.val_mul, map_mul]
            ring) }
  refine ⟨χ, h, fun ψ hψ ↦ ?_⟩
  apply MonoidHom.ext
  intro m
  exact hcanc m ((hψ m).symm.trans (h m))

local notation "S" => Spec (CommRingCat.of ℂ)

private theorem torusTranslation_fixes_rayBoundaryPoint (hΦ : Φ.IsRegular)
    (χ : Multiplicative (N →+ ℤ) →* ℂˣ) (ρ : Φ.Ray) :
    (Φ.torusTranslation χ).hom (Φ.rayBoundaryPoint hΦ ρ).val =
      (Φ.rayBoundaryPoint hΦ ρ).val := by
  let j := Φ.denseTorusι inferInstance
  let t : X ⟶ X := (Φ.torusTranslation χ).hom
  have : IsIso t := (Φ.torusTranslation χ).isIso_hom
  let y := CodimensionOnePoint.mapOfIsOpenImmersion t (Φ.rayBoundaryPoint hΦ ρ)
  let χ₀ := χ.comp (denseTorusDualEquiv Φ.lattice).toMultiplicative.toMonoidHom
  let q := Scheme.Spec.mapIso (MonoidAlgebra.charTwist χ₀).toRingEquiv.toCommRingCatIso.op
  have ht : j ≫ t = q.hom ≫ j := Φ.denseTorusι_comp_torusTranslation_hom χ
  have hy : y.val ∉ Set.range j := by
    rintro ⟨z, hz⟩
    have hz' : t (j (q.inv z)) = j z := by
      have h := congrArg (fun f : Φ.denseTorus ⟶ X ↦ f (q.inv z)) ht
      simpa [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply q.inv q.hom] using h
    have hxy : t (j (q.inv z)) = t (Φ.rayBoundaryPoint hΦ ρ).val := by
      rw [hz', hz, CodimensionOnePoint.coe_mapOfIsOpenImmersion]
    exact Φ.rayBoundaryPoint_notMem_range_denseTorusι hΦ ρ
      ⟨q.inv z, t.isOpenEmbedding.injective hxy⟩
  obtain ⟨τ, hτ⟩ : y ∈ Set.range (Φ.rayBoundaryPoint hΦ) :=
    (Φ.range_rayBoundaryPoint hΦ inferInstance).symm ▸ hy
  have hx : (Φ.rayBoundaryPoint hΦ τ).val = t (Φ.rayBoundaryPoint hΦ ρ).val := by
    rw [hτ, CodimensionOnePoint.coe_mapOfIsOpenImmersion]
  have hval (m : N →+ ℤ) : m τ.primitiveGenerator = m ρ.primitiveGenerator := by
    rw [← Φ.ord_rayBoundaryPoint_character hΦ τ, hx, ← ord_functionFieldMap t]
    exact (congrArg (fun f ↦ (X).ord f (Φ.rayBoundaryPoint hΦ ρ).val)
      (Φ.functionFieldMap_torusTranslation_character χ (ofAdd m))).trans
      (Φ.ord_rayBoundaryPoint_mul_character hΦ ρ (χ (ofAdd m)) m)
  have := Φ.lattice.free
  let b := Module.Free.chooseBasis ℤ N
  have hgen : τ.primitiveGenerator = ρ.primitiveGenerator :=
    b.ext_elem_iff.2 fun l ↦ hval (b.coord l).toAddMonoidHom
  have hEq := Ray.primitiveGenerator_injective hgen
  simpa only [hEq] using hx.symm

/-- Every torus translation preserves the reduced ideal sheaf of each ray divisor. -/
@[simp]
theorem comap_rayBoundaryIdeal_torusTranslation_hom (hΦ : Φ.IsRegular)
    (χ : Multiplicative (N →+ ℤ) →* ℂˣ) (ρ : Φ.Ray) :
    (Φ.rayBoundaryIdeal hΦ ρ).comap (Φ.torusTranslation χ).hom =
      Φ.rayBoundaryIdeal hΦ ρ :=
  (Φ.comap_rayBoundaryIdeal_eq_iff hΦ (Φ.torusTranslation χ) ρ).mpr
    (Φ.torusTranslation_fixes_rayBoundaryPoint hΦ χ ρ)

/-- A complex automorphism of a regular complete fan scheme fixing every ray divisor
is translation by a unique torus point. -/
theorem existsUnique_torusTranslation_of_comap_rayBoundaryIdeal_eq
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (e : X ≅ X) [e.hom.IsOver S]
    (he : ∀ ρ, (Φ.rayBoundaryIdeal hΦ ρ).comap e.hom = Φ.rayBoundaryIdeal hΦ ρ) :
    ∃! χ : Multiplicative (N →+ ℤ) →* ℂˣ, Φ.torusTranslation χ = e := by
  obtain ⟨χ, hχ, huniq⟩ := Φ.existsUnique_functionFieldMap_character hΦ hc e he
  refine ⟨χ, ?_, fun ψ hψ ↦ huniq ψ ?_⟩
  · apply Iso.ext
    apply Scheme.Hom.ext_of_functionFieldMap_eq S
    apply CommRingCat.hom_ext
    have hmaps : (Φ.torusTranslation χ).hom.functionFieldAlgHom ℂ =
        e.hom.functionFieldAlgHom ℂ := by
      apply Φ.functionFieldAlgHom_ext
      intro m
      simp only [Scheme.Hom.functionFieldAlgHom_apply]
      exact (Φ.functionFieldMap_torusTranslation_character χ m).trans (hχ m).symm
    apply RingHom.ext
    intro a
    simpa only [Scheme.Hom.functionFieldAlgHom_apply] using DFunLike.congr_fun hmaps a
  · subst e
    exact Φ.functionFieldMap_torusTranslation_character ψ

end TauCeti.Toric.Fan

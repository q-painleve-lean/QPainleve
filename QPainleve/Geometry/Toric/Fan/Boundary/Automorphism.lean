/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import QPainleve.Geometry.Toric.BaseChange.Translation
public import QPainleve.Geometry.Toric.Fan.Boundary.Character

import QPainleve.AlgebraicGeometry.Scheme.FunctionField
import QPainleve.Geometry.Toric.BaseChange.Fan
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Boundary-fixing toric automorphisms

On a regular complete fan scheme, an automorphism fixing every ray divisor acts on
rational characters by multiplication by the values of a single torus point. This is
the toric-model step of Gross–Hacking–Keel, *Moduli of surfaces with an anti-canonical
cycle*, Proposition 2.6.

The boundary orders recover the exponent from its values on all primitive ray
generators. The classification of rational functions with zero order on the dense
torus comes from `Fan.exists_eq_unit_mul_functionFieldCharacter`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open TauCeti.AlgebraicGeometry (CodimensionOnePoint)
open TauCeti.AlgebraicGeometry.Scheme (ord_functionFieldMap)

namespace TauCeti.Toric.Fan

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [UniqueFactorizationMonoid R] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

local notation "X" => Φ.finiteFanScheme R
local notation "C" => algebraMap R (Scheme.functionField (Φ.finiteFanScheme R))

variable [h₀ : Nonempty Φ.cones]

local notation "zeroCone" =>
  (Subtype.mk (⊥ : PointedCone ℝ V) (Φ.bot_mem (Subtype.property (Nonempty.some h₀))) : Φ.cones)

private theorem functionFieldMap_character_eq_const_mul (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (e : X ≅ X) (he : ∀ ρ, e.hom (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val =
      (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val)
    (m : N →+ ℤ) :
    ∃ c : Rˣ, e.hom.functionFieldMap (Φ.functionFieldCharacter R (ofAdd m)) =
      C (c : R) * Φ.functionFieldCharacter R (ofAdd m) := by
  let T := affineChart R Φ.lattice (⊥ : PointedCone ℝ V)
  let j := Φ.affineChartι R zeroCone
  have : IsLocallyNoetherian T := isLocallyNoetherian_of_isOpenImmersion j
  let z := Units.map e.hom.functionFieldMap.hom.toMonoidHom
    ((Φ.functionFieldCharacter R).toHomUnits (ofAdd m))
  have hz (y : CodimensionOnePoint T) :
      T.ord (j.functionFieldMap (z : (X).functionField)) y.val = 0 := by
    let y' := CodimensionOnePoint.mapOfIsOpenImmersion (j ≫ e.hom) y
    have hy : y'.val ∈ Set.range j := by
      by_contra h
      obtain ⟨ρ, hr⟩ : y' ∈ Set.range (Φ.rayBoundaryChartPoint (R := R) hΦ) :=
        (Φ.range_rayBoundaryChartPoint (R := R) hΦ (Subtype.property zeroCone)).symm ▸ h
      have hx : e.hom (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val = e.hom (j y.val) :=
        (he ρ).trans ((congrArg Subtype.val hr).trans (by
          rw [CodimensionOnePoint.coe_mapOfIsOpenImmersion, Scheme.Hom.comp_apply]))
      exact Φ.rayBoundaryChartPoint_notMem_zeroChart (R := R) hΦ ρ (Subtype.property zeroCone)
        ⟨y.val, (e.hom.isOpenEmbedding.injective hx).symm⟩
    rw [ord_functionFieldMap j]
    -- The unit is the pullback of the rational character along the automorphism.
    change (X).ord (e.hom.functionFieldMap (Φ.functionFieldCharacter R (ofAdd m))) (j y.val) = 0
    rw [ord_functionFieldMap e.hom]
    simpa only [y', CodimensionOnePoint.coe_mapOfIsOpenImmersion, Scheme.Hom.comp_apply] using
      Φ.ord_functionFieldCharacter_eq_zero_of_mem_range_zeroChart R m hy
  obtain ⟨c, m', h⟩ := Φ.exists_eq_unit_mul_functionFieldCharacter R z hz
  have hpull : e.hom.functionFieldMap (Φ.functionFieldCharacter R (ofAdd m)) =
      C (c : R) * Φ.functionFieldCharacter R (ofAdd m') := h
  have hval (ρ : Φ.Ray) : m' ρ.primitiveGenerator = m ρ.primitiveGenerator := by
    have hρ := congrArg (fun f ↦ (X).ord f (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val) hpull
    rw [ord_functionFieldMap e.hom, he ρ, Φ.ord_rayBoundaryChartPoint_character R hΦ,
      Φ.ord_rayBoundaryChartPoint_mul_character R hΦ] at hρ
    exact hρ.symm
  have hzero := Φ.character_eq_zero_of_nonneg_primitiveGenerator hc (m' - m)
    (fun ρ ↦ by simp [hval ρ])
  exact ⟨c, (sub_eq_zero.mp hzero) ▸ hpull⟩

/-- An automorphism fixing every ray divisor of a regular complete fan scales its
rational characters by the values of a unique torus point. -/
private theorem existsUnique_functionFieldMap_character (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (e : X ≅ X)
    (he : ∀ ρ, (Φ.rayDivisorIdeal R hΦ ρ).comap e.hom = Φ.rayDivisorIdeal R hΦ ρ) :
    ∃! χ : Multiplicative (N →+ ℤ) →* Rˣ, ∀ m,
      e.hom.functionFieldMap (Φ.functionFieldCharacter R m) =
        C (χ m : R) * Φ.functionFieldCharacter R m := by
  have hex (m : Multiplicative (N →+ ℤ)) := Φ.functionFieldMap_character_eq_const_mul R hΦ hc e
    (fun ρ ↦ (Φ.comap_rayDivisorIdeal_eq_iff R hΦ e ρ).mp (he ρ)) m.toAdd
  choose c h using hex
  simp only [ofAdd_toAdd] at h
  let B := CommRingCat.of (affineChartRing R Φ.lattice (⊥ : PointedCone ℝ V))
  let j : Spec B ⟶ X := Φ.affineChartι R zeroCone
  let : Algebra B (Spec B).functionField := instAlgebraCarrierFunctionFieldSpec B
  have : IsFractionRing B (Spec B).functionField := functionField_isFractionRing_of_affine B
  have hbase (r : R) : algebraMap R (Spec B).functionField r =
      algebraMap B (Spec B).functionField (algebraMap R B r) := by
    rw [Scheme.Spec.algebraMap_functionField_base, Scheme.ΓSpecIso_inv]
    rfl
  have hinj : Function.Injective C := by
    intro a b h
    have hp := congrArg j.functionFieldMap h
    rw [j.functionFieldMap_algebraMap R, j.functionFieldMap_algebraMap R,
      hbase, hbase] at hp
    have he := (IsFractionRing.injective B (Spec B).functionField) hp
    exact AddMonoidAlgebra.single_right_injective (m := (0 : dualSemigroup Φ.lattice ⊥)) he
  have hcanc (m : Multiplicative (N →+ ℤ)) {u v : Rˣ}
      (huv : C (u : R) * Φ.functionFieldCharacter R m =
        C (v : R) * Φ.functionFieldCharacter R m) : u = v := by
    have hm := (Group.isUnit m |>.map (Φ.functionFieldCharacter R)).ne_zero
    exact Units.ext (hinj (mul_right_cancel₀ hm huv))
  let χ : Multiplicative (N →+ ℤ) →* Rˣ :=
    { toFun := c
      map_one' := hcanc 1 (by
        calc
          _ = e.hom.functionFieldMap (Φ.functionFieldCharacter R 1) := (h 1).symm
          _ = _ := by simp only [map_one, Units.val_one, one_mul])
      map_mul' := fun m n ↦ hcanc (m * n) (by
        calc
          _ = e.hom.functionFieldMap (Φ.functionFieldCharacter R (m * n)) := (h (m * n)).symm
          _ = _ := by
            rw [map_mul (Φ.functionFieldCharacter R), map_mul, h m, h n, Units.val_mul, map_mul]
            ring) }
  refine ⟨χ, h, fun ψ hψ ↦ ?_⟩
  apply MonoidHom.ext
  intro m
  exact hcanc m ((hψ m).symm.trans (h m))

local notation "S" => Spec (CommRingCat.of R)

omit [UniqueFactorizationMonoid R] in
private theorem torusTranslation_fixes_rayBoundaryPoint (hΦ : Φ.IsRegular)
    (χ : Multiplicative (N →+ ℤ) →* Rˣ) (ρ : Φ.Ray) :
    (Φ.torusTranslationIso R χ).hom (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val =
      (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val := by
  let j := Φ.affineChartι R zeroCone
  let t : X ⟶ X := (Φ.torusTranslationIso R χ).hom
  have : IsIso t := (Φ.torusTranslationIso R χ).isIso_hom
  let y := CodimensionOnePoint.mapOfIsOpenImmersion t (Φ.rayBoundaryChartPoint (R := R) hΦ ρ)
  have hy : y.val ∉ Set.range j := by
    intro hy
    have h := Φ.rayBoundaryChartPoint_notMem_zeroChart (R := R) hΦ ρ
      (Subtype.property zeroCone)
    apply h
    rw [← Φ.preimage_range_affineChartι_torusTranslationIso R χ zeroCone]
    simpa only [Set.mem_preimage, y, t, j, CodimensionOnePoint.coe_mapOfIsOpenImmersion] using hy
  obtain ⟨τ, hτ⟩ : y ∈ Set.range (Φ.rayBoundaryChartPoint (R := R) hΦ) :=
    (Φ.range_rayBoundaryChartPoint (R := R) hΦ (Subtype.property zeroCone)).symm ▸ hy
  have hx : (Φ.rayBoundaryChartPoint (R := R) hΦ τ).val =
      t (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val := by
    rw [hτ, CodimensionOnePoint.coe_mapOfIsOpenImmersion]
  have hval (m : N →+ ℤ) : m τ.primitiveGenerator = m ρ.primitiveGenerator := by
    rw [← Φ.ord_rayBoundaryChartPoint_character R hΦ τ, hx, ← ord_functionFieldMap t]
    exact (congrArg (fun f ↦ (X).ord f (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val)
      (Φ.functionFieldMap_torusTranslationIso_character R χ m)).trans
      (Φ.ord_rayBoundaryChartPoint_mul_character R hΦ ρ (χ (ofAdd m)) m)
  have := Φ.lattice.free
  let b := Module.Free.chooseBasis ℤ N
  have hgen : τ.primitiveGenerator = ρ.primitiveGenerator :=
    b.ext_elem_iff.2 fun l ↦ hval (b.coord l).toAddMonoidHom
  have hEq := Ray.primitiveGenerator_injective hgen
  simpa only [hEq] using hx.symm

omit [UniqueFactorizationMonoid R] in
/-- Every torus translation preserves the reduced ideal sheaf of each ray divisor. -/
@[simp]
theorem comap_rayBoundaryIdeal_torusTranslation_hom (hΦ : Φ.IsRegular)
    (χ : Multiplicative (N →+ ℤ) →* Rˣ) (ρ : Φ.Ray) :
    (Φ.rayDivisorIdeal R hΦ ρ).comap (Φ.torusTranslationIso R χ).hom =
      Φ.rayDivisorIdeal R hΦ ρ :=
  (Φ.comap_rayDivisorIdeal_eq_iff R hΦ (Φ.torusTranslationIso R χ) ρ).mpr
    (Φ.torusTranslation_fixes_rayBoundaryPoint R hΦ χ ρ)

/-- A base-preserving automorphism of a regular complete fan scheme that fixes every
ray divisor is translation by a unique torus point. -/
theorem existsUnique_torusTranslation_of_comap_rayBoundaryIdeal_eq
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (e : X ≅ X) [e.hom.IsOver S]
    (he : ∀ ρ, (Φ.rayDivisorIdeal R hΦ ρ).comap e.hom = Φ.rayDivisorIdeal R hΦ ρ) :
    ∃! χ : Multiplicative (N →+ ℤ) →* Rˣ, Φ.torusTranslationIso R χ = e := by
  obtain ⟨χ, hχ, huniq⟩ := Φ.existsUnique_functionFieldMap_character R hΦ hc e he
  refine ⟨χ, ?_, fun ψ hψ ↦ huniq ψ ?_⟩
  · have : IsSeparated (X ↘ S) := by
      rw [Φ.finiteFanScheme_over R]
      infer_instance
    apply Iso.ext
    apply Scheme.Hom.ext_of_functionFieldMap_eq S
    apply CommRingCat.hom_ext
    have hmaps : (Φ.torusTranslationIso R χ).hom.functionFieldAlgHom R =
        e.hom.functionFieldAlgHom R := by
      apply Φ.functionFieldCharacter_algHom_ext R
      intro m
      simp only [Scheme.Hom.functionFieldAlgHom_apply]
      have hm := Φ.functionFieldMap_torusTranslationIso_character R χ m.toAdd
      simpa only [ofAdd_toAdd] using hm.trans (hχ (ofAdd m.toAdd)).symm
    apply RingHom.ext
    intro a
    simpa only [Scheme.Hom.functionFieldAlgHom_apply] using DFunLike.congr_fun hmaps a
  · subst e
    exact fun m ↦ by simpa only [ofAdd_toAdd] using
      Φ.functionFieldMap_torusTranslationIso_character R ψ m.toAdd

end TauCeti.Toric.Fan

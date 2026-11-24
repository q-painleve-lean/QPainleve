/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import TauCeti.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Tower.Reorder
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Total exceptional classes over projected points

The first blowup over a closed point accounts for the entire scheme-theoretic
inverse image of that point. Its total exceptional class therefore depends on
the inverse-image ideal, even when later centers lie over the same point.
Comparing two such ideals on a common resolution lets one read the same base
order in both Picard markings.
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X X' Y : Scheme.{u}} {n m : ℕ}
  {T : BlowupTower X n Y} {U : BlowupTower X' m Y}

local notation "I[" p "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ p)

section Smooth

variable {k : Type u} [Field k] [PerfectField k] [IsIntegral X] [IsNoetherian X]

/-- The scheme-theoretic inverse image of a projected center is an effective
Cartier divisor whose class is the total exceptional class of the first blowup
over that point. -/
theorem exists_isEffectiveCartier_comap_eq_exceptionalClass (hT : IsClosedPointTower X T)
    (s : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 s]
    {p : X} (hp : IsClosed ({p} : Set X)) (j : Fin n) (hj : hT.baseCenter j = p)
    (hfirst : ∀ l < j, hT.baseCenter l ≠ p) :
    ∃ hE : (I[p].comap T.toBase).IsEffectiveCartier,
      (mk hE.toInvertibleSheaf)⁻¹ = T.exceptionalClass j := by
  cases n with
  | zero => exact j.elim0
  | succ n =>
    obtain ⟨W, V, e, hV, hbase, hclass, _, _⟩ :=
      hT.exists_move_closed_point_blowup_to_front j hp hj hfirst
    let E := I[p].comap I[p].blowupToBase
    let f := e.hom ≫ V.toBase
    have he : E.comap f = I[p].comap T.toBase := by
      rw [← comap_comp, Category.assoc, hbase]
    have hE := I[p].isEffectiveCartier_comap_blowupToBase
    have hfirstStep : IsClosedPointTower X (BlowupTower.nil.snoc I[p]) := .snoc .nil p hp rfl
    have : IsIntegral I[p].blowup := hfirstStep.isIntegral s
    have : SmoothOfRelativeDimension 2 (I[p].blowupToBase ≫ s) := by
      simpa only [toBase_snoc, toBase_nil, Category.comp_id] using
        hfirstStep.smoothOfRelativeDimension s
    have := (BlowupTower.nil.snoc I[p]).isNoetherian
    have hEf : (E.comap f).IsEffectiveCartier := by
      rw [comap_comp]
      exact (hV.isEffectiveCartier_totalTransform (I[p].blowupToBase ≫ s) hE).comap e.hom
    refine ⟨he ▸ hEf, ?_⟩
    rw [← hclass, pullback_comp, blowupExceptionalClass_def, pullback_inv,
      hE.pullback_mk_toInvertibleSheaf hEf]
    exact congrArg Inv.inv (mk_toInvertibleSheaf_congr _ _ he.symm)

/-- On a resolution smooth of relative dimension two, a closed point has a
Cartier inverse image exactly when it is among the projected centers. -/
theorem mem_range_baseCenter_iff_isEffectiveCartier_comap (hT : IsClosedPointTower X T)
    (s : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 s]
    {p : X} (hp : IsClosed ({p} : Set X)) :
    p ∈ Set.range hT.baseCenter ↔ (I[p].comap T.toBase).IsEffectiveCartier := by
  constructor
  · intro h
    obtain ⟨j, hj, hmin⟩ := (wellFounded_lt (α := Fin n)).has_min
      {j | hT.baseCenter j = p} h
    exact (hT.exists_isEffectiveCartier_comap_eq_exceptionalClass s hp j hj
      (fun l hl he ↦ hmin l he hl)).choose
  · intro hE
    by_contra h
    obtain ⟨q, _, _, _, _, hq, _, hI, _, _, _⟩ := hT.exists_prepend_closed_point_blowup hp h
    have hdim := hT.smoothOfRelativeDimension s
    have := T.isNoetherian
    have hC : I[q].IsEffectiveCartier := hI ▸ hE
    have hsupport := Scheme.support_ker_fromSpecResidueField_of_isClosed hq
    have hqI : q ∈ I[q].support := by
      rw [← SetLike.mem_coe, hsupport]
      exact Set.mem_singleton q
    obtain ⟨x, hx, _⟩ := hC.mem_support_iff_exists_codimensionOnePoint.mp hqI
    have hxq : (x : Y) = q := by
      simpa only [← SetLike.mem_coe, hsupport, Set.mem_singleton_iff] using hx
    have hq₂ := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) (T.toBase ≫ s) hq
    have hq₁ : Order.coheight q = 1 := hxq ▸ x.property
    rw [hq₂] at hq₁
    norm_num at hq₁

end Smooth

variable {k : Type u} [Field k] [IsAlgClosed k]
  [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X' ↘ Spec (.of k))]
  [IsIntegral X] [IsIntegral X'] [X.IsProjectiveOver k] [X'.IsProjectiveOver k]

local notation "S" => Spec (CommRingCat.of k)

/-- If two point towers on a common resolution pull back the same closed-point ideal,
their first centers over the respective points give the same negative exceptional
coefficient for any line bundle on the resolution. The second tower has such a center
whenever the first does. -/
theorem base_order_eq_of_comap_point_ideal_eq (hT : IsClosedPointTower X T)
    (hU : IsClosedPointTower X' U)
    (hs : T.toBase ≫ (X ↘ S) = U.toBase ≫ (X' ↘ S))
    {p : X} {p' : X'} (hp : IsClosed ({p} : Set X)) (hp' : IsClosed ({p'} : Set X'))
    (heq : I[p].comap T.toBase = I[p'].comap U.toBase)
    (j : Fin n) (hj : hT.baseCenter j = p) (hfirst : ∀ l < j, hT.baseCenter l ≠ p)
    (L : LineBundleClass Y) :
    let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    let : IsNoetherian X' := isNoetherian_of_finiteType (X' ↘ S)
    let a := (T.picardMarking hT (X ↘ S)).symm (Additive.ofMul L)
    let a' := (U.picardMarking hU (X' ↘ S)).symm (Additive.ofMul L)
    ∃ j' : Fin m, hU.baseCenter j' = p' ∧ (∀ l < j', hU.baseCenter l ≠ p') ∧
      T.exceptionalClass j = U.exceptionalClass j' ∧ -a.2 j = -a'.2 j' := by
  intro hN hN' a a'
  let := hN
  let := hN'
  obtain ⟨hE, hEj⟩ := hT.exists_isEffectiveCartier_comap_eq_exceptionalClass (X ↘ S) hp j hj hfirst
  have hpU := (hU.mem_range_baseCenter_iff_isEffectiveCartier_comap (X' ↘ S) hp').mpr
    (heq ▸ hE)
  obtain ⟨j', hj', hmin⟩ := (wellFounded_lt (α := Fin m)).has_min
    {l | hU.baseCenter l = p'} hpU
  have hfirst' (l : Fin m) (hl : l < j') : hU.baseCenter l ≠ p' := fun h ↦ hmin l h hl
  obtain ⟨hE', hEj'⟩ :=
    hU.exists_isEffectiveCartier_comap_eq_exceptionalClass (X' ↘ S) hp' j' hj' hfirst'
  have hclass := hEj.symm.trans ((congrArg Inv.inv
    (mk_toInvertibleSheaf_congr hE hE' heq)).trans hEj')
  refine ⟨j', hj', hfirst', hclass, ?_⟩
  have ha : (T.picardHom a).toMul = L := by
    rw [← picardMarking_apply T hT (X ↘ S), LinearEquiv.apply_symm_apply, toMul_ofMul]
  have ha' : (U.picardHom a').toMul = L := by
    rw [← picardMarking_apply U hU (X' ↘ S), LinearEquiv.apply_symm_apply, toMul_ofMul]
  have hTj := classIntersectionNumber_picardHom_exceptionalClass (k := k) hT a j
  have hUj := classIntersectionNumber_picardHom_exceptionalClass (k := k) hU a' j'
  rw [ha, hclass] at hTj
  rw [ha'] at hUj
  have hover : (⟨T.toBase ≫ (X ↘ S)⟩ : Y.Over S) = ⟨U.toBase ≫ (X' ↘ S)⟩ :=
    congrArg (fun f : Y ⟶ S ↦ (⟨f⟩ : Y.Over S)) hs
  exact hTj.symm.trans ((congrArg (fun o : Y.Over S ↦
    @Chow.classIntersectionNumber k _ Y o L (U.exceptionalClass j')) hover).trans hUj)

end QPainleve.BlowupTower.IsClosedPointTower

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
import QPainleve.AlgebraicGeometry.Blowup.Picard
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Pi
import TauCeti.AlgebraicGeometry.Morphisms.RelativeDimension
import TauCeti.LinearAlgebra.FreeModule.PID

/-!
# Picard markings of ordered point blowups

The base Picard group and one integer coordinate for each blowup give coordinates on
the Picard group of the final surface. The exceptional generators are the total
transforms of the exceptional divisors at the stages where they were created. These
coordinates are compatible with concatenation and with isomorphisms matching the
ordered centers. A common resolution compares the stabilized Picard groups and transfers
finite generation and freeness.

The marking iterates `Scheme.IdealSheafData.picardBlowupEquiv`, the single-blowup
decomposition in P. Hacking, *583C Lecture notes (Compact Complex Surfaces)*,
Proposition 7.1.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace TauCeti.AlgebraicGeometry
open LineBundleClass

universe u

namespace QPainleve.BlowupTower

section Marking

variable {X Y Z X' Y' : Scheme.{u}} {m n : ℕ}

/-- Pull back a class from the base and add the indicated integral multiples of the
total-transform exceptional classes of the tower. -/
def picardHom (T : BlowupTower X n Y) :
    Additive (LineBundleClass X) × (Fin n → ℤ) →ₗ[ℤ] Additive (LineBundleClass Y) :=
  (pullbackHom T.toBase).toAdditive.toIntLinearMap.coprod
    (LinearMap.lsum ℤ (fun _ : Fin n ↦ ℤ) ℤ
      (fun j ↦ (zmultiplesHom _ (Additive.ofMul (T.exceptionalClass j))).toIntLinearMap))

/-- In additive coordinates, the marking adds the indicated multiples of the total exceptional
classes to the pullback from the base. -/
theorem picardHom_apply (T : BlowupTower X n Y)
    (a : Additive (LineBundleClass X)) (b : Fin n → ℤ) :
    T.picardHom (a, b) =
      Additive.ofMul (pullback T.toBase a.toMul) +
        ∑ j, b j • Additive.ofMul (T.exceptionalClass j) := by
  simp only [picardHom, LinearMap.coprod_apply, AddMonoidHom.coe_toIntLinearMap,
    MonoidHom.toAdditive_apply_apply, pullbackHom_apply,
    LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    zmultiplesHom_apply]

/-- The tower map is the pullback of the base class tensored with the product of the exceptional
line bundles to their specified powers. -/
theorem picardHom_apply_toMul (T : BlowupTower X n Y)
    (a : Additive (LineBundleClass X)) (b : Fin n → ℤ) :
    (T.picardHom (a, b)).toMul =
      pullback T.toBase a.toMul * ∏ j, T.exceptionalClass j ^ b j := by
  simp only [picardHom_apply, toMul_add, toMul_sum, toMul_zsmul, toMul_ofMul]

/-- The base summand maps to the pullback along the projection of the tower. -/
@[simp]
theorem picardHom_apply_zero (T : BlowupTower X n Y) (a : Additive (LineBundleClass X)) :
    (T.picardHom (a, 0)).toMul = pullback T.toBase a.toMul := by
  simp [picardHom_apply_toMul]

/-- A coefficient supported at one stage gives the corresponding power of its exceptional class. -/
@[simp]
theorem picardHom_apply_single (T : BlowupTower X n Y) (j : Fin n) (b : ℤ) :
    (T.picardHom (0, Pi.single j b)).toMul = T.exceptionalClass j ^ b := by
  rw [picardHom_apply_toMul, toMul_zero, pullback_one, one_mul]
  classical
  rw [Finset.prod_eq_single j (fun i _ hi ↦ by rw [Pi.single_eq_of_ne hi, zpow_zero])
    (by simp), Pi.single_eq_same]

@[simp]
theorem picardHom_nil (a : Additive (LineBundleClass X)) (b : Fin 0 → ℤ) :
    (nil (X := X)).picardHom (a, b) = a := by
  apply Additive.toMul.injective
  simp [picardHom_apply_toMul]

/-- Marking a concatenated tower first uses the coordinates for the initial tower and then
uses the coordinates for the following tower. -/
theorem picardHom_append (T : BlowupTower X m Y) (U : BlowupTower Y n Z)
    (a : Additive (LineBundleClass X)) (b : Fin (m + n) → ℤ) :
    (T.append U).picardHom (a, b) =
      U.picardHom (T.picardHom (a, fun j ↦ b (j.castAdd n)), fun j ↦ b (j.natAdd m)) := by
  apply Additive.toMul.injective
  simp only [picardHom_apply_toMul, toBase_append, Fin.prod_univ_add,
    exceptionalClass_append_castAdd, exceptionalClass_append_natAdd, ← pullback_comp,
    pullback_mul, ← pullback_zpow, mul_assoc]
  rw [← pullbackHom_apply (f := U.toBase) (a := ∏ j : Fin m, _), map_prod]
  simp only [pullbackHom_apply]

/-- At a new stage the earlier coordinates are pulled back and the last coordinate gives
the power of the new exceptional divisor. -/
theorem picardHom_snoc_apply_toMul (T : BlowupTower X n Y) (I : Y.IdealSheafData)
    (a : Additive (LineBundleClass X)) (b : Fin (n + 1) → ℤ) :
    ((T.snoc I).picardHom (a, b)).toMul =
      pullback I.blowupToBase (T.picardHom (a, fun j ↦ b j.castSucc)).toMul *
        I.blowupExceptionalClass ^ b (Fin.last n) := by
  simp only [picardHom_apply_toMul, toBase_snoc, Fin.prod_univ_castSucc,
    exceptionalClass_snoc_castSucc, exceptionalClass_snoc_last,
    Scheme.IdealSheafData.blowupExceptionalClass_def, ← pullback_comp, pullback_mul,
    ← pullback_zpow, mul_assoc]
  rw [← pullbackHom_apply (f := I.blowupToBase) (a := ∏ j : Fin n, _), map_prod]
  simp only [pullbackHom_apply]

/-- A morphism over a base map that preserves the ordered total exceptional classes
pulls back the marked base class and retains the exceptional coefficients. -/
theorem pullback_picardHom {T : BlowupTower X n Y} {T' : BlowupTower X' n Y'}
    {f : X ⟶ X'} {g : Y ⟶ Y'} (h : g ≫ T'.toBase = T.toBase ≫ f)
    (hE : ∀ j, pullback g (T'.exceptionalClass j) = T.exceptionalClass j)
    (a : Additive (LineBundleClass X')) (b : Fin n → ℤ) :
    pullback g (T'.picardHom (a, b)).toMul =
      (T.picardHom (Additive.ofMul (pullback f a.toMul), b)).toMul := by
  rw [picardHom_apply_toMul, picardHom_apply_toMul, pullback_mul, pullback_comp,
    h, ← pullback_comp, ← pullbackHom_apply (f := g) (a := ∏ j, _)]
  simp only [map_prod, pullbackHom_apply, pullback_zpow, hE, toMul_ofMul]

/-- A lift through two towers pulls back the marked classes by pulling back their base
classes and retaining their ordered exceptional coefficients. -/
theorem IsLift.pullback_picardHom {T : BlowupTower X n Y} {T' : BlowupTower X' n Y'}
    {e : X ≅ X'} {g : Y ≅ Y'} (h : IsLift e T T' g)
    (a : Additive (LineBundleClass X')) (b : Fin n → ℤ) :
    pullback g.hom (T'.picardHom (a, b)).toMul =
      (T.picardHom (Additive.ofMul (pullback e.hom a.toMul), b)).toMul :=
  BlowupTower.pullback_picardHom h.hom_toBase h.pullback_exceptionalClass a b

private theorem bijective_picardHom_snoc {T : BlowupTower X n Y}
    (hT : Function.Bijective T.picardHom) [IsIntegral Y] [IsNoetherian Y]
    (I : Y.IdealSheafData) [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]
    [∀ y : I.blowup, UniqueFactorizationMonoid (I.blowup.presheaf.stalk y)] {p : Y}
    (hI : (I.support : Set Y) = {p}) (hp : 1 < coheight p)
    (hE : (I.comap I.blowupToBase).IsExceptionalCurveOfFirstKind) :
    Function.Bijective (T.snoc I).picardHom := by
  let split : (Fin (n + 1) → ℤ) ≃ (Fin n → ℤ) × ℤ :=
    ((Equiv.piCongrLeft' (fun _ ↦ ℤ) finSuccEquivLast).trans
      Equiv.piOptionEquivProd).trans (Equiv.prodComm _ _)
  let e := ((Equiv.refl (Additive (LineBundleClass X))).prodCongr split).trans
    (Equiv.prodAssoc _ _ _).symm
  let P := I.picardBlowupEquiv hI hp hE
  have heq : (T.snoc I).picardHom =
      P ∘ Prod.map T.picardHom id ∘ e := by
    funext a
    apply Additive.toMul.injective
    rw [Function.comp_apply, Function.comp_apply, I.picardBlowupEquiv_apply_toMul,
      picardHom_snoc_apply_toMul, Scheme.IdealSheafData.blowupExceptionalClass_def]
    simp [e, split, Equiv.piCongrLeft'_apply]
  rw [heq]
  exact P.bijective.comp ((hT.prodMap Function.bijective_id).comp e.bijective)

/-- The tower map is bijective for a tower of closed point blowups of an integral
Noetherian smooth surface over a perfect field. -/
theorem IsClosedPointTower.bijective_picardHom {k : Type u} [Field k] [PerfectField k]
    [IsIntegral X] [IsNoetherian X] {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f] :
    Function.Bijective T.picardHom := by
  induction hT with
  | nil =>
    convert (Equiv.prodUnique (Additive (LineBundleClass X)) (Fin 0 → ℤ)).bijective using 1
    ext a
    exact picardHom_nil a.1 a.2
  | @snoc _ W S I hS p hp hI ih =>
    subst I
    let g := S.toBase ≫ f
    let I := (W.fromSpecResidueField p).ker
    have : IsNoetherian W := S.isNoetherian
    have : IsIntegral W := hS.isIntegral f
    have : SmoothOfRelativeDimension 2 g := hS.smoothOfRelativeDimension f
    have : Smooth g := SmoothOfRelativeDimension.smooth 2 g
    have : IsRegular W := IsRegular.of_smooth g
    have : IsClosedImmersion (W.fromSpecResidueField p) :=
      isClosed_singleton_iff_isClosedImmersion.mp hp
    have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq g 2).mp inferInstance).2 p hp
    have hcodim := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) g hp
    have : ∀ x : W, UniqueFactorizationMonoid (W.presheaf.stalk x) := fun x ↦
      IsRegular.uniqueFactorizationMonoid_stalk x
        (coheight_le_of_relativeDimensionLE_of_field (d := 2) g x)
    have : IsIntegral I.blowup := (hS.snoc p hp rfl).isIntegral f
    have : SmoothOfRelativeDimension 2 (I.blowupToBase ≫ g) := by
      rw [← Category.assoc, ← toBase_snoc]
      exact (hS.snoc p hp rfl).smoothOfRelativeDimension f
    have : Smooth (I.blowupToBase ≫ g) := SmoothOfRelativeDimension.smooth 2 _
    have : IsRegular I.blowup := IsRegular.of_smooth (I.blowupToBase ≫ g)
    have : ∀ x : I.blowup, UniqueFactorizationMonoid (I.blowup.presheaf.stalk x) := fun x ↦
      IsRegular.uniqueFactorizationMonoid_stalk x
        (coheight_le_of_relativeDimensionLE_of_field (d := 2) (I.blowupToBase ≫ g) x)
    apply bijective_picardHom_snoc ih I (p := p)
    · simp [I, Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField]
    · rw [hcodim]
      norm_num
    · exact Scheme.IdealSheafData.isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint
        p hp hdim

/-- Pullback along an ordered tower of closed point blowups is injective on Picard classes. -/
theorem IsClosedPointTower.injective_pullback_toBase {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y} [IsIntegral X] [IsNoetherian X]
    (hT : IsClosedPointTower X T) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f] :
    Function.Injective (pullback T.toBase) := by
  intro L M h
  have h' : (T.picardHom (Additive.ofMul L, 0)).toMul =
      (T.picardHom (Additive.ofMul M, 0)).toMul := by
    simpa only [picardHom_apply_zero, toMul_ofMul] using h
  exact Additive.ofMul.injective (congrArg Prod.fst
    ((hT.bijective_picardHom f).injective (Additive.toMul.injective h')))

/-- For an automorphism lifting through an ordered point blowup tower, pullback acts
trivially on the final Picard group exactly when it acts trivially on the base Picard group. -/
theorem IsLift.forall_pullback_eq_iff {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f] {a : X ≅ X} {g : Y ≅ Y}
    (h : IsLift a T T g) (hT : IsClosedPointTower X T) :
    (∀ L, pullback g.hom L = L) ↔ ∀ L, pullback a.hom L = L := by
  have hbij := hT.bijective_picardHom f
  constructor
  · intro hg L
    have hpair := hbij.injective (Additive.toMul.injective
      ((h.pullback_picardHom (Additive.ofMul L) 0).symm.trans (hg _)))
    exact congrArg (fun z : Additive (LineBundleClass X) × (Fin n → ℤ) ↦ z.1.toMul) hpair
  · intro ha L
    obtain ⟨⟨b, c⟩, hb⟩ := hbij.surjective (Additive.ofMul L)
    have hb' : (T.picardHom (b, c)).toMul = L := congrArg Additive.toMul hb
    rw [← hb', h.pullback_picardHom, ha, ofMul_toMul]

variable {k : Type u} [Field k] [PerfectField k] [IsIntegral X] [IsNoetherian X]
  (T : BlowupTower X n Y) (hT : IsClosedPointTower X T)
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]

/-- The canonical integral Picard marking for an ordered tower of point blowups. -/
def picardMarking : (Additive (LineBundleClass X) × (Fin n → ℤ)) ≃ₗ[ℤ]
    Additive (LineBundleClass Y) :=
  LinearEquiv.ofBijective T.picardHom (hT.bijective_picardHom f)

@[simp]
theorem picardMarking_apply (a : Additive (LineBundleClass X) × (Fin n → ℤ)) :
    T.picardMarking hT f a = T.picardHom a := (rfl)

end Marking

section CommonResolution

local notation "Pic(" S ")" => Additive (LineBundleClass S)

variable {X Y Z W : Scheme.{u}} {m n : ℕ}
  {T : BlowupTower X m Y} {U : BlowupTower Z n W}
  (k : Type u) [Field k] [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
  [IsIntegral X] [IsIntegral Z]

local notation "fX" => (X ↘ Spec (CommRingCat.of k))
local notation "fZ" => (Z ↘ Spec (CommRingCat.of k))

variable [PerfectField k] [IsNoetherian X] [IsNoetherian Z]

/-- The two Picard markings on a common resolution identify the base Picard groups after
adding one integral coordinate for each point blowup on the respective side. -/
def picardEquivOfCommonResolution
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U) (e : W ≅ Y) :
    (Pic(X) × (Fin m → ℤ)) ≃ₗ[ℤ] (Pic(Z) × (Fin n → ℤ)) :=
  (T.picardMarking hT fX).trans
    (((LineBundleClass.pullbackEquiv e).toAdditive.toIntLinearEquiv).trans
      (U.picardMarking hU fZ).symm)

/-- On the common resolution, the identification of Picard coordinates is pullback
along the isomorphism of the final schemes. -/
@[simp]
theorem picardHom_picardEquivOfCommonResolution
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U) (e : W ≅ Y)
    (a : Pic(X) × (Fin m → ℤ)) :
    U.picardHom (picardEquivOfCommonResolution k hT hU e a) =
      Additive.ofMul (LineBundleClass.pullback e.hom (T.picardHom a).toMul) := by
  rw [← U.picardMarking_apply hU fZ, ← T.picardMarking_apply hT fX]
  simp [picardEquivOfCommonResolution, LineBundleClass.pullbackEquiv_apply]

include k in
/-- Finite generation of the integral Picard group transfers across a common
resolution by towers of closed point blowups. -/
theorem finite_picard_iff_of_common_resolution
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U) (e : W ≅ Y) :
    Module.Finite ℤ (Pic(X)) ↔ Module.Finite ℤ (Pic(Z)) := by
  let E := picardEquivOfCommonResolution k hT hU e
  exact ⟨fun _ ↦ Module.Finite.of_surjective ((LinearMap.fst ℤ _ _).comp E.toLinearMap)
    ((LinearMap.fst_surjective (R := ℤ)).comp E.surjective),
    fun _ ↦ Module.Finite.of_surjective ((LinearMap.fst ℤ _ _).comp E.symm.toLinearMap)
      ((LinearMap.fst_surjective (R := ℤ)).comp E.symm.surjective)⟩

include k in
/-- Freeness of the integral Picard group transfers across a common resolution
by towers of closed point blowups. -/
theorem free_picard_iff_of_common_resolution
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U) (e : W ≅ Y) :
    Module.Free ℤ (Pic(X)) ↔ Module.Free ℤ (Pic(Z)) := by
  let E := picardEquivOfCommonResolution k hT hU e
  exact ⟨fun _ ↦ Module.Free.of_injective_of_projective_of_isPrincipalIdealRing
    (E.symm.toLinearMap.comp (LinearMap.inl ℤ _ _))
    (E.symm.injective.comp LinearMap.inl_injective),
    fun _ ↦ Module.Free.of_injective_of_projective_of_isPrincipalIdealRing
      (E.toLinearMap.comp (LinearMap.inl ℤ _ _))
      (E.injective.comp LinearMap.inl_injective)⟩

include k in
/-- For a finitely generated Picard group, its rank increases by the length of a tower
of closed point blowups. -/
theorem finrank_picard [Module.Finite ℤ (Pic(X))] (hT : IsClosedPointTower X T) :
    Module.finrank ℤ (Pic(Y)) = Module.finrank ℤ (Pic(X)) + m := by
  let p := LinearMap.fst ℤ (Pic(X)) (Fin m → ℤ)
  have h := p.ker.finrank_quotient_add_finrank
  rw [(p.quotKerEquivOfSurjective LinearMap.fst_surjective).finrank_eq,
    LinearMap.ker_fst, LinearMap.finrank_range_of_inj LinearMap.inr_injective] at h
  rw [← (T.picardMarking hT fX).finrank_eq]
  simpa using h.symm

end CommonResolution

end QPainleve.BlowupTower

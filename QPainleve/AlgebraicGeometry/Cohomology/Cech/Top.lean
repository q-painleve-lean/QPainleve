/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Cech.Linear
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Ordered.HomotopyEquiv

/-!
# Top Čech classes of finite affine covers

For a cover numbered by `Fin (n + 1)`, an ordered top cochain is a single section on
the full intersection. It is automatically a cocycle. A linear functional annihilating
the preceding differential
descends to sheaf cohomology.
-/

public noncomputable section

open CategoryTheory Limits Opposite TauCeti.CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
  {n : ℕ} {ι : Type u} [LinearOrder ι] (e : Fin (n + 1) ≃o ι)
  (U : ι → X.Opens) (M : X.Modules)

local notation "P" M:arg => Functor.obj (sectionsBasePresheafFunctor R) M
local notation "C" M:arg => Functor.obj (strictMonoCechComplexFunctor U) (P M)

private theorem topCechTuple_eq
    (a : {a : Fin (n + 1) → ι // StrictMono a}) : a = ⟨e, e.strictMono⟩ := by
  apply Subtype.ext
  have h := congrFun (e.symm.strictMono.comp a.property).eq_id
  funext i
  simpa only [Function.comp_apply, id_eq, e.apply_symm_apply] using congrArg e (h i)

private def topCechProjection :
    (C M).X n ≅ (P M).obj (op (∏ᶜ (U ∘ e))) where
  hom := strictMonoCechComplexπ U (P M) ⟨e, e.strictMono⟩
  inv := strictMonoCechComplexLift U (P M) fun a ↦
    eqToHom (congrArg (fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦
      (P M).obj (op (∏ᶜ fun j ↦ U (a.val j)))) (topCechTuple_eq e a).symm)
  hom_inv_id := by
    apply strictMonoCechComplexFunctor_obj_X_hom_ext
    intro a
    rw [topCechTuple_eq e a]
    simp
  inv_hom_id := by simp

include e in
private theorem topCech_d_eq_zero : (C M).d n (n + 1) = 0 := by
  have : Finite ι := Finite.of_equiv _ e.toEquiv
  have h : Nat.card ι = n + 1 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_fin]
  exact (isZero_strictMonoCechComplexFunctor_obj_X U h.le (P M)).eq_of_tgt _ _

private def topCechCycles : (C M).cycles n ≅ (P M).obj (op (∏ᶜ (U ∘ e))) :=
  (C M).iCyclesIso n (n + 1) ((ComplexShape.up ℕ).next_eq' rfl)
    (topCech_d_eq_zero e U M) ≪≫ topCechProjection e U M

private theorem topCechCycles_hom :
    (topCechCycles e U M).hom =
      (C M).iCycles n ≫ strictMonoCechComplexπ U (P M) ⟨e, e.strictMono⟩ :=
  by rw [topCechCycles, Iso.trans_hom, HomologicalComplex.iCyclesIso_hom]; rfl

variable (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U))
  (hcover : ⨆ i, U i = ⊤) [M.IsQuasicoherent]

private def topCechComparison : (C M).homology n ≃ₗ[R] Cohomology M n :=
  ((strictMonoCechComplexHomotopyEquiv U (P M)).toHomologyIso n).symm.toLinearEquiv ≪≫ₗ
    homologyCechComplexLinearEquiv U hU hcover M n

/-- The cohomology class of a section on the full intersection of an ordered affine cover
of `n + 1` opens, in degree `n`. -/
def topCechCohomologyClass :
    (P M).obj (op (∏ᶜ (U ∘ e))) →ₗ[R] Cohomology M n :=
  (topCechComparison U M hU hcover).toLinearMap.comp
    (((topCechCycles e U M).inv ≫ (C M).homologyπ n).hom)

/-- Every degree-`n` class is represented by a section on the full intersection of an
affine cover with `n + 1` members. -/
theorem surjective_topCechCohomologyClass :
    Function.Surjective (topCechCohomologyClass (R := R) e U M hU hcover) :=
  (topCechComparison U M hU hcover).surjective.comp
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

omit [M.IsQuasicoherent] in
private theorem topCech_d_comp_eq_zero {V : ModuleCat.{u} R}
    (f : (P M).obj (op (∏ᶜ (U ∘ e))) ⟶ V)
    (hf : ∀ i : Fin (n + 1),
      (P M).map (Pi.lift fun j : Fin n ↦ Pi.π (U ∘ e) (i.succAbove j)).op ≫ f = 0)
    (j : ℕ) :
    (C M).d j n ≫ strictMonoCechComplexπ U (P M) ⟨e, e.strictMono⟩ ≫ f = 0 := by
  by_cases h : (ComplexShape.up ℕ).Rel j n
  · obtain rfl : j + 1 = n := h
    simp only [strictMonoCechComplexFunctor_obj_d_comp_π_assoc,
      Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
    simp only [Function.comp_def] at hf ⊢
    exact Finset.sum_eq_zero fun i _ ↦ by rw [hf i, comp_zero, smul_zero]
  · rw [(C M).shape _ _ h, zero_comp]

/-- A linear map from sections on the full intersection which kills the restricted
sections from each face of the ordered top simplex descends to cohomology. -/
def topCechCohomologyDesc {V : ModuleCat.{u} R}
    (f : (P M).obj (op (∏ᶜ (U ∘ e))) ⟶ V)
    (hf : ∀ i : Fin (n + 1),
      (P M).map (Pi.lift fun j : Fin n ↦ Pi.π (U ∘ e) (i.succAbove j)).op ≫ f = 0) :
    Cohomology M n →ₗ[R] V :=
  let descend := ((C M).sc n).descHomology ((topCechCycles e U M).hom ≫ f) <| by
    -- The short complex uses the predecessor selected by the cochain shape.
    change (C M).toCycles ((ComplexShape.up ℕ).prev n) n ≫ (topCechCycles e U M).hom ≫ f = 0
    simp only [topCechCycles_hom, ← Category.assoc, HomologicalComplex.toCycles_i]
    rw [Category.assoc]
    exact topCech_d_comp_eq_zero e U M f hf _
  descend.hom.comp (topCechComparison U M hU hcover).symm.toLinearMap

/-- The descended map evaluates a top Čech class by applying the original map to its
representing section. -/
@[simp]
theorem topCechCohomologyDesc_class {V : ModuleCat.{u} R}
    (f : (P M).obj (op (∏ᶜ (U ∘ e))) ⟶ V) (hf) (x : (P M).obj (op (∏ᶜ (U ∘ e)))) :
    topCechCohomologyDesc e U M hU hcover f hf
      (topCechCohomologyClass e U M hU hcover x) = f x := by
  simp only [topCechCohomologyDesc, topCechCohomologyClass, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Category.assoc, HomologicalComplex.homologyπ,
    ShortComplex.π_descHomology, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Modules

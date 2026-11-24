/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Subdivision
public import QPainleve.Geometry.Toric.Fan.Boundary.Period
public import QPainleve.Geometry.Toric.Fan.Picard.Period.Restriction
public import QPainleve.Geometry.Toric.Fan.TorusAction.ContractedAlignment

/-!
# Center variation of marked boundary periods

The period of a charge relation is the period of its marked boundary-orthogonal
line bundle. On comparing two sets of centers the common toric class cancels.
Each center ideal quotient then contributes its period, raised to the corresponding
charge coordinate. The conductor subdivision formula transports the result to the
original boundaries.

The center comparison follows
[Gross, Hacking and Keel, Proposition 2.9](https://arxiv.org/html/1211.6367v5#S2),
using `Fan.pullback_toricBoundaryToBase_markedCharge_div` for the quotient of
the marked restrictions and `Fan.exists_internalCenterRatio_nodalPicardCycleMulEquiv`
for the period of one center quotient. Equal periods then recover the ordered centers
up to a torus translation, as in Corollary 2.10 of the same paper.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open Scheme (IdealSheafData NodalCycleNumbering)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Dtor" => Fan.boundaryIdeal Φ inferInstance
local notation "C" => IdealSheafData.subscheme Dtor
local notation "ChargeKernel" => LinearMap.ker (rayChargeMap s)
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "m" =>
  (fun j ↦ LinearMap.toAddMonoidHom (Module.Basis.detDualEquiv b (Ray.primitiveGenerator (s j))))
local notation "hm" => (fun j ↦ Module.Basis.detDualEquiv_self b (Ray.primitiveGenerator (s j)))
local notation "hprim" => (fun j ↦ Ray.surjective_detCharacter (s j) b)
local notation "J[" c "]" => (fun j ↦ Ray.internalCenter b (s j) (c j))
local notation "hJ[" c "]" => (fun j ↦ Ray.internalCenter_val b (s j) (c j))
local notation "ν[" W "]" => IdealSheafData.blowupToBase (Scheme.singularLocus ℂ W)
local notation "P[" W "]" => MonoidHom.ker (LineBundleClass.pullbackHom ν[W])
local notation "F[" W "]" => Scheme.branchSchemeToBlowup ℂ W
local notation "nodes[" W "]" => IdealSheafData.subscheme (Scheme.singularLocus ℂ W)

private theorem transport_presentation {X Y : Scheme} [X.Over S] {D : X.IdealSheafData}
    {length : ℕ} {P : QPainleve.BlowupTower X length Y}
    {U W : Σ Z, WithBoundary (Dtor).subschemeι n Z}
    (h : U = W) (e : Y ≅ W.1)
    (he : e.inv ≫ P.toBase ≫ (X ↘ S) = W.2.toTower.toBase ≫ (Φ.algebraicRealization ↘ S))
    (hD : ((D.comap P.toBase).comap e.inv).support = W.2.boundaryι.ker.support) :
    let a := e ≪≫ eqToIso (congrArg Sigma.fst h).symm
    a.inv ≫ P.toBase ≫ (X ↘ S) = U.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap ∧
      ((D.comap P.toBase).comap a.inv).support = U.2.boundaryι.ker.support := by
  subst W
  simpa only [eqToIso_refl, Iso.trans_refl, ← algebraicRealization_over] using
    And.intro he hD

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]

section Presentation

variable {c : Fin n → ℂˣ}
  {X Y : Scheme} [X.Over S] [X.IsProjectiveOver ℂ] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ S)]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm ℂ X)]
  {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
  (e : Y ≅ (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter b (c j))).1)
  (he : e.inv ≫ T.toBase ≫ (X ↘ S) =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter b (c j))).2.toTower.toBase ≫ (Φ.algebraicRealization ↘ S))
  (hD : ((D.comap T.toBase).comap e.inv).support =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter b (c j))).2.boundaryι.ker.support)

local notation "charge" =>
  picardBoundaryOrthogonalEquivChargeKernel hΦ rankTwo s m hm hprim c (J[c]) (hJ[c]) hT e he hD
local notation "chargeClass" =>
  (LinearEquiv.trans (LinearEquiv.symm charge)
    (LinearEquiv.ofEq _ _ (Eq.symm (IdealSheafData.boundaryOrthogonal_def D ℂ))))

/-- The charge coordinates identify the boundary-orthogonal classes on the contracted
surface with the kernel of the charge map of its ordered toric presentation. -/
def markedBoundaryChargeEquiv : D.boundaryOrthogonal ℂ ≃ₗ[ℤ] ChargeKernel :=
  (chargeClass).symm

/-- The inverse charge coordinates give the same underlying Picard class as the
inverse of the span-based comparison. -/
@[simp]
theorem coe_markedBoundaryChargeEquiv_symm (x : ChargeKernel) :
    ((markedBoundaryChargeEquiv hΦ b s hT e he hD).symm x).val = ((charge).symm x).val := by
  simp only [markedBoundaryChargeEquiv, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply]

local notation "g" => toricBoundaryToBase (J[c]) e hD

variable [PrestableFamily (D.subscheme ↘ S)]
  (hCartier : D.IsEffectiveCartier)
  (hgenus : ∀ v : irreducibleComponents (D.subscheme.singularLocus ℂ).blowup,
    (D.subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
  {α : Type*} {p : α → (D.subscheme ↘ S).smoothLocus} {a : ℕ} [NeZero a]
  (A : NodalCycleNumbering p a)

/-- The period character written in the charge coordinates of an ordered toric presentation. -/
def markedBoundaryPeriod : Multiplicative ChargeKernel →* ℂˣ :=
  (hCartier.boundaryPeriod hgenus A.endpoint_eq).comp
    (chargeClass).toAddMonoidHom.toMultiplicative

/-- Evaluate the marked period on a charge relation by taking its inverse image in
the boundary-orthogonal Picard lattice. -/
theorem markedBoundaryPeriod_apply (x : ChargeKernel) :
    markedBoundaryPeriod hΦ b s hT e he hD hCartier hgenus A (Multiplicative.ofAdd x) =
      hCartier.boundaryPeriod hgenus A.endpoint_eq (Multiplicative.ofAdd (chargeClass x)) :=
  (rfl)

/-- Writing the boundary period in charge coordinates preserves and detects
injectivity. -/
theorem markedBoundaryPeriod_injective_iff :
    Function.Injective (markedBoundaryPeriod hΦ b s hT e he hD hCartier hgenus A) ↔
      Function.Injective (hCartier.boundaryPeriod hgenus A.endpoint_eq) :=
  Function.Injective.of_comp_iff' _ (chargeClass).toAddEquiv.toMultiplicative.bijective

variable [PrestableFamily ((Φ.boundaryIdeal inferInstance).subscheme ↘ Spec (.of ℂ))]
  {β : Type*} {q : β → ((Φ.boundaryIdeal inferInstance).subscheme ↘ S).smoothLocus}
  {k : ℕ} [NeZero k]
  (B : NodalCycleNumbering q k)

/-- The restriction of a marked charge class pulled back to the toric boundary has the
same period as on the original boundary when the boundary projection is an oriented
subdivision on the conductor. -/
theorem exists_pullback_markedBoundaryPeriod
    {gν : ((C).singularLocus ℂ).blowup ⟶ (D.subscheme.singularLocus ℂ).blowup}
    (hν : CommSq ν[C] gν g ν[D.subscheme])
    (hnodes : Set.MapsTo g ((C).singularLocus ℂ).support (D.subscheme.singularLocus ℂ).support)
    (keep : nodes[D.subscheme] ↪ nodes[C])
    (hkeep : ∀ z j,
      gν (F[C] ((C).branchOrderOfDualGraph q B.order (keep z) j).val) =
        F[D.subscheme] (D.subscheme.branchOrderOfDualGraph p A.order z j).val)
    (hcollapse : ∀ z ∉ Set.range keep,
      gν (F[C] ((C).branchOrderOfDualGraph q B.order z 1).val) =
        gν (F[C] ((C).branchOrderOfDualGraph q B.order z 0).val))
    (x : ChargeKernel) :
    ∃ L : P[C],
      L.val = pullback g (pullback D.subschemeι ((charge).symm x).val.toMul) ∧
      (C).nodalPicardCycleMulEquiv B.endpoint_eq L =
        markedBoundaryPeriod hΦ b s hT e he hD hCartier hgenus A (Multiplicative.ofAdd x) := by
  let := isOver_toricBoundaryToBase (J[c]) e he hD
  let L := hCartier.restrictBoundaryOrthogonal hgenus (Multiplicative.ofAdd (chargeClass x))
  obtain ⟨hL, hperiod⟩ := (g).nodalPicardCycleMulEquiv_pullback_of_subdivision
    hν B.endpoint_eq A.endpoint_eq hnodes keep hkeep hcollapse L
  refine ⟨⟨_, hL⟩, ?_, ?_⟩
  · simp only [L, IsEffectiveCartier.restrictBoundaryOrthogonal_apply, toAdd_ofAdd,
      LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  · rw [markedBoundaryPeriod_apply, IsEffectiveCartier.boundaryPeriod_apply]
    exact hperiod

end Presentation

section CenterRatio

variable {c₀ c₁ : Fin n → ℂˣ}
  {X₀ X₁ Y₀ Y₁ : Scheme}
  [X₀.Over S] [X₀.IsProjectiveOver ℂ] [IsIntegral X₀]
  [SmoothOfRelativeDimension 2 (X₀ ↘ S)]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm ℂ X₀)]
  [X₁.Over S] [X₁.IsProjectiveOver ℂ] [IsIntegral X₁]
  [SmoothOfRelativeDimension 2 (X₁ ↘ S)]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm ℂ X₁)]
  {D₀ : X₀.IdealSheafData} {D₁ : X₁.IdealSheafData}
  {d₀ d₁ : ℕ} {T₀ : QPainleve.BlowupTower X₀ d₀ Y₀} {T₁ : QPainleve.BlowupTower X₁ d₁ Y₁}
  (hT₀ : IsNodalBoundaryTower D₀ (X₀ ↘ S) (𝟙 X₀) T₀)
  (hT₁ : IsNodalBoundaryTower D₁ (X₁ ↘ S) (𝟙 X₁) T₁)
  (e₀ : Y₀ ≅ (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter b (c₀ j))).1)
  (e₁ : Y₁ ≅ (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter b (c₁ j))).1)
  (he₀ : e₀.inv ≫ T₀.toBase ≫ (X₀ ↘ S) =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter b (c₀ j))).2.toTower.toBase ≫ (Φ.algebraicRealization ↘ S))
  (he₁ : e₁.inv ≫ T₁.toBase ≫ (X₁ ↘ S) =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter b (c₁ j))).2.toTower.toBase ≫ (Φ.algebraicRealization ↘ S))
  (hD₀ : ((D₀.comap T₀.toBase).comap e₀.inv).support =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter b (c₀ j))).2.boundaryι.ker.support)
  (hD₁ : ((D₁.comap T₁.toBase).comap e₁.inv).support =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter b (c₁ j))).2.boundaryι.ker.support)

variable [PrestableFamily (D₀.subscheme ↘ S)] [PrestableFamily (D₁.subscheme ↘ S)]
  (hCartier₀ : D₀.IsEffectiveCartier) (hCartier₁ : D₁.IsEffectiveCartier)
  (hgenus₀ : ∀ v : irreducibleComponents (D₀.subscheme.singularLocus ℂ).blowup,
    (D₀.subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
  (hgenus₁ : ∀ v : irreducibleComponents (D₁.subscheme.singularLocus ℂ).blowup,
    (D₁.subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
  {α₀ α₁ : Type*} {p₀ : α₀ → (D₀.subscheme ↘ S).smoothLocus}
  {p₁ : α₁ → (D₁.subscheme ↘ S).smoothLocus} {a₀ a₁ : ℕ} [NeZero a₀] [NeZero a₁]
  (A₀ : NodalCycleNumbering p₀ a₀) (A₁ : NodalCycleNumbering p₁ a₁)

local notation "period₀" => markedBoundaryPeriod hΦ b s hT₀ e₀ he₀ hD₀ hCartier₀ hgenus₀ A₀
local notation "period₁" => markedBoundaryPeriod hΦ b s hT₁ e₁ he₁ hD₁ hCartier₁ hgenus₁ A₁

variable [PrestableFamily ((Φ.boundaryIdeal inferInstance).subscheme ↘ Spec (.of ℂ))]
  {β : Type*} {q : β → ((Φ.boundaryIdeal inferInstance).subscheme ↘ S).smoothLocus}
  {k : ℕ} [NeZero k]
  (B : NodalCycleNumbering q k) (r : ZMod k ≃ Φ.Ray)
  (hcomp : ∀ j, (Φ.boundaryIdeal inferInstance).subscheme.dualGraphVertexEquiv q (B.vertex j) =
    Φ.boundaryNormalizationComponentEquiv hΦ (r j))
  (hdet : ∀ j, b.detDualEquiv (r j).primitiveGenerator (r (j + 1)).primitiveGenerator = 1)
  (hnodes : ∀ j, ∃ σ : Φ.cones, (r j).toCone ≤ σ ∧ (r (j + 1)).toCone ≤ σ ∧
    (Φ.boundaryIdeal inferInstance).subschemeι
      ((Φ.boundaryIdeal inferInstance).subscheme.dualGraphEdgeEquiv q (B.edge j)).val =
      Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))

local notation "boundaryOf(" φ ")" => IdealSheafData.subscheme (Fan.boundaryIdeal φ inferInstance)

variable
    {gν₀ : (boundaryOf(Φ).singularLocus ℂ).blowup ⟶
      (D₀.subscheme.singularLocus ℂ).blowup}
    {gν₁ : (boundaryOf(Φ).singularLocus ℂ).blowup ⟶
      (D₁.subscheme.singularLocus ℂ).blowup}
    (hν₀ : CommSq ν[boundaryOf(Φ)] gν₀
      (toricBoundaryToBase (fun j ↦ (s j).internalCenter b (c₀ j)) e₀ hD₀) ν[D₀.subscheme])
    (hν₁ : CommSq ν[boundaryOf(Φ)] gν₁
      (toricBoundaryToBase (fun j ↦ (s j).internalCenter b (c₁ j)) e₁ hD₁) ν[D₁.subscheme])
    (hnodes₀ : Set.MapsTo (toricBoundaryToBase (fun j ↦ (s j).internalCenter b (c₀ j)) e₀ hD₀)
      (boundaryOf(Φ).singularLocus ℂ).support
      (D₀.subscheme.singularLocus ℂ).support)
    (hnodes₁ : Set.MapsTo (toricBoundaryToBase (fun j ↦ (s j).internalCenter b (c₁ j)) e₁ hD₁)
      (boundaryOf(Φ).singularLocus ℂ).support
      (D₁.subscheme.singularLocus ℂ).support)
    (keep₀ : nodes[D₀.subscheme] ↪ nodes[boundaryOf(Φ)])
    (keep₁ : nodes[D₁.subscheme] ↪ nodes[boundaryOf(Φ)])
    (hkeep₀ : ∀ z j,
      gν₀ (F[boundaryOf(Φ)] (boundaryOf(Φ).branchOrderOfDualGraph q B.order (keep₀ z) j).val) =
        F[D₀.subscheme] (D₀.subscheme.branchOrderOfDualGraph p₀ A₀.order z j).val)
    (hkeep₁ : ∀ z j,
      gν₁ (F[boundaryOf(Φ)] (boundaryOf(Φ).branchOrderOfDualGraph q B.order (keep₁ z) j).val) =
        F[D₁.subscheme] (D₁.subscheme.branchOrderOfDualGraph p₁ A₁.order z j).val)
    (hcollapse₀ : ∀ z ∉ Set.range keep₀,
      gν₀ (F[boundaryOf(Φ)] (boundaryOf(Φ).branchOrderOfDualGraph q B.order z 1).val) =
      gν₀ (F[boundaryOf(Φ)] (boundaryOf(Φ).branchOrderOfDualGraph q B.order z 0).val))
    (hcollapse₁ : ∀ z ∉ Set.range keep₁,
      gν₁ (F[boundaryOf(Φ)] (boundaryOf(Φ).branchOrderOfDualGraph q B.order z 1).val) =
      gν₁ (F[boundaryOf(Φ)] (boundaryOf(Φ).branchOrderOfDualGraph q B.order z 0).val))

include hcomp hdet hnodes hν₀ hν₁ hnodes₀ hnodes₁ keep₀ keep₁ hkeep₀ hkeep₁ hcollapse₀ hcollapse₁

/-- The ratio of two marked periods in the same fan and charge coordinates is the
inverse center ratio character. The two original boundary orders agree with the positive
toric one through their respective conductor subdivisions. Centers may be repeated. -/
theorem markedBoundaryPeriod_div
    (x : ChargeKernel) :
    period₀ (Multiplicative.ofAdd x) / period₁ (Multiplicative.ofAdd x) =
      ∏ j, (c₁ j / c₀ j) ^ (x : Fin n → ℤ) j := by
  obtain ⟨L₀, hL₀, hp₀⟩ := exists_pullback_markedBoundaryPeriod hΦ b s hT₀ e₀ he₀ hD₀
    hCartier₀ hgenus₀ A₀ B hν₀ hnodes₀ keep₀ hkeep₀ hcollapse₀ x
  obtain ⟨L₁, hL₁, hp₁⟩ := exists_pullback_markedBoundaryPeriod hΦ b s hT₁ e₁ he₁ hD₁
    hCartier₁ hgenus₁ A₁ B hν₁ hnodes₁ keep₁ hkeep₁ hcollapse₁ x
  obtain ⟨L, hL, hp⟩ :=
    exists_prod_internalCenterRatio_nodalPicardCycleMulEquiv hΦ r B.endpoint_eq hcomp b
      hdet hnodes s c₀ c₁ (x : Fin n → ℤ)
  have hratio : L₀ / L₁ = L := by
    apply Subtype.ext
    simpa only [Subgroup.coe_div, hL₀, hL₁, hL] using
      pullback_toricBoundaryToBase_markedCharge_div hΦ b s hT₀ hT₁ e₀ e₁ he₀ he₁ hD₀ hD₁ x
  rw [← hp₀, ← hp₁, ← map_div, hratio, hp]

local notation "M" c:arg => internalBlowupTower b s c
local notation "T" c:arg => WithBoundary.toTower (Sigma.snd (M c))
local notation "Chars" => (Multiplicative (N →+ ℤ) →* ℂˣ)

/-- Equal marked boundary periods give a translation of the toric surface that aligns
the labeled centers and lifts to the ordered blowups. The lift permits repeated centers. -/
theorem exists_translation_lift_of_eq_markedBoundaryPeriod (hperiod : period₀ = period₁) :
    ∃ (χ : Chars) (g : (M c₀).1 ≅ (M c₁).1),
      IsLift (Φ.torusTranslation χ) (T c₀) (T c₁) g := by
  apply (exists_translation_lift_internalBlowupTower_iff b s c₀ c₁).mpr
  intro x hx
  have hr := markedBoundaryPeriod_div hΦ b s hT₀ hT₁ e₀ e₁ he₀ he₁ hD₀ hD₁
    hCartier₀ hCartier₁ hgenus₀ hgenus₁ A₀ A₁ B r hcomp hdet hnodes
    hν₀ hν₁ hnodes₀ hnodes₁ keep₀ keep₁ hkeep₀ hkeep₁ hcollapse₀ hcollapse₁ ⟨x, hx⟩
  rw [hperiod, div_self'] at hr
  have hcenters : (∏ j, c₁ j ^ x j) / (∏ j, c₀ j ^ x j) = 1 := by
    simpa only [div_zpow, Finset.prod_div_distrib] using hr.symm
  exact (div_eq_one.mp hcenters).symm

local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

local notation "presentationIso(" e "," c ")" =>
  (e ≪≫ eqToIso (Eq.symm (congrArg Sigma.fst (internalBlowupTower_eq_alongBoundary b s c))))

/-- Equal marked periods for two ordered presentations with the same fan and labeled rays
give an isomorphism of the square-zero pairs over ℂ. Its pullback agrees with the marking
on the entire Picard group, in the toric and total exceptional coordinates. -/
theorem exists_iso_of_eq_markedBoundaryPeriod
    (hperiod : period₀ = period₁)
    (hnef₀ : LineBundleClass.IsNef ℂ (X₀ ↘ S) classOf(hCartier₀))
    (hnef₁ : LineBundleClass.IsNef ℂ (X₁ ↘ S) classOf(hCartier₁))
    (hsq₀ : Chow.classIntersectionNumber ℂ X₀ classOf(hCartier₀) classOf(hCartier₀) = 0)
    (hsq₁ : Chow.classIntersectionNumber ℂ X₁ classOf(hCartier₁) classOf(hCartier₁) = 0) :
    let a₀ := presentationIso(e₀, c₀)
    let a₁ := presentationIso(e₁, c₁)
    ∃ (χ : Chars) (g : (M c₀).1 ≅ (M c₁).1) (f : X₀ ≅ X₁),
      IsLift (Φ.torusTranslation χ) (T c₀) (T c₁) g ∧
      T₀.toBase ≫ f.hom = a₀.hom ≫ g.hom ≫ a₁.inv ≫ T₁.toBase ∧
      f.hom ≫ (X₁ ↘ S) = (X₀ ↘ S) ∧ D₁.comap f.hom = D₀ ∧
      ∀ L : LineBundleClass X₁,
        (internalBlowupPicardMarking b s c₀ hΦ).symm
          (Additive.ofMul (pullback (a₀.inv ≫ T₀.toBase) (pullback f.hom L))) =
        (internalBlowupPicardMarking b s c₁ hΦ).symm
          (Additive.ofMul (pullback (a₁.inv ≫ T₁.toBase) L)) := by
  dsimp only
  obtain ⟨χ, g, hg⟩ := exists_translation_lift_of_eq_markedBoundaryPeriod hΦ b s
    hT₀ hT₁ e₀ e₁ he₀ he₁ hD₀ hD₁ hCartier₀ hCartier₁ hgenus₀ hgenus₁ A₀ A₁ B r
    hcomp hdet hnodes hν₀ hν₁ hnodes₀ hnodes₁ keep₀ keep₁ hkeep₀ hkeep₁ hcollapse₀ hcollapse₁
    hperiod
  have hnodal₀ : AtWorstNodalOfRelativeDimensionOne (D₀.subschemeι ≫ (X₀ ↘ S)) := by
    rw [← D₀.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have hnodal₁ : AtWorstNodalOfRelativeDimensionOne (D₁.subschemeι ≫ (X₁ ↘ S)) := by
    rw [← D₁.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have hconn : _root_.IsConnected (D₀.support : Set X₀) := by
    let := GeometricallyConnected.connectedSpace_of_subsingleton (f := D₀.subscheme ↘ S)
    rw [← D₀.range_subschemeι]
    exact isConnected_range D₀.subschemeι.continuous
  obtain ⟨he₀', hD₀'⟩ := transport_presentation
    (internalBlowupTower_eq_alongBoundary b s c₀) e₀ he₀ hD₀
  obtain ⟨he₁', hD₁'⟩ := transport_presentation
    (internalBlowupTower_eq_alongBoundary b s c₁) e₁ he₁ hD₁
  obtain ⟨f, hf, -⟩ := existsUnique_iso_of_translation_of_nef_square_zero_boundary b s hΦ
    hT₀ hT₁ presentationIso(e₀, c₀) presentationIso(e₁, c₁) he₀' he₁' hD₀' hD₁'
    hg hCartier₀ hCartier₁ hnodal₀ hnodal₁ hconn hnef₀ hnef₁ hsq₀ hsq₁
  exact ⟨χ, g, f, hg, hf⟩

end CenterRatio

end TauCeti.Toric.Fan

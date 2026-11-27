/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Center
public import QPainleve.Algebra.Cluster.Word.RationalMap
public import QPainleve.SignedClusterModularGroup.Realization.Period

import QPainleve.Geometry.Toric.CharacterTorus.Separation
import QPainleve.LinearAlgebra.Basis.DiagonalTorus

/-!
# Charge transport between marked toric presentations

The exponent map of a realized word is the Picard pullback on boundary orthogonals,
multiplied by the branch sign. The two toric presentations may have different
fans, charge vectors, and Picard markings. Each ordered toric period has its own
constant factor, which disappears when comparing exponents on a nonempty open.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative Quiver
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open QPainleve.Cluster QPainleve.CharacterTorus

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

variable {r n : ℕ} [NeZero n] {E₀ E₁ : SkewExchangeMatrix (Fin r)}

local notation "A" => (Fin r → ℤ)
local notation "Tcent" => Over.mk (structureMap k₀ A)

local notation "χ[" p "]" => pointsEquiv k₀ A
  (Subtype.mk (Over.Hom.left (p : Point Tcent)) (Over.w (p : Point Tcent)))

variable {C : (scheme k₀ (Fin r → ℤ)).PartialMap (scheme k₀ (Fin r → ℤ))}
  [IsDominant C.hom]
  [C.IsOver (Over.mk (structureMap k₀ (Fin r → ℤ))).hom
    (Over.mk (structureMap k₀ (Fin r → ℤ))).hom]

local notation "DomainPoint" => CenterPoint (U := Tcent) (V := Tcent) C
local notation "src[" p "]" => p ≫ PartialMap.domainSource (X := Tcent) (Y := Tcent) C
local notation "dst[" p "]" => p ≫ PartialMap.domainTarget (X := Tcent) (Y := Tcent) C

omit [IsDominant C.hom] in
omit [IsAlgClosed k₀] in
private theorem centerCharacter_domainTarget (w : Word E₀ E₁)
    (hC : C.hom = C.domain.ι ≫ (w.centerIso k₀).hom) (p : DomainPoint) :
    χ[dst[p]] =
      (χ[src[p]]).comp
        w.exponentEquiv.toAddEquiv.toAddMonoidHom.toMultiplicative := by
  apply (pointsEquiv k₀ A).symm.injective
  apply Subtype.ext
  simp only [Equiv.symm_apply_apply,
    ← Path.pointsEquiv_symm_comp_centerIso_hom]
  simp only [Over.comp_left, PartialMap.domainTarget_left, PartialMap.domainSource_left,
    hC, Category.assoc]

section PeriodFactor

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {m : ℕ} [NeZero m]
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}

local notation "Charge" => LinearMap.ker (Fan.rayChargeMap s)

variable [PrestableFamily ((Φ.toricBoundaryIdeal k₀ h₀).subscheme ↘ Spec (.of k₀))]
  {γ : Type*} {a : γ → ((Φ.toricBoundaryIdeal k₀ h₀).subscheme ↘ Spec (.of k₀)).smoothLocus}
  {T : NodalCycleNumbering a m}
  [(Φ.finiteFanScheme k₀).IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme k₀) ↘ Spec (.of k₀))]
  [LinearMap.IsPerfPair ((Chow.intersectionBilinForm k₀ (Φ.finiteFanScheme k₀)).prod
    (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))]

local notation "center" c:arg => (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))
local notation "period[" c "]" => Fan.orderedBoundaryPeriod k₀ hΦ b s T (center c)

variable (u : ZMod m ≃ Φ.Ray)
  (hvertices : ∀ j, Scheme.dualGraphVertexEquiv (Φ.toricBoundaryIdeal k₀ h₀).subscheme a
    (T.vertex j) =
    Φ.boundaryNormalizationComponentEquiv k₀ hΦ (u j))
  (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
  (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
    (Φ.toricBoundaryIdeal k₀ h₀).subschemeι
      (Scheme.dualGraphEdgeEquiv (Φ.toricBoundaryIdeal k₀ h₀).subscheme a (T.edge j)).val =
      (Φ.distinguishedSection (R := k₀) σ) (IsLocalRing.closedPoint k₀))

include hvertices hdet hnodes in
private theorem period_mul_centerCharacter (c : Multiplicative A →* k₀ˣ) (x : Charge) :
    period[c] (ofAdd x) * c (ofAdd (x : A)) = period[(1 : Multiplicative A →* k₀ˣ)] (ofAdd x) := by
  have h := Fan.orderedBoundaryPeriod_mul_torusCharacter k₀ hΦ b s T u hvertices hdet hnodes
    (center c) 1 x
  have hone : (center (1 : Multiplicative A →* k₀ˣ)) = (1 : Fin r → k₀ˣ) := by
    funext j
    simp only [MonoidHom.one_apply, Pi.one_apply]
  simpa only [torusCharacter_of_pi_single, torusCharacter_one, mul_one, hone] using h

end PeriodFactor

variable {N₀ V₀ : Type} [AddCommGroup N₀] [AddCommGroup V₀] [Module ℝ V₀]
  {i₀ : N₀ →+ V₀} {Φ₀ : Fan i₀} [hNonempty₀ : Nonempty Φ₀.cones]
  {m₀ : ℕ} [NeZero m₀] {L₀ : Type} [AddCommGroup L₀]
  {B₀ : LinearMap.BilinForm ℤ L₀}
  {b₀ : Module.Basis (Fin 2) ℤ N₀} {s₀ : Fin r → Φ₀.Ray} {hΦ₀ : Φ₀.IsRegular}

variable [PrestableFamily ((Φ₀.toricBoundaryIdeal k₀ hNonempty₀).subscheme ↘ Spec (.of k₀))]
  {γ₀ : Type*} {a₀ : γ₀ → ((Φ₀.toricBoundaryIdeal k₀ hNonempty₀).subscheme ↘ Spec
    (.of k₀)).smoothLocus}
  {T₀ : NodalCycleNumbering a₀ m₀} {origin₀ : ZMod m₀}
  {ι₀ : L₀ →ₗ[ℤ] Additive (LineBundleClass (Φ₀.finiteFanScheme k₀)) × (Fin r → ℤ)}
  [(Φ₀.finiteFanScheme k₀).IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 ((Φ₀.finiteFanScheme k₀) ↘ Spec (.of k₀))]
  [LinearMap.IsPerfPair
    ((Chow.intersectionBilinForm k₀ (Φ₀.finiteFanScheme k₀)).prod
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))]

local notation "Aux₀" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm k₀ (Φ₀.finiteFanScheme k₀))
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ A))
local notation "aux₀" => (LinearEquiv.symm (Fan.boundaryOrthogonalEquivChargeKernel k₀ hΦ₀ s₀ Aux₀))
local notation "period₀[" c "]" => Fan.orderedBoundaryPeriod k₀ hΦ₀ b₀ s₀ T₀
  (fun j ↦ c (ofAdd (Pi.single j 1)))

variable {N₁ V₁ : Type} [AddCommGroup N₁] [AddCommGroup V₁] [Module ℝ V₁]
  {i₁ : N₁ →+ V₁} {Φ₁ : Fan i₁} [hNonempty₁ : Nonempty Φ₁.cones]
  {m₁ : ℕ} [NeZero m₁] {L₁ : Type} [AddCommGroup L₁]
  {B₁ : LinearMap.BilinForm ℤ L₁}
  {b₁ : Module.Basis (Fin 2) ℤ N₁} {s₁ : Fin r → Φ₁.Ray} {hΦ₁ : Φ₁.IsRegular}

variable [PrestableFamily ((Φ₁.toricBoundaryIdeal k₀ hNonempty₁).subscheme ↘ Spec (.of k₀))]
  {γ₁ : Type*} {a₁ : γ₁ → ((Φ₁.toricBoundaryIdeal k₀ hNonempty₁).subscheme ↘ Spec
    (.of k₀)).smoothLocus}
  {T₁ : NodalCycleNumbering a₁ m₁} {origin₁ : ZMod m₁}
  {ι₁ : L₁ →ₗ[ℤ] Additive (LineBundleClass (Φ₁.finiteFanScheme k₀)) × (Fin r → ℤ)}
  [(Φ₁.finiteFanScheme k₀).IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 ((Φ₁.finiteFanScheme k₀) ↘ Spec (.of k₀))]
  [LinearMap.IsPerfPair
    ((Chow.intersectionBilinForm k₀ (Φ₁.finiteFanScheme k₀)).prod
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))]

local notation "period₁[" c "]" => Fan.orderedBoundaryPeriod k₀ hΦ₁ b₁ s₁ T₁
  (fun j ↦ c (ofAdd (Pi.single j 1)))

variable {P₀ : Point (Over.mk (structureMap k₀ (Fin r → ℤ))) →
    MarkedSurface k₀ n B₀ (Spec (CommRingCat.of (LaurentRing k₀ (Fin r))))}
  {P₁ : Point (Over.mk (structureMap k₀ (Fin r → ℤ))) →
    MarkedSurface k₀ n B₁ (Spec (CommRingCat.of (LaurentRing k₀ (Fin r))))}
  {d₀ : ZMod n → L₀} {d₁ : ZMod n → L₁}
  {hD₀ : ∀ c, D[P₀ c].IsEffectiveCartier} {hD₁ : ∀ c, D[P₁ c].IsEffectiveCartier}
  (hmark₀ : ∀ c j, (P₀ c).boundaryClass (hD₀ c) j = d₀ j)
  (hmark₁ : ∀ c j, (P₁ c).boundaryClass (hD₁ c) j = d₁ j)

local notation "Orth₁" => B₁.orthogonal (Submodule.span ℤ (Set.range d₁))
local notation "fiber₀[" c "]" =>
  ContractedToricFiber b₀ s₀ hΦ₀ T₀ origin₀ ι₀ (χ[c]) (P₀ c)
local notation "fiber₁[" c "]" =>
  ContractedToricFiber b₁ s₁ hΦ₁ T₁ origin₁ ι₁ (χ[c]) (P₁ c)

variable {w : Word E₀ E₁} (R : GeometricRealization P₀ P₁ C (w.xRationalMap k₀))
  (e₀ : B₀.orthogonal (Submodule.span ℤ (Set.range d₀)) ≃ₗ[ℤ] (Fan.rayChargeMap s₀).ker)
  (e₁ : B₁.orthogonal (Submodule.span ℤ (Set.range d₁)) ≃ₗ[ℤ] (Fan.rayChargeMap s₁).ker)
  (he₀ : ∀ x : (Fan.rayChargeMap s₀).ker, ι₀ (e₀.symm x).val =
    ((Fan.boundaryOrthogonalEquivChargeKernel k₀ hΦ₀ s₀
      ((Chow.intersectionBilinForm k₀ (Φ₀.finiteFanScheme k₀)).prod
        (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))).symm x).val)
  (he₁ : ∀ x : (Fan.rayChargeMap s₁).ker, ι₁ (e₁.symm x).val =
    ((Fan.boundaryOrthogonalEquivChargeKernel k₀ hΦ₁ s₁
      ((Chow.intersectionBilinForm k₀ (Φ₁.finiteFanScheme k₀)).prod
        (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))).symm x).val)

include he₀ he₁ in
private theorem period_eq_of_signedPicard (p : DomainPoint)
    (M : fiber₀[src[p]]) (N : fiber₁[dst[p]])
    (gM : letI := (P₀ (src[p])).prestable_boundaryImage
      ∀ v : irreducibleComponents (D[P₀ (src[p])].subscheme.singularLocus k₀).blowup,
        (D[P₀ (src[p])].subscheme.blowupComponent (K := k₀) v).toScheme.genus k₀ = 0)
    (gN : letI := (P₁ (dst[p])).prestable_boundaryImage
      ∀ v : irreducibleComponents (D[P₁ (dst[p])].subscheme.singularLocus k₀).blowup,
        (D[P₁ (dst[p])].subscheme.blowupComponent (K := k₀) v).toScheme.genus k₀ = 0)
    (x : Orth₁) :
    period₁[χ[dst[p]]] (ofAdd (e₁ x)) =
      period₀[χ[src[p]]]
        (ofAdd (e₀ (R.orientation • R.boundaryOrthogonalEquiv hmark₀ hmark₁ x))) := by
  let η := R.orientation
  -- Applying the sign to the target class cancels the orientation power in its period.
  let t := (η : ℤ) • x
  let y := e₀ (η • R.boundaryOrthogonalEquiv hmark₀ hmark₁ x)
  let : (P₁ (dst[p])).surface.IsProjectiveOver k₀ := (P₁ (dst[p])).projective
  let : SmoothOfRelativeDimension 2 ((P₁ (dst[p])).surface ↘ S) := (P₁ (dst[p])).smooth
  have ht : (P₁ (dst[p])).picardMarking t.val ∈ D[P₁ (dst[p])].boundaryOrthogonal k₀ := by
    rw [(P₁ (dst[p])).picardMarking_mem_boundaryOrthogonal_iff (hD₁ _), funext (hmark₁ _)]
    exact t.property
  have hin := he₁ (e₁ t)
  rw [LinearEquiv.symm_apply_apply] at hin
  have hout := he₀ y
  rw [LinearEquiv.symm_apply_apply] at hout
  have hout' : ι₀ (R.picard t.val) = (aux₀ y).val := by
    rw [← hout]
    simp only [t, map_smul, Units.smul_def, Submodule.coe_smul,
      coe_boundaryOrthogonalEquiv_apply]
  have h := M.orderedBoundaryPeriod_apply_of_pullback N (hD₀ _) (hD₁ _) gM gN
    (R.fiber p) t.val ht (e₁ t) y hin hout'
  have hsq : (R.orientation : ℤ) * (R.orientation : ℤ) = 1 :=
    congrArg Units.val (Int.units_mul_self R.orientation)
  simpa only [← R.orientation_def, t, η, map_smul, ofAdd_zsmul, map_zpow, ← zpow_mul,
    hsq, zpow_one] using h.symm

include he₀ he₁ in
/-- On a target boundary-orthogonal class, the exponent pullback of a realized word
is the charge coordinate of its Picard pullback multiplied by the branch sign.
The center map on the realization domain is the word's monomial center map.
The ordered toric presentations at the two ends may be chosen independently. -/
theorem exponentEquiv_eq_signed_picard_pullback
    (hC : C.hom = C.domain.ι ≫ (w.centerIso k₀).hom)
    (u₀ : ZMod m₀ ≃ Φ₀.Ray)
    (hvertices₀ : ∀ j,
      (Φ₀.toricBoundaryIdeal k₀ hNonempty₀).subscheme.dualGraphVertexEquiv a₀ (T₀.vertex j) =
        Φ₀.boundaryNormalizationComponentEquiv k₀ hΦ₀ (u₀ j))
    (hdet₀ : ∀ j, b₀.detDualEquiv (u₀ j).primitiveGenerator (u₀ (j + 1)).primitiveGenerator = 1)
    (hnodes₀ : ∀ j, ∃ σ : Φ₀.cones, (u₀ j).toCone ≤ σ ∧ (u₀ (j + 1)).toCone ≤ σ ∧
      (Φ₀.toricBoundaryIdeal k₀ hNonempty₀).subschemeι
        ((Φ₀.toricBoundaryIdeal k₀ hNonempty₀).subscheme.dualGraphEdgeEquiv a₀ (T₀.edge j)).val =
      (Φ₀.distinguishedSection (R := k₀) σ) (IsLocalRing.closedPoint k₀))
    (u₁ : ZMod m₁ ≃ Φ₁.Ray)
    (hvertices₁ : ∀ j,
      (Φ₁.toricBoundaryIdeal k₀ hNonempty₁).subscheme.dualGraphVertexEquiv a₁ (T₁.vertex j) =
        Φ₁.boundaryNormalizationComponentEquiv k₀ hΦ₁ (u₁ j))
    (hdet₁ : ∀ j, b₁.detDualEquiv (u₁ j).primitiveGenerator (u₁ (j + 1)).primitiveGenerator = 1)
    (hnodes₁ : ∀ j, ∃ σ : Φ₁.cones, (u₁ j).toCone ≤ σ ∧ (u₁ (j + 1)).toCone ≤ σ ∧
      (Φ₁.toricBoundaryIdeal k₀ hNonempty₁).subschemeι
        ((Φ₁.toricBoundaryIdeal k₀ hNonempty₁).subscheme.dualGraphEdgeEquiv a₁ (T₁.edge j)).val =
      (Φ₁.distinguishedSection (R := k₀) σ) (IsLocalRing.closedPoint k₀))
    (models₀ : ∀ p : DomainPoint, Nonempty (fiber₀[src[p]]) ∧
      (letI := (P₀ (src[p])).prestable_boundaryImage
        ∀ v : irreducibleComponents (D[P₀ (src[p])].subscheme.singularLocus k₀).blowup,
          (D[P₀ (src[p])].subscheme.blowupComponent (K := k₀) v).toScheme.genus k₀ = 0))
    (models₁ : ∀ p : DomainPoint, Nonempty (fiber₁[dst[p]]) ∧
      (letI := (P₁ (dst[p])).prestable_boundaryImage
        ∀ v : irreducibleComponents (D[P₁ (dst[p])].subscheme.singularLocus k₀).blowup,
          (D[P₁ (dst[p])].subscheme.blowupComponent (K := k₀) v).toScheme.genus k₀ = 0))
    (x : Orth₁) :
    w.exponentEquiv (e₁ x : A) =
      (e₀ (R.orientation • R.boundaryOrthogonalEquiv hmark₀ hmark₁ x) : A) := by
  let y := e₀ (R.orientation • R.boundaryOrthogonalEquiv hmark₀ hmark₁ x)
  have hU : (C.domain : Set (scheme k₀ A)).Nonempty := C.dense_domain.nonempty
  apply exponent_eq_of_proportional_on_open hU
    (a := period₁[(1 : Multiplicative A →* k₀ˣ)] (ofAdd (e₁ x)) /
      period₀[(1 : Multiplicative A →* k₀ˣ)] (ofAdd y))
  intro c hc
  let t := (pointsEquiv k₀ A).symm c
  let p₀ : Point Tcent := Over.homMk t.val t.property
  obtain ⟨p, hp₀⟩ := (C.exists_section_comp_domainSource_eq_iff
    (Y := Tcent) p₀ (default : S)).mpr hc
  have hp : χ[src[p]] = c := by
    rw [hp₀]
    exact (pointsEquiv k₀ A).apply_symm_apply c
  obtain ⟨⟨M⟩, gM⟩ := models₀ p
  obtain ⟨⟨N⟩, gN⟩ := models₁ p
  have hz : χ[dst[p]] (ofAdd (e₁ x : A)) = c (ofAdd (w.exponentEquiv (e₁ x : A))) := by
    simp only [centerCharacter_domainTarget w hC, MonoidHom.comp_apply, hp,
      AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd,
      AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply]
  have hperiod := R.period_eq_of_signedPicard hmark₀ hmark₁ e₀ e₁ he₀ he₁ p M N gM gN x
  rw [hp] at hperiod
  have hs := period_mul_centerCharacter u₀ hvertices₀ hdet₀ hnodes₀ c y
  have ht := period_mul_centerCharacter u₁ hvertices₁ hdet₁ hnodes₁ χ[dst[p]] (e₁ x)
  rw [hperiod, hz] at ht
  -- The source period cancels from the ratio of the two reference-period values.
  rw [← ht, ← hs, mul_div_mul_left_eq_div, div_mul_cancel]

end QPainleve.SignedClusterModularGroup.GeometricRealization

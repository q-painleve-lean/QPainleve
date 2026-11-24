/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Action
public import QPainleve.Algebra.Cluster.Word.RationalMap
public import QPainleve.SignedClusterModularGroup.Boundary.Restriction
public import QPainleve.SignedClusterModularGroup.Realization.Period

import QPainleve.Geometry.Toric.CharacterTorus.Separation

/-!
# Picard and Casimir actions of a realized loop

The monomial center map and the signed Picard pullback give the same substitution
on charge exponents. The variation of the boundary period leaves a constant
factor that cancels in the comparison of exponents on a nonempty center open.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup MulOpposite Multiplicative Quiver
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open QPainleve.Cluster QPainleve.CharacterTorus QPainleve.SignedBoundaryIsometryGroup

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L : Type} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L} {E : SkewExchangeMatrix (Fin r)}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}

local notation "A" => (Fin r → ℤ)
local notation "Xtor" => Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))
local notation "Tcent" => Over.mk (structureMap ℂ A)
local notation "ChargeKernel" => LinearMap.ker (Fan.rayChargeMap s)
local notation "Ex" => LinearMap.ker (Matrix.mulVecLin (SkewExchangeMatrix.matrix E))
local notation "Qform" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm ℂ Φ.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ A))

local notation "χ[" p "]" => pointsEquiv ℂ A
  (Subtype.mk (Over.Hom.left (p : Point Tcent)) (Over.w (p : Point Tcent)))

variable {C : (scheme ℂ (Fin r → ℤ)).PartialMap (scheme ℂ (Fin r → ℤ))}
  [IsDominant C.hom]
  [C.IsOver (Over.mk (structureMap ℂ (Fin r → ℤ))).hom
    (Over.mk (structureMap ℂ (Fin r → ℤ))).hom]

local notation "DomainPoint" => CenterPoint (U := Tcent) (V := Tcent) C
local notation "src[" p "]" => p ≫ PartialMap.domainSource (X := Tcent) (Y := Tcent) C
local notation "dst[" p "]" => p ≫ PartialMap.domainTarget (X := Tcent) (Y := Tcent) C

omit [IsDominant C.hom]
  [C.IsOver (Over.mk (structureMap ℂ (Fin r → ℤ))).hom
    (Over.mk (structureMap ℂ (Fin r → ℤ))).hom] in
private theorem exists_centerPoint (c : Multiplicative A →* ℂˣ)
    (hc : ((pointsEquiv ℂ A).symm c).val default ∈ C.domain) :
    ∃ p : DomainPoint, χ[src[p]] = c := by
  let t := (pointsEquiv ℂ A).symm c
  have ht : Set.range t.val ⊆ Set.range C.domain.ι := by
    rw [Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x default]
  let f := IsOpenImmersion.lift C.domain.ι t.val ht
  have hf : f ≫ C.domain.ι = t.val := IsOpenImmersion.lift_fac _ _ _
  let p : DomainPoint := Over.homMk f (by
    -- The structure map of the slice domain is the open inclusion over the base.
    change f ≫ (C.domain.ι ≫ structureMap ℂ A) = 𝟙 S
    rw [← Category.assoc, hf]
    exact t.property)
  refine ⟨p, (pointsEquiv ℂ A).eq_symm_apply.mp (Subtype.ext ?_)⟩
  simpa only [p, Over.comp_left, PartialMap.domainSource_left, Over.homMk_left] using hf

omit [IsDominant C.hom] in
private theorem centerCharacter_domainTarget (w : Word E E)
    (hC : C.hom = C.domain.ι ≫ (w.centerIso ℂ).hom) (p : DomainPoint) :
    χ[dst[p]] =
      (χ[src[p]]).comp
        w.exponentEquiv.toAddEquiv.toAddMonoidHom.toMultiplicative := by
  apply (pointsEquiv ℂ A).symm.injective
  apply Subtype.ext
  simp only [Equiv.symm_apply_apply,
    ← Path.pointsEquiv_symm_comp_centerIso_hom]
  simp only [Over.comp_left, PartialMap.domainTarget_left, PartialMap.domainSource_left,
    hC, Category.assoc]

variable [PrestableFamily ((Φ.boundaryIdeal h₀).subscheme ↘ S)]
  {γ : Type*} {a : γ → ((Φ.boundaryIdeal h₀).subscheme ↘ S).smoothLocus}
  {T : NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ)}
  [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]
  [LinearMap.IsPerfPair
    ((Chow.intersectionBilinForm ℂ Φ.algebraicRealization).prod
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))]

local notation "aux" => (LinearEquiv.symm (Fan.boundaryOrthogonalEquivChargeKernel hΦ s Qform))
local notation "center" c:arg => (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))
local notation "period[" c "]" => Fan.orderedBoundaryPeriod hΦ b s T (center c)

variable (u : ZMod m ≃ Φ.Ray)
  (hvertices : ∀ j, Scheme.dualGraphVertexEquiv (Φ.boundaryIdeal h₀).subscheme a (T.vertex j) =
    Φ.boundaryNormalizationComponentEquiv hΦ (u j))
  (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
  (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
    (Φ.boundaryIdeal h₀).subschemeι
      (Scheme.dualGraphEdgeEquiv (Φ.boundaryIdeal h₀).subscheme a (T.edge j)).val =
      Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))

include hvertices hdet hnodes in
private theorem period_mul_centerCharacter (c : Multiplicative A →* ℂˣ) (x : ChargeKernel) :
    period[c] (ofAdd x) * c (ofAdd (x : A)) = period[(1 : Multiplicative A →* ℂˣ)] (ofAdd x) := by
  have h := Fan.orderedBoundaryPeriod_mul_torusCharacter hΦ b s T u hvertices hdet hnodes
    (center c) 1 x
  have hc : torusCharacter (center c) (x : A) = c (ofAdd (x : A)) := by
    conv_rhs => rw [pi_eq_sum_univ' (x : A), ofAdd_sum, map_prod]
    simp only [torusCharacter_def, ofAdd_zsmul, map_zpow]
  have hone : (center (1 : Multiplicative A →* ℂˣ)) = (1 : Fin r → ℂˣ) := by
    funext j
    simp only [MonoidHom.one_apply, Pi.one_apply]
  simpa only [hc, torusCharacter_one, mul_one, hone] using h

variable {P : Point (Over.mk (structureMap ℂ (Fin r → ℤ))) →
  MarkedSurface ℂ n B (Spec (CommRingCat.of (LaurentRing ℂ (Fin r))))}
  (D : ZMod n → L) (hD : ∀ c, D[P c].IsEffectiveCartier)
  (hmark : ∀ c j, (P c).boundaryClass (hD c) j = D j)

local notation "Orth" => LinearMap.BilinForm.orthogonal B (Submodule.span ℤ (Set.range D))
local notation "ρ" => signedOrthogonalRestriction B D

private theorem period_eq_of_signedPicard {F : Xtor ⤏ Xtor} [F.IsDominant]
    (R : GeometricRealization P P C F) (p : DomainPoint)
    (e : Orth ≃ₗ[ℤ] ChargeKernel) (he : ∀ x : ChargeKernel, ι (e.symm x).val = (aux x).val)
    (M : ContractedToricFiber (h₀ := h₀) b s hΦ T origin ι (χ[src[p]]) (P (src[p])))
    (N : ContractedToricFiber (h₀ := h₀) b s hΦ T origin ι (χ[dst[p]]) (P (dst[p])))
    (gM : letI := (P (src[p])).prestable_boundaryImage
      ∀ v : irreducibleComponents (D[P (src[p])].subscheme.singularLocus ℂ).blowup,
        (D[P (src[p])].subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
    (gN : letI := (P (dst[p])).prestable_boundaryImage
      ∀ v : irreducibleComponents (D[P (dst[p])].subscheme.singularLocus ℂ).blowup,
        (D[P (dst[p])].subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
    (x : ChargeKernel) :
    period[χ[dst[p]]] (ofAdd x) =
      period[χ[src[p]]]
        (ofAdd (e ((ρ (R.toSignedBoundaryIsometry D hD hmark)).val (e.symm x)))) := by
  let c₀ := src[p]
  let c₁ := dst[p]
  let η := R.orientation
  let v := (ρ (R.toSignedBoundaryIsometry D hD hmark)).val
  let y := e (v (e.symm x))
  have hι := he y
  rw [LinearEquiv.symm_apply_apply] at hι
  have hv : ((v (e.symm x) : Orth) : L) = η • R.picard (e.symm x).val := by
    rw [coe_signedOrthogonalRestriction_apply, toIsometry_apply, coe_toSignedBoundaryIsometry,
      SignedBoundaryIsometryGroup.sign_apply, coe_toSignedBoundaryIsometry,
      LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv_symm]
  have hper := M.orderedBoundaryPeriod_apply_of_pullback N (hD c₀) (hD c₁)
    gM gN (R.fiber p)
  have hη : cycleOrientationSign R.boundaryAction = η := R.orientation_def.symm
  -- The sign in the pullback of periods cancels the sign on the target exponent.
  let x' := (η : ℤ) • x
  let t := e.symm x'
  let : (P c₁).surface.IsProjectiveOver ℂ := (P c₁).projective
  let : SmoothOfRelativeDimension 2 ((P c₁).surface ↘ S) := (P c₁).smooth
  have hx : (P c₁).picardMarking t.val ∈ D[P c₁].boundaryOrthogonal ℂ := by
    apply ((P c₁).picardMarking_mem_boundaryOrthogonal_iff (hD c₁) _).mpr
    rw [funext (hmark c₁)]
    exact t.property
  have hι' : ι (R.picard t.val) = (aux y).val := by
    rw [← hι, hv]
    simp only [t, x', map_smul, Submodule.coe_smul, Units.smul_def]
  have h' := hper t.val hx x' y (he x') hι'
  have hsq : (η : ℤ) * (η : ℤ) = 1 := congrArg Units.val (Int.units_mul_self η)
  have hpow : period[χ[c₁]] (ofAdd x') = period[χ[c₁]] (ofAdd x) ^ (η : ℤ) := by
    simp only [x', ofAdd_zsmul, map_zpow]
  rw [hη, hpow, ← zpow_mul, hsq, zpow_one] at h'
  exact h'.symm

include hvertices hdet hnodes in
/-- In the charge coordinates of a fixed ordered presentation, a realized signed
loop acts on the charge kernel by the restriction of its Picard pullback times
its branch sign. The center map is the loop's monomial center map restricted to
the realization domain. The coordinate identification is characterized by the
toric and total exceptional classes of each charge relation. -/
theorem chargeKernelAction_eq_signedOrthogonalRestriction
    (w : Word E E) (R : GeometricRealization P P C (w.xRationalMap ℂ))
    (hC : C.hom = C.domain.ι ≫ (w.centerIso ℂ).hom)
    (Q : ChargeSeed E N) (hcharge : Q.charge = Fan.rayChargeMap s)
    (hker : Ex = Q.charge.ker) (e : Orth ≃ₗ[ℤ] ChargeKernel)
    (he : ∀ x : ChargeKernel, ι (e.symm x).val = (aux x).val)
    {U : Set (Point Tcent)}
    (hends : ∀ c : CenterPoint (U := Tcent) (V := Tcent) C, src[c] ∈ U ∧ dst[c] ∈ U)
    (hgenus : ∀ t ∈ U,
      letI := (P t).prestable_boundaryImage
      ∀ v : irreducibleComponents (D[P t].subscheme.singularLocus ℂ).blowup,
        (D[P t].subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
    (hmodel : ∀ t ∈ U,
      Nonempty (ContractedToricFiber (h₀ := h₀) b s hΦ T origin ι (χ[t]) (P t))) :
    LinearEquiv.autCongr
      (LinearEquiv.ofEq Q.charge.ker ChargeKernel (congrArg LinearMap.ker hcharge))
      (chargeKernelAction ℂ Q hker (op (signedClusterModularGroupMap ℂ E (End.of w)))) =
      LinearEquiv.autCongr e (ρ (R.toSignedBoundaryIsometry D hD hmark)).val := by
  let g := R.toSignedBoundaryIsometry D hD hmark
  let v := (ρ g).val
  apply LinearEquiv.ext
  intro x
  let y := e (v (e.symm x))
  let j := LinearEquiv.ofEq Q.charge.ker ChargeKernel (congrArg LinearMap.ker hcharge)
  let z := j (chargeKernelAction ℂ Q hker (op (signedClusterModularGroupMap ℂ E (End.of w)))
    (j.symm x))
  suffices (z : A) = (y : A) by
    apply Subtype.ext
    simpa only [y, z, j, v, g, LinearEquiv.autCongr_apply_apply]
      using this
  have hU : (C.domain : Set (scheme ℂ A)).Nonempty :=
    C.dense_domain.nonempty
  apply exponent_eq_of_proportional_on_open hU
    (a := period[(1 : Multiplicative A →* ℂˣ)] (ofAdd x) /
      period[(1 : Multiplicative A →* ℂˣ)] (ofAdd y))
  intro c hc
  obtain ⟨p, hp⟩ := exists_centerPoint (C := C) c hc
  let c₀ := src[p]
  let c₁ := dst[p]
  obtain ⟨h₀, h₁⟩ := hends p
  obtain ⟨M⟩ := hmodel c₀ h₀
  obtain ⟨N⟩ := hmodel c₁ h₁
  have hz : χ[c₁] (ofAdd (x : A)) = c (ofAdd (z : A)) := by
    rw [centerCharacter_domainTarget w hC, MonoidHom.comp_apply, hp]
    simp only [z, j, AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd,
      AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv,
      chargeKernelAction_op_loop, LinearEquiv.trans_apply, Path.coe_chargeKernelEquiv_apply,
      LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]
    rfl
  have hperiod := period_eq_of_signedPicard D hD hmark R p e he M N
    (hgenus c₀ h₀) (hgenus c₁ h₁) x
  rw [hp] at hperiod
  have hs := period_mul_centerCharacter u hvertices hdet hnodes c y
  have ht := period_mul_centerCharacter u hvertices hdet hnodes (χ[c₁]) x
  rw [hperiod, hz] at ht
  rw [← ht, ← hs, mul_div_mul_left_eq_div, div_mul_cancel]

end QPainleve.SignedClusterModularGroup.GeometricRealization

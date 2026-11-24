/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Contracted.Basic
public import QPainleve.SignedClusterModularGroup.Realization.Agreement

import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.Geometry.Toric.Fan.Mutation.CycleAction

/-!
# Fixed-center realizations of a mutation

The elementary transformation of Gross, Hacking and Keel
([*Birational geometry of cluster algebras*, §3.1][GHK]) gives a realization of
independent X mutation between marked contractions. The rotation on the contracted
cycles is determined by the sheared ray above component zero. Its positive orientation
comes from the ordered branches, including for cycles of length one or two.

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative PointedCone
open Module (Basis)
open QPainleve.BlowupTower QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan
open Scheme.IdealSheafData
open LineBundleClass (IsNef pullback)

namespace QPainleve.SignedClusterModularGroup

open MarkedSurface (surfaceIso boundaryIso)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Xtor[" r "]" => Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))

section Pair

variable {r m : ℕ} [NeZero m] {L₀ L₁ : Type} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  (M : MarkedSurface ℂ m B₀ Xtor[r]) (N : MarkedSurface ℂ m B₁ Xtor[r])

private theorem exists_pairIso_of_boundaryIdeal (g : M.surface ≅ N.surface)
    (hover : g.hom ≫ (N.surface ↘ S) = M.surface ↘ S)
    (hker : N.pair.hom.left.ker.comap g.hom = M.pair.hom.left.ker) :
    ∃ e : M.pair ≅ N.pair, (surfaceIso e).hom = g.hom := by
  have : IsClosedImmersion M.pair.hom.left := M.closedImmersion
  have : IsClosedImmersion N.pair.hom.left := N.closedImmersion
  obtain ⟨d, hd⟩ := N.pair.hom.left.ker.exists_iso_of_comap_eq_ker g M.pair.hom.left hker
  let d' := d ≪≫ (asIso N.pair.hom.left.toImage).symm
  have hi : N.pair.hom.left.toImage ≫ N.pair.hom.left.ker.subschemeι = N.pair.hom.left :=
    N.pair.hom.left.toImage_imageι
  have hd' : d'.hom ≫ N.pair.hom.left = M.pair.hom.left ≫ g.hom := by
    simpa only [d', Iso.trans_hom, Iso.symm_hom, ← hi, Category.assoc, asIso_inv,
      IsIso.inv_hom_id_assoc] using hd
  have hdOver : d'.hom ≫ N.pair.left.hom = M.pair.left.hom := by
    have hover' : g.hom ≫ N.pair.right.hom = M.pair.right.hom := hover
    rw [← Over.w N.pair.hom, ← Category.assoc, hd', Category.assoc, hover', Over.w M.pair.hom]
  let e := Arrow.isoMk (Over.isoMk d' hdOver) (Over.isoMk g hover) (by ext1; exact hd')
  exact ⟨e, rfl⟩

private theorem boundaryIdeal_nodal :
    AtWorstNodalOfRelativeDimensionOne
      (M.pair.hom.left.ker.subschemeι ≫ (M.surface ↘ S)) := by
  have : IsClosedImmersion M.pair.hom.left := M.closedImmersion
  have : PrestableFamily M.pair.left.hom := M.prestable
  have hi : M.pair.hom.left.toImage ≫ M.pair.hom.left.ker.subschemeι = M.pair.hom.left :=
    M.pair.hom.left.toImage_imageι
  have hOver : M.pair.hom.left ≫ (M.surface ↘ S) = M.pair.left.hom := Over.w M.pair.hom
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @AtWorstNodalOfRelativeDimensionOne)
    M.pair.hom.left.toImage, ← Category.assoc, hi, hOver]
  exact PrestableFamily.atWorstNodalOfRelativeDimensionOne

end Pair

section Mutation

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) {n : ℕ}
  (s : Fin (n + 1) → Φ.Ray) (k : Fin (n + 1))
  (hOpp : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones)
  (hΦ : Φ.IsRegular)

local notation "ρ" => s k
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "shear" => Φ.mutationFanRayEquiv b hv hp hOpp
local notation "t" => Φ.mutationFanCenterRays b s k hOpp
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hOpp) hΦ
variable [hΦ₀ : Nonempty Φ.cones]
  [hΨ₀ : Nonempty (Φ.mutationFan b (s k).primitiveGenerator_ne_zero
    (s k).hull_primitiveGenerator_mem hOpp).cones]
local notation "ε" => chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s)

variable (χ : Multiplicative (Fin (n + 1) → ℤ) →* ℂˣ)

local notation "center" a:arg => (fun j : Fin (n + 1) ↦ a (ofAdd (Pi.single j 1)))
local notation "χ′" => MonoidHom.comp χ (AddMonoidHom.toMultiplicative
  (AddEquiv.toAddMonoidHom (LinearEquiv.toAddEquiv (chargeMutationEquiv ε k))))
local notation "d" => center χ
local notation "c" => (d) k
local notation "d′" => center χ′
local notation "A" => internalBlowupTower (h₀ := hΦ₀) b s (d)
local notation "B" => internalBlowupTower (h₀ := hΨ₀) b (t) (d′)
local notation "ιA" => WithBoundary.boundaryι (Sigma.snd A)
local notation "ιB" => WithBoundary.boundaryι (Sigma.snd B)
local notation "u" => Ray.mutationBoundaryIso b ρ hOpp c hΦ
local notation "classOf(" h ")" =>
  (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {m l : ℕ} [NeZero m] [NeZero l]
  {L₀ L₁ : Type} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  {M : MarkedSurface ℂ m B₀ Xtor[n + 1]} {N' : MarkedSurface ℂ m B₁ Xtor[n + 1]}
  [PrestableFamily ((Φ.boundaryIdeal hΦ₀).subscheme ↘ S)]
  [PrestableFamily (((Φ.mutationFan b (s k).primitiveGenerator_ne_zero
    (s k).hull_primitiveGenerator_mem hOpp).boundaryIdeal hΨ₀).subscheme ↘ S)]
  {γ₀ γ₁ : Type*} {a₀ : γ₀ → ((Φ.boundaryIdeal hΦ₀).subscheme ↘ S).smoothLocus}
  {a₁ : γ₁ → (((Φ.mutationFan b (s k).primitiveGenerator_ne_zero
    (s k).hull_primitiveGenerator_mem hOpp).boundaryIdeal hΨ₀).subscheme ↘ S).smoothLocus}
  {T₀ : Scheme.NodalCycleNumbering a₀ l} {T₁ : Scheme.NodalCycleNumbering a₁ l}
  {o₀ o₁ : ZMod l}
  {J₀ : L₀ →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin (n + 1) → ℤ)}
  {J₁ : L₁ →ₗ[ℤ] Additive (LineBundleClass
    (Φ.mutationFan b (s k).primitiveGenerator_ne_zero
      (s k).hull_primitiveGenerator_mem hOpp).algebraicRealization) × (Fin (n + 1) → ℤ)}
  (p : ContractedToricFiber (h₀ := hΦ₀) b s hΦ T₀ o₀ J₀ χ M)
  (q : ContractedToricFiber (h₀ := hΨ₀) b
    (Φ.mutationFanCenterRays b s k hOpp)
    ((Φ.isRegular_mutationFan_iff b (s k).primitiveGenerator_ne_zero
      (s k).hull_primitiveGenerator_mem hOpp).mpr hΦ) T₁ o₁ J₁
    (χ.comp (chargeMutationEquiv (chargeExchangeMatrix b.detDualEquiv.toLinearMap
      (rayChargeMap s)) k).toAddEquiv.toAddMonoidHom.toMultiplicative) N')

variable {r₀ : ZMod l ≃ Φ.Ray}
  {r₁ : ZMod l ≃ (Φ.mutationFan b (s k).primitiveGenerator_ne_zero
    (s k).hull_primitiveGenerator_mem hOpp).Ray}
  (hr₀ : ∀ j, T₀.component j = Φ.boundaryNormalizationComponentEquiv hΦ (r₀ j))
  (hr₁ : ∀ j, T₁.component j = (Φ.mutationFan b (s k).primitiveGenerator_ne_zero
    (s k).hull_primitiveGenerator_mem hOpp).boundaryNormalizationComponentEquiv
      ((Φ.isRegular_mutationFan_iff b (s k).primitiveGenerator_ne_zero
        (s k).hull_primitiveGenerator_mem hOpp).mpr hΦ) (r₁ j))
  (hAdjacent : b.detDualEquiv (r₀ 0).primitiveGenerator (r₀ 1).primitiveGenerator = 1 ∧
    ∃ σ : Φ.cones, (r₀ 0).toCone ≤ σ ∧ (r₀ 1).toCone ≤ σ)
  (hPositive : ∀ j, b.detDualEquiv (r₁ j).primitiveGenerator (r₁ (j + 1)).primitiveGenerator = 1)

include hr₀ hr₁ hAdjacent hPositive
private theorem mutation_boundaryAction (e : (A).1 ≅ (B).1) (g : M.pair ≅ N'.pair)
    (he : (ιA) ≫ e.hom = (u).hom ≫ (ιB))
    (hg : p.projection ≫ (surfaceIso g).hom = e.hom ≫ q.projection) :
    letI : PrestableFamily (M.boundary ↘ S) := M.prestable
    letI : PrestableFamily (N'.boundary ↘ S) := N'.prestable
    ∃ j : ZMod m, (boundaryIso g).boundaryCycleAction M.cycle N'.cycle = DihedralGroup.r j ∧
      q.boundaryMap (T₁.componentGenericPoint (r₁.symm (shear (r₀ o₀)))) =
        N'.cycle.componentGenericPoint j := by
  let : PrestableFamily (M.boundary ↘ S) := M.prestable
  let : PrestableFamily (N'.boundary ↘ S) := N'.prestable
  have : IsClosedImmersion N'.pair.hom.left := N'.closedImmersion
  have hsquare : CommSq (u).hom p.boundaryMap q.boundaryMap (boundaryIso g).hom := by
    constructor
    apply (cancel_mono N'.pair.hom.left).mp
    simp only [Category.assoc, q.boundary_comp, MarkedSurface.boundaryIso_hom_comp,
      reassoc_of% p.boundary_comp, ← Category.assoc (u).hom, ← he, Category.assoc, hg]
  have hsign := (ρ).cycleOrientationSign_of_mutationBoundaryIso_descends b hOpp c hΦ
    T₀ T₁ hr₀ hr₁ hAdjacent hPositive M.cycle N'.cycle (boundaryIso g)
    p.orientedSubdivision q.orientedSubdivision hsquare
  refine ⟨_, (eq_r_iff_cycleVertexPerm_zero_eq hsign).mpr rfl, ?_⟩
  have hray := (ρ).mutationBoundaryIso_cycleVertexPerm b hOpp c hΦ T₀ T₁ hr₀ hr₁ o₀
  have hlabel := congrArg r₁.symm hray
  rw [Equiv.symm_apply_apply] at hlabel
  rw [← (boundaryIso g).apply_componentGenericPoint M.cycle N'.cycle, ← p.component_zero,
    ← Scheme.Hom.comp_apply, ← hsquare.w, Scheme.Hom.comp_apply,
    (u).apply_componentGenericPoint T₀ T₁, hlabel]

omit hr₀ hr₁ hAdjacent hPositive
private theorem mutation_picard_eq (I : B₁.IsometryEquiv B₀)
    (hPull : Function.Injective (pullback p.projection))
    (hI : ∀ x, J₀ (I x) = mutationPicardEquiv b s k hOpp hΦ (J₁ x))
    (g : M.pair ≅ N'.pair)
    (hmark : ∀ L : LineBundleClass N'.surface,
      (internalBlowupPicardMarking (h₀ := hΦ₀) b s (d) hΦ).symm
          (Additive.ofMul (pullback p.projection (pullback (surfaceIso g).hom L))) =
        mutationPicardEquiv b s k hOpp hΦ
          ((internalBlowupPicardMarking (h₀ := hΨ₀) b (t) (d′) hΨ).symm
            (Additive.ofMul (pullback q.projection L))))
    (x : L₁) :
    M.picardMarking (I x) =
      Additive.ofMul (pullback (surfaceIso g).hom (N'.picardMarking x).toMul) := by
  apply Additive.toMul.injective
  apply hPull
  apply Additive.ofMul.injective
  apply (internalBlowupPicardMarking b s (d) hΦ).symm.injective
  rw [p.marked_pullback, toMul_ofMul, hmark, q.marked_pullback]
  exact hI x

include hr₀ hr₁ hAdjacent hPositive
/-- At a noncolliding pivot, the elementary transformation of marked nef square-zero
pairs realizes the independent X mutation. The marked Picard isometry is specified by
its integral formula in the two toric markings. The branch action is rotation by the
label of the component corresponding to the sheared source ray above component zero.
The two projection squares describe the upper isomorphism giving the realization. -/
theorem FiberRealization.exists_mutate
    (I : B₁.IsometryEquiv B₀)
    (hI : ∀ x, J₀ (I x) = mutationPicardEquiv b s k hOpp hΦ (J₁ x))
    (hsame : ∀ j, j ≠ k → (s j).primitiveGenerator = Ray.primitiveGenerator ρ → (d) j ≠ c)
    (hopp : ∀ j, j ≠ k → (s j).primitiveGenerator = -Ray.primitiveGenerator ρ → (d) j * c ≠ 1)
    {Y Y' : Scheme} {a a' : ℕ}
    {P : BlowupTower M.surface a Y} {Q : BlowupTower N'.surface a' Y'}
    (hP : IsNodalBoundaryTower M.pair.hom.left.ker (M.surface ↘ S) (𝟙 M.surface) P)
    (hQ : IsNodalBoundaryTower N'.pair.hom.left.ker (N'.surface ↘ S) (𝟙 N'.surface) Q)
    (e₀ : Y ≅ (A).1) (e₁ : Y' ≅ (B).1)
    (hp₀ : p.projection = e₀.inv ≫ P.toBase) (hq₁ : q.projection = e₁.inv ≫ Q.toBase)
    (hD : M.pair.hom.left.ker.IsEffectiveCartier) (hD' : N'.pair.hom.left.ker.IsEffectiveCartier)
    (hnef : IsNef ℂ (M.surface ↘ S) classOf(hD))
    (hnef' : IsNef ℂ (N'.surface ↘ S) classOf(hD'))
    (hsq : Chow.classIntersectionNumber ℂ M.surface classOf(hD) classOf(hD) = 0)
    (hsq' : Chow.classIntersectionNumber ℂ N'.surface classOf(hD') classOf(hD') = 0)
    (E : SkewExchangeMatrix (Fin (n + 1))) (hE : ∀ j, E.matrix j k = ε j k) :
    let F := ((Generator.mutate k).toStep E).toPath.xRationalMap ℂ
    letI : PrestableFamily (N'.boundary ↘ S) := N'.prestable
    ∃ (j : ZMod m) (R : FiberRealization M N' F I (DihedralGroup.r j)) (e : (A).1 ≅ (B).1),
      (ιA) ≫ e.hom = (u).hom ≫ (ιB) ∧
      p.projection ≫ (surfaceIso R.iso).hom = e.hom ≫ q.projection ∧
      q.boundaryMap (T₁.componentGenericPoint (r₁.symm (shear (r₀ o₀)))) =
        N'.cycle.componentGenericPoint j := by
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : N'.surface.IsProjectiveOver ℂ := N'.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : SmoothOfRelativeDimension 2 (N'.surface ↘ S) := N'.smooth
  have : PrestableFamily M.pair.left.hom := M.prestable
  have : IsClosedImmersion M.pair.hom.left := M.closedImmersion
  let : ConnectedSpace M.boundary :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := M.pair.left.hom)
  have hconn : _root_.IsConnected (M.pair.hom.left.ker.support : Set M.surface) := by
    rw [M.pair.hom.left.support_ker, M.pair.hom.left.isClosedEmbedding.isClosed_range.closure_eq]
    exact isConnected_range M.pair.hom.left.continuous
  have hpOver := congrArg (e₀.hom ≫ ·) p.projection_over.symm
  have hqOver := congrArg (e₁.hom ≫ ·) q.projection_over.symm
  simp only [hp₀, hq₁, Category.assoc, Iso.hom_inv_id_assoc] at hpOver hqOver
  obtain ⟨e, g, he, hg, hover, hker, hmark, heval⟩ :=
    exists_iso_ordered_nodal_mutation b s k χ hOpp hΦ hsame hopp hP hQ e₀ e₁ hpOver hqOver
      (by simpa only [← support_comap, ← comap_comp, hp₀, Iso.hom_inv_id_assoc] using
        congrArg (·.preimage e₀.hom.continuous) p.support_comap.symm)
      (by simpa only [← support_comap, ← comap_comp, hq₁, Iso.hom_inv_id_assoc] using
        congrArg (·.preimage e₁.hom.continuous) q.support_comap.symm)
      hD hD' (boundaryIdeal_nodal M) (boundaryIdeal_nodal N') hconn hnef hnef' hsq hsq' E hE
  obtain ⟨f, hf⟩ := exists_pairIso_of_boundaryIdeal M N' g hover hker
  have hcomm : p.projection ≫ (surfaceIso f).hom = e.hom ≫ q.projection := by
    simpa only [hp₀, hq₁, hf] using hg
  obtain ⟨j, hAction, hj⟩ :=
    mutation_boundaryAction b s k hOpp hΦ χ p q hr₀ hr₁ hAdjacent hPositive e f he hcomm
  refine ⟨j, ⟨f, ?_, hAction, ?_⟩, e, he, hcomm, hj⟩
  · have : IsNoetherian M.surface := isNoetherian_of_finiteType (M.surface ↘ S)
    have hPull : Function.Injective (pullback p.projection) := by
      intro x y hxy
      apply hP.isClosedPointTower.injective_pullback_toBase (M.surface ↘ S)
      apply (LineBundleClass.pullbackEquiv e₀.symm).injective
      simpa only [hp₀, LineBundleClass.pullback_comp, LineBundleClass.pullbackEquiv_apply,
        Iso.symm_hom] using hxy
    exact mutation_picard_eq b s k hOpp hΦ χ p q I hPull hI f
      (by simpa only [hp₀, hq₁, hf] using hmark)
  · rw [p.evaluation_eq, q.evaluation_eq]
    simpa only [hp₀, hq₁, hf] using heval

end Mutation

end QPainleve.SignedClusterModularGroup

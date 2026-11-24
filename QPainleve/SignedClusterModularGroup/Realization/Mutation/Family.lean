/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.MutationDomain
public import QPainleve.SignedClusterModularGroup.Realization.Boundary
public import QPainleve.SignedClusterModularGroup.Realization.Mutation.Basic

/-!
# Mutation realizations over the center open

The fixed-center elementary transformations of Gross, Hacking and Keel, as
formalized in `FiberRealization.exists_mutate`, give a geometric realization
over the noncollision open of the typed mutation step. In fixed markings the
image of component zero has a constant label: its boundary class pulls back
to the class of component zero. The fiber calculation retains the order of the
branches and makes the resulting dihedral action a rotation even for a
one- or two-component boundary.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative PointedCone
open Module (Basis)
open QPainleve.BlowupTower QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan
open Scheme.IdealSheafData
open LineBundleClass (IsNef)

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) {n : ℕ}
  (s : Fin (n + 1) → Φ.Ray) (k : Fin (n + 1))
  (hOpp : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones)
  (hΦ : Φ.IsRegular)

local notation "ρ" => s k
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "MutFan[" b "," s "," k "," h "]" =>
  Fan.mutationFan _ b (Ray.primitiveGenerator_ne_zero (s k))
    (Ray.hull_primitiveGenerator_mem (s k)) h
local notation "Ψ" => MutFan[b,s,k,hOpp]
local notation "t" => Φ.mutationFanCenterRays b s k hOpp
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hOpp) hΦ

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "A" => (Fin (n + 1) → ℤ)
local notation "Centers" => Over.mk (structureMap ℂ A)
local notation "XTor" => scheme ℂ (Fin (n + 1) →₀ ℤ)
local notation "ε" => chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s)
local notation "χ(" c ")" => pointsEquiv ℂ A
  (Subtype.mk (CommaMorphism.left (c : Point Centers)) (Over.w (c : Point Centers)))
local notation "χ′(" c ")" => MonoidHom.comp χ(c) (AddMonoidHom.toMultiplicative
  (AddEquiv.toAddMonoidHom (LinearEquiv.toAddEquiv (chargeMutationEquiv ε k))))
local notation "center(" χ ")" => fun j : Fin (n + 1) ↦ (χ) (ofAdd (Pi.single j 1))
local notation "classOf(" h ")" =>
  (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {E : SkewExchangeMatrix (Fin (n + 1))} (P : ChargeSeed E N)
  (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = rayChargeMap s)

local notation "w" => Quiver.Hom.toPath (Generator.toStep (Generator.mutate k) E)
local notation "C" => Quiver.Path.centerPartialMap ℂ w P
local notation "DomainPoint" => CenterPoint (U := Centers) (V := Centers) C
local notation "F" => Quiver.Path.xRationalMap ℂ w
local notation "src(" c ")" => (c) ≫ Scheme.PartialMap.domainSource (X := Centers) (Y := Centers) C
local notation "dst(" c ")" => (c) ≫ Scheme.PartialMap.domainTarget (X := Centers) (Y := Centers) C

include hform hcharge in
/-- At a center in the domain of a mutation, the target character is the source
character precomposed with the integral exponent mutation. -/
theorem mutation_target_character (c : DomainPoint) :
    χ(dst(c)) = χ′(src(c)) := by
  have hE : E.matrix = ε := by rw [← P.matrix_eq, hform, hcharge]
  apply (pointsEquiv ℂ A).symm.injective
  apply Subtype.ext
  simp only [Equiv.symm_apply_apply, Over.comp_left, Scheme.PartialMap.domainTarget_left,
    Scheme.PartialMap.domainSource_left, Quiver.Path.centerPartialMap_hom, ← Category.assoc]
  have h := Quiver.Path.pointsEquiv_symm_comp_centerIso_hom ℂ w χ(src(c))
  rw [Quiver.Path.exponentEquiv_toPath, Step.exponentEquiv_mutate, hE] at h
  simpa only [Equiv.symm_apply_apply, Over.comp_left, Scheme.PartialMap.domainSource_left] using h

include hOpp hform hcharge in
/-- The center open separates the pivot from every other center on the pivot ray
and from the inverse of each center on the opposite ray. -/
theorem mutation_center_conditions (c : DomainPoint) :
    (∀ j, j ≠ k → (s j).primitiveGenerator = (ρ).primitiveGenerator →
      center(χ(src(c))) j ≠ center(χ(src(c))) k) ∧
    (∀ j, j ≠ k → (s j).primitiveGenerator = -(ρ).primitiveGenerator →
      center(χ(src(c))) j * center(χ(src(c))) k ≠ 1) := by
  let x : S := default
  have hmem : (src(c)).left x ∈ mutationCenterOpen b s k hOpp ℂ := by
    rw [mutationCenterOpen_eq_centerOpen b s k hOpp ℂ P hform hcharge,
      ← Quiver.Path.centerPartialMap_domain, Over.comp_left, Scheme.PartialMap.domainSource_left,
      Scheme.Hom.comp_apply]
    exact (c.left x).property
  have h := (point_mem_mutationCenterOpen_iff b s k hOpp ℂ χ(src(c)) x).mp
    (by simpa only [Equiv.symm_apply_apply] using hmem)
  exact ⟨fun j hj he ↦ h.1 j k hj (Ray.primitiveGenerator_injective he), fun j _ ↦ h.2 j⟩

variable [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty (Φ.mutationFan b
  (s k).primitiveGenerator_ne_zero (s k).hull_primitiveGenerator_mem hOpp).cones]

variable {m l : ℕ} [NeZero m] [NeZero l]
  {L₀ L₁ : Type} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  {P₀ : Point (Over.mk (structureMap ℂ (Fin (n + 1) → ℤ))) →
    MarkedSurface ℂ m B₀ (scheme ℂ (Fin (n + 1) →₀ ℤ))}
  {P₁ : Point (Over.mk (structureMap ℂ (Fin (n + 1) → ℤ))) →
    MarkedSurface ℂ m B₁ (scheme ℂ (Fin (n + 1) →₀ ℤ))}

local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "Pic[" Φ "," n "]" =>
  Additive (LineBundleClass (Fan.algebraicRealization Φ)) × (Fin (n + 1) → ℤ)

variable [PrestableFamily (Dtor[Φ,hΦ₀] ↘ Spec (CommRingCat.of ℂ))]
  [PrestableFamily (Dtor[MutFan[b,s,k,hOpp],hΨ₀] ↘ Spec (CommRingCat.of ℂ))]
  {γ₀ γ₁ : Type*} {a₀ : γ₀ → (Dtor[Φ,hΦ₀] ↘ Spec (CommRingCat.of ℂ)).smoothLocus}
  {a₁ : γ₁ → (Dtor[MutFan[b,s,k,hOpp],hΨ₀] ↘ Spec (CommRingCat.of ℂ)).smoothLocus}
  {T₀ : Scheme.NodalCycleNumbering a₀ l} {T₁ : Scheme.NodalCycleNumbering a₁ l}
  {o₀ o₁ : ZMod l} {J₀ : L₀ →ₗ[ℤ] Pic[Φ,n]} {J₁ : L₁ →ₗ[ℤ] Pic[MutFan[b,s,k,hOpp],n]}
  {r₀ : ZMod l ≃ Φ.Ray} {r₁ : ZMod l ≃ (MutFan[b,s,k,hOpp]).Ray}

local notation "M(" c ")" => P₀ (src(c))
local notation "M′(" c ")" => P₁ (dst(c))
local notation "Aux₀(" c ")" => Sigma.fst (internalBlowupTower (h₀ := hΦ₀) b s
  center(χ(src(c))))
local notation "Aux₁(" c ")" => Sigma.fst (internalBlowupTower (h₀ := hΨ₀) b (t)
  center(χ(dst(c))))
local notation "Models₀(" c ")" => ContractedToricFiber (h₀ := hΦ₀)
  b s hΦ T₀ o₀ J₀ χ(src(c)) (M(c))
local notation "Models₁(" c ")" => ContractedToricFiber (h₀ := hΨ₀)
  b (t) (hΨ) T₁ o₁ J₁ χ(dst(c)) (M′(c))

include hform hcharge in
/-- A mutation between fixed marked contractions over the noncollision open gives a
geometric realization of the typed mutation step. The Picard pullback is the integral
mutation isometry. The action on numbered branches is rotation by the unique index
whose boundary class pulls back to the class of source component zero. -/
theorem exists_mutate
    (hr₀ : ∀ j, T₀.component j = Φ.boundaryNormalizationComponentEquiv hΦ (r₀ j))
    (hr₁ : ∀ j, T₁.component j = (Ψ).boundaryNormalizationComponentEquiv (hΨ) (r₁ j))
    (hAdjacent : b.detDualEquiv (r₀ 0).primitiveGenerator (r₀ 1).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (r₀ 0).toCone ≤ σ ∧ (r₀ 1).toCone ≤ σ)
    (hPositive : ∀ j, b.detDualEquiv (r₁ j).primitiveGenerator
      (r₁ (j + 1)).primitiveGenerator = 1)
    (I : B₁.IsometryEquiv B₀)
    (hI : ∀ x, J₀ (I x) = mutationPicardEquiv b s k hOpp hΦ (J₁ x))
    (hD₀ : ∀ c : DomainPoint, (M(c)).pair.hom.left.ker.IsEffectiveCartier)
    (hD₁ : ∀ c : DomainPoint, (M′(c)).pair.hom.left.ker.IsEffectiveCartier)
    (hnef₀ : ∀ c, IsNef ℂ ((M(c)).surface ↘ S) classOf(hD₀ c))
    (hnef₁ : ∀ c, IsNef ℂ ((M′(c)).surface ↘ S) classOf(hD₁ c))
    (hsq₀ : ∀ c, Chow.classIntersectionNumber ℂ (M(c)).surface
      classOf(hD₀ c) classOf(hD₀ c) = 0)
    (hsq₁ : ∀ c, Chow.classIntersectionNumber ℂ (M′(c)).surface
      classOf(hD₁ c) classOf(hD₁ c) = 0)
    (hmodel₀ : ∀ c : DomainPoint, ∃ p : Models₀(c), ∃ (Y : Scheme) (a : ℕ)
        (T : BlowupTower (M(c)).surface a Y) (e : Y ≅ Aux₀(c)),
      IsNodalBoundaryTower (M(c)).pair.hom.left.ker ((M(c)).surface ↘ S) (𝟙 _) T ∧
        p.projection = e.inv ≫ T.toBase)
    (hmodel₁ : ∀ c : DomainPoint, ∃ q : Models₁(c), ∃ (Y : Scheme) (a : ℕ)
        (T : BlowupTower (M′(c)).surface a Y) (e : Y ≅ Aux₁(c)),
      IsNodalBoundaryTower (M′(c)).pair.hom.left.ker ((M′(c)).surface ↘ S) (𝟙 _) T ∧
        q.projection = e.inv ≫ T.toBase)
    (D₀ : L₀) (D₁ : ZMod m → L₁)
    (hmark₀ : ∀ c, (M(c)).boundaryClass (hD₀ c) 0 = D₀)
    (hmark₁ : ∀ c j, (M′(c)).boundaryClass (hD₁ c) j = D₁ j)
    (hD₁inj : Function.Injective D₁) :
    ∃ (R : GeometricRealization (T₀ := Centers) (T₁ := Centers) P₀ P₁ C F) (j : ZMod m),
      R.picard = I ∧ R.boundaryAction = DihedralGroup.r j ∧ I (D₁ j) = D₀ := by
  have hf (c : DomainPoint) :
      ∃ j : ZMod m, Nonempty (FiberRealization (M(c)) (M′(c)) F I (DihedralGroup.r j)) ∧
        I (D₁ j) = D₀ := by
    obtain ⟨p, _, _, _, e₀, hP, hproj₀⟩ := hmodel₀ c
    have htarget := hmodel₁ c
    rw [mutation_target_character b s k P hform hcharge c] at htarget
    obtain ⟨q, _, _, _, e₁, hQ, hproj₁⟩ := htarget
    obtain ⟨hsame, hopp⟩ := mutation_center_conditions b s k hOpp P hform hcharge c
    have hE : E.matrix = ε := by rw [← P.matrix_eq, hform, hcharge]
    obtain ⟨j, R, -, -, -, -⟩ := FiberRealization.exists_mutate b s k hOpp hΦ χ(src(c))
      p q hr₀ hr₁ hAdjacent hPositive I hI hsame hopp hP hQ e₀ e₁ hproj₀ hproj₁
      (hD₀ c) (hD₁ c) (hnef₀ c) (hnef₁ c) (hsq₀ c) (hsq₁ c) E
      (fun j ↦ congrFun (congrFun hE j) k)
    refine ⟨j, ⟨R⟩, ?_⟩
    have h := R.picard_boundaryClass (hD₀ c) (hD₁ c) j
    simpa only [inv_r, cycleVertexPerm_r_apply, add_neg_cancel, hmark₀, hmark₁] using h
  obtain ⟨c₀⟩ := nonempty_centerPoint (T₀ := Centers) (T₁ := Centers) C
  obtain ⟨j, -, hj⟩ := hf c₀
  have fibers (c : DomainPoint) :
      Nonempty (FiberRealization (M(c)) (M′(c)) F I (DihedralGroup.r j)) := by
    obtain ⟨j', R, hj'⟩ := hf c
    have he := hD₁inj (I.injective (hj'.trans hj.symm))
    exact he ▸ R
  exact ⟨⟨I, DihedralGroup.r j, fun c ↦ Classical.choice (fibers c)⟩, j, rfl, rfl, hj⟩

end QPainleve.SignedClusterModularGroup.GeometricRealization

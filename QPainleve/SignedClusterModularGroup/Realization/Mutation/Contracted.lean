/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Mutation.Family
public import QPainleve.SignedClusterModularGroup.Realization.Mutation.Transport

import QPainleve.Geometry.Toric.Fan.Boundary.DualGraph

/-!
# Mutating a family of ordered toric presentations

The fixed-center transport of
`ContractedToricFiber.exists_target_contraction_of_ordered_mutation` gives
one target presentation over the center open. The target fan, branch numbering
and Picard inclusion are independent of the center. A nodal contraction for the
source also presents the target via the auxiliary isomorphism. Keeping the
contracted surface and its marking gives the identity on Picard classes and
numbered branches. The construction can start from any dense open in the
mutation domain, as is needed after previous steps of a word.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative PointedCone
open Module (Basis)
open QPainleve.BlowupTower QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan
open Scheme Scheme.PartialMap

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) {n : ℕ}
  (s : Fin (n + 1) → Φ.Ray) (k : Fin (n + 1))
  (hOpp : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones)
  (hΦ : Φ.IsRegular)

local notation "hv" => Ray.primitiveGenerator_ne_zero (s k)
local notation "hp" => Ray.hull_primitiveGenerator_mem (s k)
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hOpp) hΦ
local notation "t" => Φ.mutationFanCenterRays b s k hOpp
local notation "shear" => Φ.mutationFanRayEquiv b hv hp hOpp

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "A" => (Fin (n + 1) → ℤ)
local notation "Centers" => Over.mk (structureMap ℂ A)
local notation "XTor" => scheme ℂ (Fin (n + 1) →₀ ℤ)
local notation "χ(" c ")" => pointsEquiv ℂ A
  (Subtype.mk (CommaMorphism.left (c : Point Centers)) (Over.w (c : Point Centers)))
local notation "ε" => chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s)
local notation "centers(" a ")" => fun j : Fin (n + 1) ↦ (a) (ofAdd (Pi.single j 1))
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)

variable {E : SkewExchangeMatrix (Fin (n + 1))} (P : ChargeSeed E N)
  (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = rayChargeMap s)

local notation "step" => Generator.toStep (Generator.mutate k) E
local notation "w" => Quiver.Hom.toPath step
local notation "C" => Quiver.Path.centerPartialMap ℂ w P
local notation "F" => Quiver.Path.xRationalMap ℂ w

variable (U : (scheme ℂ (Fin (n + 1) → ℤ)).Opens)
  (hU : Dense (U : Set (scheme ℂ (Fin (n + 1) → ℤ))))
  (hle : U ≤ (Quiver.Path.centerPartialMap ℂ ((Generator.mutate k).toStep E).toPath P).domain)

local notation "C'" => Scheme.PartialMap.restrict C U hU hle
local notation "src(" c ")" => (c) ≫ Scheme.PartialMap.domainSource (X := Centers) (Y := Centers) C'
local notation "dst(" c ")" => (c) ≫ Scheme.PartialMap.domainTarget (X := Centers) (Y := Centers) C'

variable [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty (Φ.mutationFan b
  (s k).primitiveGenerator_ne_zero (s k).hull_primitiveGenerator_mem hOpp).cones]
  [PrestableFamily (Dtor[Φ,hΦ₀] ↘ S)]
  {m l : ℕ} [NeZero m] [NeZero l]
  {L : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
  {γ : Type*} {a : γ → (Dtor[Φ,hΦ₀] ↘ S).smoothLocus}
  {T : Scheme.NodalCycleNumbering a l} {o : ZMod l}
  {J : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin (n + 1) → ℤ)}
  (M : Point (Over.mk (structureMap ℂ (Fin (n + 1) → ℤ))) →
    MarkedSurface ℂ m H (scheme ℂ (Fin (n + 1) →₀ ℤ)))
  (r : ZMod l ≃ Φ.Ray)

local notation "J'" => LinearMap.comp
  (LinearEquiv.toLinearMap (LinearEquiv.symm (mutationPicardEquiv b s k hOpp hΦ))) J

local notation "Aux[" b "," s "," h "," c "]" =>
  internalBlowupTower (h₀ := h) b s centers(χ(c))

private theorem exists_mutation_numbering (hc : Φ.IsComplete)
    (hpos : ∀ j, b.detDualEquiv (r j).primitiveGenerator (r (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (r j).toCone ≤ σ ∧ (r (j + 1)).toCone ≤ σ) :
    ∃ (hpre : PrestableFamily (Dtor[Ψ,hΨ₀] ↘ S)),
      letI := hpre
      ∃ T' : Scheme.NodalCycleNumbering
          (Empty.elim : Empty → (Dtor[Ψ,hΨ₀] ↘ S).smoothLocus) l,
      (∀ j, T'.component j = (Ψ).boundaryNormalizationComponentEquiv (hΨ) (shear (r j))) ∧
      ∀ j, b.detDualEquiv (shear (r j)).primitiveGenerator
        (shear (r (j + 1))).primitiveGenerator = 1 ∧
        ∃ σ : (Ψ).cones, (shear (r j)).toCone ≤ σ ∧ (shear (r (j + 1))).toCone ≤ σ := by
  have hc' := (Φ.isComplete_mutationFan_iff b hv hp hOpp).mpr hc
  let u := (s k).mutationBoundaryIso b hOpp (1 : ℂˣ) hΦ
  have hpre : PrestableFamily (Dtor[Ψ,hΨ₀] ↘ S) := by
    rw [← comp_over u.inv S]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily)
      u.inv _).2 inferInstance
  let _ := hpre
  let r' := r.trans (shear)
  have ht (j : ZMod l) : b.detDualEquiv (r' j).primitiveGenerator
      (r' (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : (Ψ).cones, (r' j).toCone ≤ σ ∧ (r' (j + 1)).toCone ≤ σ := by
    obtain ⟨hd, σ, h₀, h₁⟩ := hpos j
    let e := Φ.mutationFanConeEquiv b hv hp hOpp
    refine ⟨(Φ.detDualEquiv_mutationFanRayEquiv_of_le b hv hp hOpp h₀ h₁).trans hd, e σ, ?_, ?_⟩
    · simpa only [r', Equiv.trans_apply, mutationFanRayEquiv_toCone] using e.monotone h₀
    · simpa only [r', Equiv.trans_apply, mutationFanRayEquiv_toCone] using e.monotone h₁
  obtain ⟨edge, branches, vertices, hcycle, hcomponent, -⟩ :=
    (Ψ).exists_toric_boundary_dualGraph_cycle (hΨ) hc' Empty.elim b r' ht
  let T' : Scheme.NodalCycleNumbering
      (Empty.elim : Empty → (Dtor[Ψ,hΨ₀] ↘ S).smoothLocus) l :=
    ⟨vertices, edge, branches, hcycle⟩
  have hr' (j : ZMod l) : T'.component j = (Ψ).boundaryNormalizationComponentEquiv (hΨ) (r' j) :=
    by simpa only [Scheme.NodalCycleNumbering.component_apply, T'] using hcomponent j
  exact ⟨hpre, T', hr', ht⟩

section Fibers

variable [PrestableFamily (Dtor[Φ.mutationFan b (s k).primitiveGenerator_ne_zero
  (s k).hull_primitiveGenerator_mem hOpp,hΨ₀] ↘ S)]
  (T' : Scheme.NodalCycleNumbering
    (Empty.elim : Empty → (Dtor[Φ.mutationFan b (s k).primitiveGenerator_ne_zero
      (s k).hull_primitiveGenerator_mem hOpp,hΨ₀] ↘ S).smoothLocus) l)

include hform hcharge in
private theorem exists_mutation_fiber
    (hr : ∀ j, T.component j = Φ.boundaryNormalizationComponentEquiv hΦ (r j))
    (hr' : ∀ j, T'.component j = (Ψ).boundaryNormalizationComponentEquiv (hΨ) (shear (r j)))
    (hAdjacent : b.detDualEquiv (r 0).primitiveGenerator (r 1).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (r 0).toCone ≤ σ ∧ (r 1).toCone ≤ σ)
    (hPositive : ∀ j, b.detDualEquiv (shear (r j)).primitiveGenerator
      (shear (r (j + 1))).primitiveGenerator = 1)
    (c : CenterPoint (U := Centers) (V := Centers) C')
    (hmodel :
      ∃ (p : ContractedToricFiber (h₀ := hΦ₀) b s hΦ T o J χ(src(c)) (M (src(c))))
        (Y : Scheme) (d : ℕ) (W : BlowupTower (M (src(c))).surface d Y)
        (e : Y ≅ (Aux[b,s,hΦ₀,src(c)]).1),
      IsNodalBoundaryTower (M (src(c))).pair.hom.left.ker ((M (src(c))).surface ↘ S) (𝟙 _) W ∧
        p.projection = e.inv ≫ W.toBase) :
      ∃ (ev : (M (src(c))).surface ⤏ XTor)
        (R : FiberRealization (M (src(c))) ((M (src(c))).withEvaluation ev) F (.refl H) 1),
      R.iso = Iso.refl _ ∧
      ∃ (p : ContractedToricFiber (h₀ := hΨ₀) b (t) (hΨ) T' o J' χ(dst(c))
          ((M (src(c))).withEvaluation ev))
        (Y : Scheme) (d : ℕ) (W : BlowupTower (M (src(c))).surface d Y)
        (e : Y ≅ (Aux[b,t,hΨ₀,dst(c)]).1),
        IsNodalBoundaryTower (M (src(c))).pair.hom.left.ker ((M (src(c))).surface ↘ S) (𝟙 _) W ∧
          p.projection = e.inv ≫ W.toBase := by
  let r' := r.trans (shear)
  let inclusion := (C).restrictDomainHom (X := Centers) (Y := Centers) U hU hle
  let c₀ := c ≫ inclusion
  have hs : c₀ ≫ (C).domainSource (X := Centers) (Y := Centers) = src(c) := by
    simpa only [c₀, inclusion, Category.assoc] using congrArg (c ≫ ·)
      ((C).restrictDomainHom_source (X := Centers) (Y := Centers) U hU hle)
  have hd : c₀ ≫ (C).domainTarget (X := Centers) (Y := Centers) = dst(c) := by
    simpa only [c₀, inclusion, Category.assoc] using congrArg (c ≫ ·)
      ((C).restrictDomainHom_target (X := Centers) (Y := Centers) U hU hle)
  obtain ⟨p, Y, d, W, e, hW, hp₀⟩ := hmodel
  obtain ⟨hsame, hopp⟩ := mutation_center_conditions b s k hOpp P hform hcharge c₀
  rw [hs] at hsame hopp
  have hχ := mutation_target_character b s k P hform hcharge c₀
  rw [hs, hd] at hχ
  have hE : E.matrix = ε := by rw [← P.matrix_eq, hform, hcharge]
  have hf :=
    ContractedToricFiber.exists_target_contraction_of_ordered_mutation b s k hOpp hΦ χ(src(c))
      p r r'
      hr hr' hAdjacent hPositive hsame hopp E
      (fun j ↦ congrFun (congrFun hE j) k)
  have ho : r'.symm (shear (r o)) = o := r'.symm_apply_apply o
  obtain ⟨f, q, hq, -, R, hR⟩ := hf
  -- Replace the origin in the target model and its projection equation together.
  generalize hindex : r'.symm (shear (r o)) = o' at q hq
  have : o' = o := hindex.symm.trans ho
  clear hindex
  subst o'
  refine ⟨_, R, hR, ?_⟩
  rw [hχ]
  refine ⟨q, Y, d, W, e ≪≫ f, hW, hq.trans ?_⟩
  calc
    f.inv ≫ p.projection = f.inv ≫ e.inv ≫ W.toBase := congrArg (f.inv ≫ ·) hp₀
    _ = (e ≪≫ f).inv ≫ W.toBase := by rw [Iso.trans_inv, Category.assoc]

end Fibers

include hform hcharge in
/-- Transport a marked family through a mutation on any dense open of its center
domain. The target numbering follows the shear on the auxiliary rays and has
positive determinant on consecutive pairs. At corresponding centers the
target uses the source pair, Picard marking and numbered branches. Its nodal
contraction uses the inverse integral mutation on the auxiliary Picard inclusion. -/
theorem exists_mutate_contracted (hc : Φ.IsComplete)
    (hr : ∀ j, T.component j = Φ.boundaryNormalizationComponentEquiv hΦ (r j))
    (hpos : ∀ j, b.detDualEquiv (r j).primitiveGenerator (r (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (r j).toCone ≤ σ ∧ (r (j + 1)).toCone ≤ σ)
    (hmodel : ∀ c : CenterPoint (U := Centers) (V := Centers) C',
      ∃ (p : ContractedToricFiber (h₀ := hΦ₀) b s hΦ T o J χ(src(c)) (M (src(c))))
        (Y : Scheme) (d : ℕ) (W : BlowupTower (M (src(c))).surface d Y)
        (e : Y ≅ (Aux[b,s,hΦ₀,src(c)]).1),
      IsNodalBoundaryTower (M (src(c))).pair.hom.left.ker ((M (src(c))).surface ↘ S) (𝟙 _) W ∧
        p.projection = e.inv ≫ W.toBase) :
    ∃ (hpre : PrestableFamily (Dtor[Ψ,hΨ₀] ↘ S)),
      letI := hpre
      ∃ (T' : Scheme.NodalCycleNumbering
          (Empty.elim : Empty → (Dtor[Ψ,hΨ₀] ↘ S).smoothLocus) l)
        (M' : Point Centers → MarkedSurface ℂ m H XTor)
        (R : GeometricRealization (T₀ := Centers) (T₁ := Centers) M M' C' F),
      (∀ j, T'.component j = (Ψ).boundaryNormalizationComponentEquiv (hΨ) (shear (r j))) ∧
      (∀ j, b.detDualEquiv (shear (r j)).primitiveGenerator
        (shear (r (j + 1))).primitiveGenerator = 1 ∧
        ∃ σ : (Ψ).cones, (shear (r j)).toCone ≤ σ ∧ (shear (r (j + 1))).toCone ≤ σ) ∧
      (Quiver.Path.chargeTarget w P).charge = rayChargeMap (t) ∧
      R.picard = LinearMap.BilinForm.IsometryEquiv.refl H ∧ R.boundaryAction = 1 ∧
      ∀ c : CenterPoint (U := Centers) (V := Centers) C',
        ∃ (ev : (M (src(c))).surface ⤏ XTor) (hM : M' (dst(c)) = (M (src(c))).withEvaluation ev),
        (R.fiber c).iso ≪≫ eqToIso (congrArg MarkedSurface.pair hM) = Iso.refl _ ∧
        ∃ (p : ContractedToricFiber (h₀ := hΨ₀) b (t) (hΨ) T' o J' χ(dst(c)) (M' (dst(c))))
          (Y : Scheme) (d : ℕ) (W : BlowupTower (M' (dst(c))).surface d Y)
          (e : Y ≅ (Aux[b,t,hΨ₀,dst(c)]).1),
        IsNodalBoundaryTower (M' (dst(c))).pair.hom.left.ker ((M' (dst(c))).surface ↘ S) (𝟙 _) W ∧
          p.projection = e.inv ≫ W.toBase := by
  classical
  obtain ⟨hpre, T', hr', ht⟩ := exists_mutation_numbering b s k hOpp hΦ r hc hpos
  let _ := hpre
  have hcharge' : (Quiver.Path.chargeTarget w P).charge = rayChargeMap (t) := by
    rw [Quiver.Hom.toPath, Quiver.Path.chargeTarget_cons, Quiver.Path.chargeTarget_nil,
      Step.chargeTarget_mutate_charge, hform, hcharge, rayChargeMap_mutationFanCenterRays]
  have hdata (c : CenterPoint (U := Centers) (V := Centers) C') :=
    exists_mutation_fiber b s k hOpp hΦ P hform hcharge U hU hle M r T'
      hr hr' (by simpa only [zero_add] using hpos 0) (fun j ↦ (ht j).1) c (hmodel c)
  choose ev R₁ hR hW using hdata
  have hhom : ((C').domainTarget (X := Centers) (Y := Centers)).left =
      U.ι ≫ (Quiver.Path.centerIso ℂ w).hom := by
    simp only [domainTarget_left, PartialMap.restrict_hom, Quiver.Path.centerPartialMap_hom,
      Scheme.homOfLE_ι_assoc]
    -- The domain of the restricted partial map is `U`.
    rfl
  have hleft : Mono ((C').domainTarget (X := Centers) (Y := Centers)).left :=
    hhom ▸ inferInstanceAs (Mono (U.ι ≫ (Quiver.Path.centerIso ℂ w).hom))
  have hmono := Over.mono_of_mono_left ((C').domainTarget (X := Centers) (Y := Centers))
  have hinj : Function.Injective (fun c : CenterPoint (U := Centers) (V := Centers) C' ↦ dst(c)) :=
    fun _ _ h ↦ (cancel_mono ((C').domainTarget (X := Centers) (Y := Centers))).mp h
  -- The family type is indexed by the whole torus. Only the image of the open
  -- is used by the realization and the target contraction.
  let M' : Point Centers → MarkedSurface ℂ m H XTor :=
    Function.extend (fun c : CenterPoint (U := Centers) (V := Centers) C' ↦ dst(c))
      (fun c ↦ (M (src(c))).withEvaluation (ev c)) M
  have hM (c : CenterPoint (U := Centers) (V := Centers) C') :
      M' (dst(c)) = (M (src(c))).withEvaluation (ev c) :=
    hinj.extend_apply _ _ _
  let R : GeometricRealization (T₀ := Centers) (T₁ := Centers) M M' C' F :=
    ⟨.refl H, 1, fun c ↦ (hM c).symm ▸ R₁ c⟩
  refine ⟨hpre, T', M', R, hr', ht, hcharge', rfl, rfl, fun c ↦ ⟨ev c, hM c, ?_, ?_⟩⟩
  · have hIso {Y : MarkedSurface ℂ m H XTor}
        (hY : Y = (M (src(c))).withEvaluation (ev c)) :
        (hY.symm ▸ R₁ c : FiberRealization (M (src(c))) Y F (.refl H) 1).iso ≪≫
            eqToIso (congrArg MarkedSurface.pair hY) = Iso.refl _ := by
      subst Y
      simpa using hR c
    exact hIso (hM c)
  · rw [hM]
    exact hW c

end QPainleve.SignedClusterModularGroup.GeometricRealization

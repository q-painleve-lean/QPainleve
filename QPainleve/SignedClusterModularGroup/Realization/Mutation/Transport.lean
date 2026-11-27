/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Mutation.Basic

import QPainleve.Geometry.Toric.Fan.Mutation.CycleAction

/-!
# Transporting a toric presentation through mutation

An elementary transformation changes the ordered toric model of a marked surface.
Transporting the original contraction along the auxiliary isomorphism gives the
contraction in the mutated presentation. The auxiliary Picard inclusion changes by
the inverse of the integral mutation formula, and the resulting fixed-center
realization has the identity action on the underlying marked pair.

The auxiliary isomorphism is the elementary transformation of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1][GHK].

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative PointedCone
open Module (Basis)
open QPainleve.BlowupTower QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan
open Scheme.IdealSheafData LineBundleClass

namespace QPainleve.SignedClusterModularGroup

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {n : ℕ} (b : Basis (Fin 2) ℤ N)
  (s : Fin (n + 1) → Φ.Ray) (k : Fin (n + 1))
  (hOpp : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones) (hΦ : Φ.IsRegular)
  (χ : Multiplicative (Fin (n + 1) → ℤ) →* k₀ˣ)

local notation "ρ" => s k
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hOpp) hΦ
local notation "shear" => Φ.mutationFanRayEquiv b hv hp hOpp
local notation "t" => Φ.mutationFanCenterRays b s k hOpp
local notation "ε" => chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s)
local notation "χ′" => MonoidHom.comp χ (AddMonoidHom.toMultiplicative
  (AddEquiv.toAddMonoidHom (LinearEquiv.toAddEquiv (chargeMutationEquiv ε k))))
local notation "center" a:arg => (fun j ↦ a (ofAdd (Pi.single j 1)))
local notation "d" => center χ
local notation "d′" => center χ′
local notation "c" => (d) k
local notation "S" => Spec (CommRingCat.of k₀)
local notation "Xtor[" coeff "," r "]" => Spec (CommRingCat.of (LaurentRing coeff (Fin r)))
local notation "D[" coeff "," Φ "," h "]" => Scheme.IdealSheafData.subscheme
  (Fan.toricBoundaryIdeal coeff Φ h)
local notation "Pic[" coeff "," Φ "," r "]" =>
  Additive (LineBundleClass (Fan.finiteFanScheme coeff Φ)) × (Fin r → ℤ)

variable [hΦ₀ : Nonempty Φ.cones]
  [hΨ₀ : Nonempty (Φ.mutationFan b (s k).primitiveGenerator_ne_zero
    (s k).hull_primitiveGenerator_mem hOpp).cones]

local notation "A" => internalBlowupTower k₀ (h₀ := hΦ₀) b s (d)
local notation "B" => internalBlowupTower k₀ (h₀ := hΨ₀) b (t) (d′)
local notation "ιA" => WithBoundary.boundaryι (Sigma.snd A)
local notation "ιB" => WithBoundary.boundaryι (Sigma.snd B)
local notation "πA" => BlowupTower.toBase (WithBoundary.toTower (Sigma.snd A))
local notation "πB" => BlowupTower.toBase (WithBoundary.toTower (Sigma.snd B))
local notation "u" => Ray.mutationBoundaryIso b ρ hOpp c hΦ
local notation "I" => mutationPicardEquiv k₀ b s k hOpp hΦ

variable {m l : ℕ} [NeZero m] [NeZero l] {L : Type} [AddCommGroup L]
  {H : LinearMap.BilinForm ℤ L} {M : MarkedSurface k₀ m H Xtor[k₀,n + 1]}
  [PrestableFamily (D[k₀,Φ,hΦ₀] ↘ Spec (.of k₀))]
  [PrestableFamily (D[k₀,Φ.mutationFan b (s k).primitiveGenerator_ne_zero
    (s k).hull_primitiveGenerator_mem hOpp,hΨ₀] ↘ Spec (.of k₀))]
  {γ₀ γ₁ : Type*} {a₀ : γ₀ → (D[k₀,Φ,hΦ₀] ↘ Spec (.of k₀)).smoothLocus}
  {a₁ : γ₁ → (D[k₀,Φ.mutationFan b (s k).primitiveGenerator_ne_zero
    (s k).hull_primitiveGenerator_mem hOpp,hΨ₀] ↘ Spec (.of k₀)).smoothLocus}
  {T₀ : Scheme.NodalCycleNumbering a₀ l} {T₁ : Scheme.NodalCycleNumbering a₁ l}
  {o₀ o₁ : ZMod l} {J : L →ₗ[ℤ] Pic[k₀,Φ,n + 1]}
  (p : ContractedToricFiber (h₀ := hΦ₀) b s hΦ T₀ o₀ J χ M)

local notation "J′" => LinearMap.comp (LinearEquiv.toLinearMap (LinearEquiv.symm (I))) J
local notation "qProj(" e ")" => Iso.inv e ≫ ContractedToricFiber.projection p
local notation "eval′(" f ")" => Fan.contractedXEvaluation k₀ b (t) (χ′) (hΨ) f

omit [PrestableFamily (D[k₀,Ψ,hΨ₀] ↘ S)] in
private theorem transported_marked_pullback (e : (A).1 ≅ (B).1)
    (hmark : ∀ x : Pic[k₀,Ψ,n + 1],
      pullback e.hom (internalBlowupPicardMarking k₀ b (t) (d′) (hΨ) x).toMul =
        (internalBlowupPicardMarking k₀ b s (d) hΦ (I x)).toMul) (x : L) :
    (internalBlowupPicardMarking k₀ b (t) (d′) (hΨ)).symm
        (Additive.ofMul (pullback (qProj(e)) (M.picardMarking x).toMul)) = J′ x := by
  apply (I).injective
  have hsquare : e.hom ≫ qProj(e) = p.projection ≫ (Iso.refl M.surface).hom := by
    simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  have hpullback := pullback_nodal_mutation_picard_marking k₀ b s k hOpp hΦ (d) (d′)
    hsquare (by simpa only [internalBlowupPicardMarking_apply] using hmark)
    (M.picardMarking x).toMul
  rw [Iso.refl_hom, pullback_id, p.marked_pullback x] at hpullback
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    using hpullback.symm

private def transportMutation (e : (A).1 ≅ (B).1)
    (he : (ιA) ≫ e.hom = (u).hom ≫ (ιB))
    (hover : e.hom ≫ πB ≫ (Fan.finiteFanSchemeToSpec k₀ (Ψ)) =
      πA ≫ (Φ.finiteFanSchemeToSpec k₀))
    (hmark : ∀ x : Pic[k₀,Ψ,n + 1],
      pullback e.hom (internalBlowupPicardMarking k₀ b (t) (d′) (hΨ) x).toMul =
        (internalBlowupPicardMarking k₀ b s (d) hΦ (I x)).toMul)
    (hsign : cycleOrientationSign ((u).boundaryCycleAction T₀ T₁) = 1)
    (horigin : cycleVertexPerm ((u).boundaryCycleAction T₀ T₁) o₀ = o₁) :
    ContractedToricFiber (h₀ := hΨ₀) b (t) (hΨ) T₁ o₁ (J′) (χ′)
      (M.withEvaluation (eval′(qProj(e)))) := by
  let q := qProj(e)
  have hMod : IsModification q := inferInstanceAs (IsModification (qProj(e)))
  let target := M.withEvaluation (eval′(qProj(e)))
  let : PrestableFamily (target.boundary ↘ S) := target.prestable
  let : PrestableFamily (M.boundary ↘ S) := M.prestable
  let : (u).symm.hom.IsOver S := by
    rw [Iso.symm_hom]
    infer_instance
  have hMapOver : ((u).inv ≫ p.boundaryMap).IsOver S := inferInstance
  have huInv : cycleOrientationSign ((u).symm.boundaryCycleAction T₁ T₀) = 1 := by
    rw [Iso.boundaryCycleAction_symm, map_inv, hsign, inv_one]
  have hboundary : (ιB) ≫ e.inv = (u).inv ≫ (ιA) := by
    simpa only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id] using
      (congrArg (fun f ↦ (u).inv ≫ f ≫ e.inv) he).symm
  have hOver : q ≫ (M.surface ↘ S) = πB ≫ (Fan.finiteFanSchemeToSpec k₀ (Ψ)) := by
    rw [Category.assoc, p.projection_over, ← hover, Iso.inv_hom_id_assoc]
  have hComp : ((u).inv ≫ p.boundaryMap) ≫ M.pair.hom.left = (ιB) ≫ q := by
    simp only [Category.assoc, p.boundary_comp, q, reassoc_of% hboundary]
  refine
    { projection := q
      modification := hMod
      projection_over := hOver
      support_comap := ?_
      boundaryMap := (u).inv ≫ p.boundaryMap
      boundary_comp := hComp
      boundary_over := hMapOver
      orientedSubdivision := by
        exact ((u).symm.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one
          T₁ T₀ huInv).comp p.orientedSubdivision
      component_zero := ?_
      marked_pullback := ?_
      evaluation_eq := MarkedSurface.withEvaluation_evaluation _ _ }
  · have ht : (ιA).ker.comap e.inv = (ιB).ker := by
      rw [← (ιB).comap_ker_comp_of_isClosedImmersion e.inv, hboundary, Scheme.Hom.ker_comp_of_isIso]
    have h := congrArg (·.preimage e.inv.continuous) p.support_comap
    rwa [← support_comap, ← support_comap, ht, ← comap_comp] at h
  · have h := (u).apply_componentGenericPoint T₀ T₁ o₀
    rw [horigin] at h
    have hzero : ((u).inv ≫ p.boundaryMap) (T₁.componentGenericPoint o₁) =
        M.cycle.componentGenericPoint 0 := by
      rw [Scheme.Hom.comp_apply, ← h, Scheme.hom_inv_apply]
      exact p.component_zero
    exact hzero
  · intro x
    rw [MarkedSurface.withEvaluation_picardMarking]
    exact transported_marked_pullback b s k hOpp hΦ χ p e hmark x

/-- A noncolliding mutation constructs a marked target contraction from the source
contraction. It uses the same surface, marking and numbered boundary, so any specified
nodal blowup tower for the source also presents the target via the auxiliary
isomorphism. The two ordered toric presentations intertwine the independent X mutation.
The target auxiliary origin is the sheared ray above the original component zero. -/
theorem ContractedToricFiber.exists_target_contraction_of_ordered_mutation
    (r₀ : ZMod l ≃ Φ.Ray) (r₁ : ZMod l ≃ (Ψ).Ray)
    (hr₀ : ∀ j, T₀.component j = Φ.boundaryNormalizationComponentEquiv k₀ hΦ (r₀ j))
    (hr₁ : ∀ j, T₁.component j = (Ψ).boundaryNormalizationComponentEquiv k₀ (hΨ) (r₁ j))
    (hAdjacent : b.detDualEquiv (r₀ 0).primitiveGenerator (r₀ 1).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (r₀ 0).toCone ≤ σ ∧ (r₀ 1).toCone ≤ σ)
    (hPositive : ∀ j, b.detDualEquiv (r₁ j).primitiveGenerator
      (r₁ (j + 1)).primitiveGenerator = 1)
    (hsame : ∀ j, j ≠ k → (s j).primitiveGenerator = Ray.primitiveGenerator ρ → (d) j ≠ c)
    (hopp : ∀ j, j ≠ k → (s j).primitiveGenerator = -Ray.primitiveGenerator ρ → (d) j * c ≠ 1)
    (E : SkewExchangeMatrix (Fin (n + 1))) (hE : ∀ j, E.matrix j k = ε j k) :
    ∃ e : (A).1 ≅ (B).1,
      let target : MarkedSurface k₀ m H Xtor[k₀,n + 1] := M.withEvaluation (eval′(qProj(e)))
      ∃ q : ContractedToricFiber (h₀ := hΨ₀) b (t) (hΨ) T₁ (r₁.symm (shear (r₀ o₀)))
          (J′) (χ′) target,
        q.projection = qProj(e) ∧
        (ιA) ≫ e.hom = (u).hom ≫ (ιB) ∧
        ∃ R : FiberRealization M target
            (((Generator.mutate k).toStep E).toPath.xRationalMap k₀) (.refl H) 1,
          R.iso = Iso.refl M.pair := by
  obtain ⟨e, f, hf, he, hover, hmark, -⟩ :=
    exists_iso_ordered_mutation_picard_marking k₀ b hΦ s χ k hOpp hsame hopp
  have hboundary :=
    boundaryι_comp_of_ordered_mutation k₀ b ρ hOpp c s (d) (t) (d′) hΦ hf he
  have hsign := (ρ).cycleOrientationSign_mutationBoundaryIso k₀ b hOpp c hΦ T₀ T₁
    hr₀ hr₁ hAdjacent hPositive
  have horigin := congrArg r₁.symm
    ((ρ).mutationBoundaryIso_cycleVertexPerm k₀ b hOpp c hΦ T₀ T₁ hr₀ hr₁ o₀)
  rw [Equiv.symm_apply_apply] at horigin
  let q := transportMutation b s k hOpp hΦ χ p e hboundary hover hmark hsign horigin
  have hsquare : p.projection ≫ (Iso.refl M.surface).hom = e.hom ≫ qProj(e) := by
    simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  have heval := compOfDefined_contractedXEvaluation_mutate k₀ b s k χ hOpp hΦ f hf he hsquare E hE
  have hcomp : ∃ h, M.evaluation.compOfDefined
      (((Generator.mutate k).toStep E).toPath.xRationalMap k₀) h = eval′(qProj(e)) := by
    rw [p.evaluation_eq]
    simpa only [Iso.refl_hom, Scheme.RationalMap.id_comp] using heval
  exact ⟨e, q, by rfl, hboundary, FiberRealization.withEvaluation M _ _ hcomp,
    FiberRealization.withEvaluation_iso M _ _ hcomp⟩

end QPainleve.SignedClusterModularGroup

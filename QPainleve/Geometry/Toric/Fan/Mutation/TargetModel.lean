/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Factorization
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Pivot

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Split
import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Geometric

/-!
# The ordered target model of a specified elementary transformation

When an ordered internal blowup model resolves a toric elementary transformation,
the same surface has an ordered internal blowup presentation over the mutated fan.
The reverse pivot comes first. The remaining centers retain their relative order,
including when they are infinitely near points over the reverse pivot. In the
Picard markings, the elementary transformation acts on the two pivot blowups
and leaves the coordinates of the other total exceptional classes fixed.

The elementary transformation is that of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public section

open AlgebraicGeometry CategoryTheory PointedCone
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  (b : Module.Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ)

local notation "v" => Ray.primitiveGenerator ρ
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "hΨ₀" => Nonempty.intro (Φ.mutationFanConeEquiv b hv hp hOpp ρ.toCone)
local notation "shear" => Φ.mutationFanRayEquiv b hv hp hOpp
local notation "reverseRay" => Φ.mutationFanCenterRays b (fun _ : Unit ↦ ρ) () hOpp ()
local notation "I₁" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "P₁" => QPainleve.BlowupTower.nil.snoc (I₁)
local notation "j₁" => Ray.mutationTargetBoundaryι b ρ hOpp c

variable {n : ℕ}

local notation "targetModel(" t "," d ")" =>
  internalBlowupTower (h₀ := hΨ₀) b (Fin.cons reverseRay t) (Fin.cons c⁻¹ d)
local notation "targetTail(" t "," d ")" =>
  alongBoundary (j₁) (fun l ↦ Ray.internalCenter (h₀ := hΨ₀) b (t l) (d l))

omit hΦ₀ in
private theorem exists_iso_targetModel_targetTail (t : Fin n → (Ψ).Ray) (d : Fin n → ℂˣ) :
    ∃ e : (targetModel(t,d)).1 ≅ (targetTail(t,d)).1,
      e.hom ≫ (targetTail(t,d)).2.toTower.toBase ≫ (I₁).blowupToBase =
        (targetModel(t,d)).2.toTower.toBase ∧
      (targetModel(t,d)).2.boundaryι ≫ e.hom = (targetTail(t,d)).2.boundaryι ∧
      ∀ a z x, pullback e.hom ((targetTail(t,d)).2.toTower.picardHom
        ((P₁).picardHom (a, fun _ ↦ z), x)).toMul =
          ((targetModel(t,d)).2.toTower.picardHom (a, Fin.cons z x)).toMul := by
  let : Nonempty (Ψ).cones := hΨ₀
  let J := Ray.internalCenter (h₀ := hΨ₀) b (reverseRay) c⁻¹
  have hJ : J.val.map ((Ψ).boundaryIdeal hΨ₀).subschemeι = I₁ := by
    rw [Ray.mutationTargetCenterIdeal_eq]
    exact Ray.map_internalCenter_subschemeι b _ _
  let D := (Ψ).boundaryIdeal hΨ₀
  let K := fun l : Fin n ↦ Ray.internalCenter (h₀ := hΨ₀) b (t l) (d l)
  have hmodel : targetModel(t,d) = alongBoundary D.subschemeι (Fin.cons J K) := by
    rw [internalBlowupTower_eq_alongBoundary]
    congr 1
    exact funext (Fin.cases rfl (fun _ ↦ by simp [K]))
  obtain ⟨e, he, hb, hpic⟩ := exists_iso_alongBoundary_cons J hJ (j₁)
    (ρ.mutationTargetBoundaryι_blowupToBase b hOpp c) K
  rw [hmodel]
  exact ⟨e, he, hb, hpic⟩

variable (s : Fin (n + 1) → Φ.Ray) (d : Fin (n + 1) → ℂˣ)

local notation "A" => internalBlowupTower b s d
local notation "πA" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd A))
local notation "q" => Scheme.PartialMap.toRationalMap
  (Fan.mutationPartialMap Φ b (c : ℂ) hv hp hOpp)
local notation "rays(" k ")" => (fun l ↦ shear (s (Fin.succAbove k l)))
local notation "params(" k ")" => (fun l ↦
  d (Fin.succAbove k l) * c ^ max (b.det ![Ray.primitiveGenerator (s (Fin.succAbove k l)), v]) 0)

/-- A morphism resolving a specified toric mutation presents its source as the ordered
internal blowup tower over the mutated fan. The first occurrence of the source pivot is
replaced by the reverse pivot at the head of the target order. Every other center follows
the shear with its transformed parameter and keeps its relative place in the tail.
The presentation recovers the given morphism and identifies the full strict boundary via
the elementary transformation's boundary isomorphism. The pivot Picard equivalence
computes the two pivot coordinates (toric class and pivot coefficient), and each
other exceptional coefficient is carried back to its original label. -/
theorem Ray.exists_ordered_target_model_of_resolves (hΦ : Φ.IsRegular)
    (r : A.1 ⟶ (Ψ).algebraicRealization)
    (hr : have := isIntegral_internalBlowupTower b s d hΦ
          have := isModification_internalBlowupTower_toBase b s d hΦ
          (πA).toRationalMap.comp q = r.toRationalMap) :
    ∃ k : Fin (n + 1), s k = ρ ∧ d k = c ∧ (∀ l < k, (s l, d l) ≠ (ρ, c)) ∧
      let B := targetModel(rays(k),params(k))
      ∃ e : A.1 ≅ B.1, e.hom ≫ B.2.toTower.toBase = r ∧
        A.2.boundaryι ≫ e.hom =
          (ρ.mutationBoundaryIso b hOpp c hΦ).hom ≫ B.2.boundaryι ∧
        ∀ a z x,
          let y := mutationPicardEquiv b (fun _ : Fin 1 ↦ ρ) 0 hOpp hΦ (a, fun _ ↦ z)
          pullback e.hom (B.2.toTower.picardHom (a, Fin.cons z x)).toMul =
            (A.2.toTower.picardHom (y.1, k.insertNth (y.2 0) x)).toMul := by
  obtain ⟨k, hk, hd, hfirst, f, g, hg, _, hfb, hr', hgb, hfPic⟩ :=
    ρ.exists_ordered_mutation_factorization_of_resolves b c s d hOpp hΦ r hr
  obtain ⟨u, hu, hub, huPic⟩ := exists_iso_targetModel_targetTail b ρ hOpp c (rays(k)) (params(k))
  refine ⟨k, hk, hd, hfirst, f ≪≫ g ≪≫ u.symm, ?_, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hu, Iso.inv_hom_id_assoc]
      using hr'
  · apply (cancel_mono u.hom).mp
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      reassoc_of% hfb, hgb, hub]
  · intro a z x
    dsimp only
    rw [← huPic a z x, pullback_comp]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rw [← pullback_comp, hg.pullback_picardHom,
      ρ.pullback_mutationBlowupIso_picardHom b hOpp c hΦ, ofMul_toMul]
    let y := mutationPicardEquiv b (fun _ : Fin 1 ↦ ρ) 0 hOpp hΦ (a, fun _ ↦ z)
    let x₀ : Fin (n + 1) → ℤ := k.insertNth (y.2 0) x
    have hy : (fun _ : Fin 1 ↦ x₀ k) = y.2 := by
      funext j
      dsimp only [x₀]
      rw [Fin.insertNth_apply_same, Subsingleton.elim j 0]
    have hx : x₀ ∘ k.succAbove = x := Fin.insertNth_comp_succAbove k _ x
    simpa only [hy, hx, x₀, y] using hfPic y.1 x₀

end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.StarFactorization
public import QPainleve.Geometry.Toric.Fan.Mutation.Subdivision
public import QPainleve.Geometry.Toric.Fan.Mutation.TargetModel
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.Logarithmic.Morphism

/-!
# Ordered models for a resolved logarithmic mutation

A specified logarithmic projection and a regular representative of its composite
with a toric mutation admit compatible ordered internal blowup models. The first
occurrence of the pivot is replaced by the reverse pivot, and the other centers
retain their relative order. The comparison identifies the strict boundary as a
scheme and gives the full Picard pullback in the two ordered models.

This is the elementary transformation of [Gross, Hacking and Keel, §3.1][GHK]
in the specified factorization of [Lutz, Theorem 8.4][HKL]. The proof uses
`IsSubdivision.existsUnique_mutation_resolution` to refine the specified target
projection and `Ray.exists_ordered_target_model_of_resolves` to transport the
ordered centers and their Picard coordinates.

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory PointedCone
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "base[" A "]" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd A))

variable {Z : Scheme} [Z.Over S] [IsIntegral Z] [Z.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Z ↘ S)] {P : Z.IdealSheafData}
  (A : LogarithmicProjection i P) (b : Module.Basis (Fin 2) ℤ N)
  (ρ : A.fan.Ray) (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ A.fan.cones) (c : ℂˣ)

local notation "M[" Δ "," r "," h "]" =>
  Fan.mutationFan Δ b (Ray.primitiveGenerator_ne_zero r) (Ray.hull_primitiveGenerator_mem r) h
local notation "μ[" Δ "," r "," h "]" =>
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap Δ b (c : ℂ)
    (Ray.primitiveGenerator_ne_zero r) (Ray.hull_primitiveGenerator_mem r) h)

local notation "liftRay(" H ")" => IsSubdivision.liftRay H ρ
local notation "oppositeRayMem(" H ")" =>
  IsSubdivision.hull_neg_primitiveGenerator_liftRay_mem H ρ hOpp
local notation "mutationSubdivision(" H ")" => IsSubdivision.mutation H b
  (IsSubdivision.primitiveGenerator_liftRay H ρ)
  (Ray.primitiveGenerator_ne_zero ρ) (Ray.primitiveGenerator_ne_zero (liftRay(H)))
  (Ray.hull_primitiveGenerator_mem ρ) hOpp
  (Ray.hull_primitiveGenerator_mem (liftRay(H))) (oppositeRayMem(H))

/-- The two specified projections of a resolved logarithmic mutation are the
projections of two ordered internal models over compatible toric subdivisions.
The reverse pivot becomes the first target center, and every remaining center
is transported by the shear with its transformed parameter. The comparison
identifies the strict boundary via the elementary transformation and carries the
full target Picard marking back to the source marking in its original order. -/
theorem exists_ordered_toric_mutation_models
    (hf : Scheme.BirationalOver A.hom (𝟙 X[A.fan]))
    (r : Z ⟶ X[M[A.fan,ρ,hOpp]])
    (hr : A.hom.toRationalMap.comp μ[A.fan,ρ,hOpp] = r.toRationalMap) :
    ∃ (Ω : Fan i) (hΩ : Ω.IsRegular) (H : Ω.IsSubdivision A.fan),
      letI : Nonempty Ω.cones := H.nonempty_cones_of_nonempty A.isComplete.nonempty_cones
      let σ := liftRay(H)
      let opp := oppositeRayMem(H)
      let Ψ := M[Ω,σ,opp]
      letI : Nonempty Ψ.cones := ⟨Ω.mutationFanConeEquiv b σ.primitiveGenerator_ne_zero
        σ.hull_primitiveGenerator_mem opp σ.toCone⟩
      ∃ (n : ℕ) (a : Fin (n + 1) → Ω.Ray) (u : Fin (n + 1) → ℂˣ) (k : Fin (n + 1)),
        a k = σ ∧ u k = c ∧ (∀ l < k, (a l, u l) ≠ (σ, c)) ∧
        let reverseRay := Ω.mutationFanCenterRays b (fun _ : Unit ↦ σ) () opp ()
        let tailRay := fun l : Fin n ↦ Ω.mutationFanRayEquiv b σ.primitiveGenerator_ne_zero
          σ.hull_primitiveGenerator_mem opp (a (k.succAbove l))
        let tailParam := fun l : Fin n ↦ u (k.succAbove l) *
          c ^ max (b.det ![(a (k.succAbove l)).primitiveGenerator, σ.primitiveGenerator]) 0
        let U := Ω.internalBlowupTower b a u
        let W := Ψ.internalBlowupTower b (Fin.cons reverseRay tailRay)
          (Fin.cons c⁻¹ tailParam)
        ∃ (e : U.1 ≅ Z) (g : U.1 ≅ W.1),
          e.hom ≫ A.hom = base[U] ≫ π[H] ∧
          e.hom ≫ r = g.hom ≫ base[W] ≫ π[mutationSubdivision(H)] ∧
          P.comap e.hom = U.2.boundaryι.ker ∧
          U.2.boundaryι ≫ g.hom = (σ.mutationBoundaryIso b opp c hΩ).hom ≫ W.2.boundaryι ∧
          ∀ d z x,
            let y := mutationPicardEquiv b (fun _ : Fin 1 ↦ σ) 0 opp hΩ (d, fun _ ↦ z)
            pullback g.hom (W.2.toTower.picardHom (d, Fin.cons z x)).toMul =
              (U.2.toTower.picardHom (y.1, k.insertNth (y.2 0) x)).toMul := by
  obtain ⟨Ω, hΩ, H, m, a, u, e, hsource, hboundary⟩ :=
    A.fan.exists_toric_internal_factorization_of_boundary_comap_eq b A.isRegular A.isComplete
      hf A.comap_boundaryIdeal
  let : Nonempty Ω.cones := H.nonempty_cones_of_nonempty A.isComplete.nonempty_cones
  let U := Ω.internalBlowupTower b a u
  let := isIntegral_internalBlowupTower b a u hΩ
  let := isModification_internalBlowupTower_toBase b a u hΩ
  have hres : (base[U] ≫ π[H]).toRationalMap.comp μ[A.fan,ρ,hOpp] =
      (e.hom ≫ r).toRationalMap := by
    simp only [U, ← hsource, ← Scheme.RationalMap.comp_toRationalMap,
      ← Scheme.Hom.toRationalMap_compHom, Scheme.RationalMap.comp_assoc, hr]
  obtain ⟨q, ⟨hq, hproj⟩, -⟩ := H.existsUnique_mutation_resolution b ρ hOpp c
    (isClosedPointTower_internalBlowupTower b a u) A.isRegular hΩ (e.hom ≫ r) hres
  cases m with
  | zero =>
    obtain ⟨k, -⟩ := (liftRay(H)).exists_first_internalBlowupTower_center_of_resolves
      b (oppositeRayMem(H)) c a u q hq
    exact Fin.elim0 k
  | succ n =>
    obtain ⟨k, hk, hu, hfirst, g, hg, hb, hpic⟩ :=
      (liftRay(H)).exists_ordered_target_model_of_resolves b (oppositeRayMem(H)) c a u hΩ q hq
    exact ⟨Ω, hΩ, H, n, a, u, k, hk, hu, hfirst, e, g, hsource,
      hproj.symm.trans (by rw [← hg, Category.assoc]), hboundary, hb, hpic⟩

end TauCeti.Toric.Fan.LogarithmicProjection

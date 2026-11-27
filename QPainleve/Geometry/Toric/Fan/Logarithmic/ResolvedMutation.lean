/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Subdivision

public import QPainleve.Geometry.Toric.Fan.Logarithmic.StarFactorization
public import QPainleve.Geometry.Toric.Fan.Mutation.Subdivision
public import QPainleve.Geometry.Toric.Fan.Mutation.TargetModel

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic

/-!
# Transport of an ordered model through a resolved mutation

An ordered internal blowup model over a subdivision of the source fan determines
a compatible ordered model over the mutated subdivision. Both models recover the
specified regular projections on the same surface. The comparison uses the elementary
transformation of [Gross, Hacking and Keel, §3.1][GHK] in a resolved factorization
as in [Lutz, Theorem 8.4][HKL].

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory PointedCone
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {K : Type} [Field K] [PerfectField K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

local notation "S" => Spec (CommRingCat.of K)
local notation "X[" Φ "]" => Fan.finiteFanScheme K Φ
local notation "π[" H "]" => FanHom.finiteFanSchemeHom K (IsSubdivision.toFanHom H)
local notation "base[" A "]" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd A))

variable {Z : Scheme} [Z.Over (Spec (.of K))] [PreirreducibleSpace Z]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of K))] {P : Z.IdealSheafData}
  (A : LogarithmicProjection K i P) (b : Module.Basis (Fin 2) ℤ N)
  (ρ : A.fan.Ray) (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ A.fan.cones) (c : Kˣ)

local notation "M[" Δ "," r "," h "]" =>
  Fan.mutationFan Δ b (Ray.primitiveGenerator_ne_zero r) (Ray.hull_primitiveGenerator_mem r) h
local notation "μ[" Δ "," r "," h "]" =>
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap K Δ b (c : K)
    (Ray.primitiveGenerator_ne_zero r) (Ray.hull_primitiveGenerator_mem r) h)

local notation "liftRay(" H ")" => IsSubdivision.liftRay H ρ
local notation "oppositeRayMem(" H ")" =>
  IsSubdivision.hull_neg_primitiveGenerator_liftRay_mem H ρ hOpp
local notation "mutationSubdivision(" H ")" => IsSubdivision.mutation H b
  (IsSubdivision.primitiveGenerator_liftRay H ρ)
  (Ray.primitiveGenerator_ne_zero ρ) (Ray.primitiveGenerator_ne_zero (liftRay(H)))
  (Ray.hull_primitiveGenerator_mem ρ) hOpp
  (Ray.hull_primitiveGenerator_mem (liftRay(H))) (oppositeRayMem(H))

/-- Transport a specified ordered internal blowup model through a resolved mutation.
The mutation lifts to the source subdivision. In the given source order, the first
occurrence of the pivot is replaced by the reverse pivot at the head of the target
order. The other centers are transported by the shear and retain their relative order,
including infinitely near centers. The model realizes the refined mutation as a rational
map and recovers the given target morphism and pole ideal on the resolving surface.
The comparison identifies the strict boundaries by the elementary transformation
and computes the Picard pullback in the given source marking. -/
theorem exists_ordered_toric_mutation_model_of_factorization
    {Ω : Fan i} (hΩ : Ω.IsRegular) (H : Ω.IsSubdivision A.fan)
    {m : ℕ} (a : Fin m → Ω.Ray) (u : Fin m → Kˣ)
    (r : Z ⟶ X[M[A.fan,ρ,hOpp]])
    (hr : A.hom.toRationalMap.comp μ[A.fan,ρ,hOpp] = r.toRationalMap) :
    letI : Nonempty Ω.cones := H.nonempty_cones_of_nonempty A.isComplete.nonempty_cones
    let U := Ω.internalBlowupTower K b a u
    ∀ (e : U.1 ≅ Z), e.hom ≫ A.hom = base[U] ≫ π[H] →
      P.comap e.hom = U.2.boundaryι.ker →
      let σ := liftRay(H)
      let opp := oppositeRayMem(H)
      let Ψ := M[Ω,σ,opp]
      letI : Nonempty Ψ.cones := ⟨Ω.mutationFanConeEquiv b σ.primitiveGenerator_ne_zero
        σ.hull_primitiveGenerator_mem opp σ.toCone⟩
      letI : IsIntegral U.1 := isIntegral_internalBlowupTower K b a u hΩ
      letI : IsModification U.2.toTower.toBase :=
        isModification_internalBlowupTower_toBase K b a u hΩ
      ∃ (n : ℕ) (hm : n + 1 = m) (k : Fin (n + 1)),
        let ι := finCongr hm
        a (ι k) = σ ∧ u (ι k) = c ∧ (∀ l < k, (a (ι l), u (ι l)) ≠ (σ, c)) ∧
        let reverseRay := Ω.mutationFanCenterRays b (fun _ : Unit ↦ σ) () opp ()
        let tailRay := fun l : Fin n ↦ Ω.mutationFanRayEquiv b σ.primitiveGenerator_ne_zero
          σ.hull_primitiveGenerator_mem opp (a (ι (k.succAbove l)))
        let tailParam := fun l : Fin n ↦ u (ι (k.succAbove l)) *
          c ^ max (b.det ![(a (ι (k.succAbove l))).primitiveGenerator, σ.primitiveGenerator]) 0
        let W := Ψ.internalBlowupTower K b (Fin.cons reverseRay tailRay) (Fin.cons c⁻¹ tailParam)
        ∃ g : U.1 ≅ W.1,
          g.inv ≫ e.hom ≫ r = base[W] ≫ π[mutationSubdivision(H)] ∧
          P.comap (g.inv ≫ e.hom) = W.2.boundaryι.ker ∧
          (base[U]).toRationalMap.comp μ[Ω,σ,opp] = (g.hom ≫ base[W]).toRationalMap ∧
          U.2.boundaryι ≫ g.hom = (σ.mutationBoundaryIso b opp c hΩ).hom ≫ W.2.boundaryι ∧
          ∀ d z x,
            let y := mutationPicardEquiv K b (fun _ : Fin 1 ↦ σ) 0 opp hΩ (d, fun _ ↦ z)
            pullback g.hom (W.2.toTower.picardHom (d, Fin.cons z x)).toMul =
              (U.2.toTower.picardHom (y.1, k.insertNth (y.2 0) x ∘ ι.symm)).toMul := by
  let : Nonempty Ω.cones := H.nonempty_cones_of_nonempty A.isComplete.nonempty_cones
  intro U e he hP
  let := isIntegral_internalBlowupTower K b a u hΩ
  let := isModification_internalBlowupTower_toBase K b a u hΩ
  let : IrreducibleSpace Z :=
    { isPreirreducible_univ := PreirreducibleSpace.isPreirreducible_univ
      toNonempty := A.hom.denseRange.nonempty }
  have hres : (base[U] ≫ π[H]).toRationalMap.comp μ[A.fan,ρ,hOpp] =
      (e.hom ≫ r).toRationalMap := by
    simp only [← he, ← Scheme.RationalMap.comp_toRationalMap,
      ← Scheme.Hom.toRationalMap_compHom, Scheme.RationalMap.comp_assoc, hr]
  obtain ⟨q, ⟨hq, hproj⟩, -⟩ := H.existsUnique_mutation_resolution K b ρ hOpp c
    (isClosedPointTower_internalBlowupTower K b a u) A.isRegular hΩ (e.hom ≫ r) hres
  cases m with
  | zero =>
    obtain ⟨k, -⟩ := (liftRay(H)).exists_first_internalBlowupTower_center_of_resolves K
      b (oppositeRayMem(H)) c a u q hq
    exact Fin.elim0 k
  | succ n =>
    obtain ⟨k, hk, hu, hfirst, g, hg, hb, hpic⟩ :=
      (liftRay(H)).exists_ordered_target_model_of_resolves K b (oppositeRayMem(H)) c a u hΩ q hq
    have htarget := hproj.symm.trans (by rw [← hg, Category.assoc])
    refine ⟨n, rfl, k, hk, hu, hfirst, g, ?_, ?_, hq.trans ?_, hb, hpic⟩
    · rw [htarget]
      exact g.inv_hom_id_assoc _
    · have hker := (Scheme.Hom.comap_ker_comp_of_isClosedImmersion U.2.boundaryι g.hom).symm
      rw [hb, Scheme.Hom.ker_comp_of_isIso] at hker
      have htargetBoundary := congrArg (fun I ↦ I.comap g.inv) (hP.trans hker)
      rw [← comap_comp, ← comap_comp, Iso.inv_hom_id, comap_id] at htargetBoundary
      exact htargetBoundary
    · exact congrArg Scheme.Hom.toRationalMap hg.symm

end TauCeti.Toric.Fan.LogarithmicProjection

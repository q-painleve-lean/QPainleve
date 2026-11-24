/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.ResolvedMutation
public import QPainleve.Geometry.Toric.Fan.Mutation.ResolvedEvaluation
public import TauCeti.Algebra.Group.FreeAbelianCharacter

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic

/-!
# Cluster words of resolved logarithmic mutations

A resolved mutation of a specified logarithmic projection determines a two-letter word in
the labels of the actual ordered blowup towers. Its evaluation and Picard pullback use the
same identification of the resolving surface. The two letters are the elementary mutation
of Gross, Hacking and Keel (https://arxiv.org/html/1309.2573v2#S3.SS1) and the relabeling
that puts the reverse pivot first.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative PointedCone
open QPainleve.BlowupTower QPainleve.Cluster TauCeti TauCeti.AlgebraicGeometry
open LineBundleClass

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "base[" T "]" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd T))
local notation "χ[" u "]" => MonoidHom.comp (freeAbelianCharEquiv.symm u)
  (MulEquiv.toMonoidHom (AddEquiv.toMultiplicative (LinearEquiv.toAddEquiv
    (LinearEquiv.symm (Finsupp.linearEquivFunOnFinite ℤ ℤ _)))))
local notation "E[" b "," a "]" => chargeExchangeMatrix
  (LinearEquiv.toLinearMap (Module.Basis.detDualEquiv b)) (rayChargeMap a)
local notation "B[" b "," a "]" => SkewExchangeMatrix.ofMatrix E[b,a]
  (isSkewSymmetrizer_chargeExchangeMatrix _ (Module.Basis.detDualEquiv_self b) _)
local notation "σ[" k "]" => Equiv.trans (finSuccEquiv _) (Equiv.symm (finSuccEquiv' k))
local notation "w[" B "," k "]" => Quiver.Path.comp
  (Quiver.Hom.toPath (Generator.toStep (Generator.mutate k) B))
  (Quiver.Hom.toPath (Generator.toStep (Generator.permute σ[k]) _))
local notation "rays[" Ω "," b "," τ "," opp "," a "," k "]" => Fin.cons
  (α := fun _ ↦ Fan.Ray (Fan.mutationFan Ω b (Ray.primitiveGenerator_ne_zero τ)
    (Ray.hull_primitiveGenerator_mem τ) opp))
  (Fan.mutationFanCenterRays Ω b (fun _ : Unit ↦ τ) () opp ())
  (fun l ↦ Fan.mutationFanRayEquiv Ω b (Ray.primitiveGenerator_ne_zero τ)
    (Ray.hull_primitiveGenerator_mem τ) opp (a (Fin.succAbove k l)))
local notation "params[" b "," τ "," c "," a "," u "," k "]" => Fin.cons (α := fun _ ↦ ℂˣ) c⁻¹
  (fun l ↦ u (Fin.succAbove k l) * c ^ max (Module.Basis.det b
    ![Ray.primitiveGenerator (a (Fin.succAbove k l)), Ray.primitiveGenerator τ]) 0)

variable {Z : Scheme} [IsIntegral Z]

local notation "M[" Δ "," b "," r "," h "]" =>
  Fan.mutationFan Δ b (Ray.primitiveGenerator_ne_zero r) (Ray.hull_primitiveGenerator_mem r) h

private theorem compare_ordered_mutation {Ω : Fan i} [Nonempty Ω.cones]
    (b : Module.Basis (Fin 2) ℤ N)
    {n : ℕ} (a : Fin (n + 1) → Ω.Ray) (u : Fin (n + 1) → ℂˣ) (k : Fin (n + 1))
    (τ : Ω.Ray) (opp : hull ℝ {i (-τ.primitiveGenerator)} ∈ Ω.cones) (t : ℂˣ)
    (hk : τ = a k) (ht : t = u k)
    (f : Z ⟶ X[Ω]) [IsDominant f] (g : Z ⟶ X[M[Ω,b,τ,opp]])
    (hr : f.toRationalMap.comp
      (Ω.mutationPartialMap b (t : ℂ) τ.primitiveGenerator_ne_zero
        τ.hull_primitiveGenerator_mem opp).toRationalMap = g.toRationalMap) :
    letI : Nonempty (M[Ω,b,τ,opp]).cones := ⟨(rays[Ω,b,τ,opp,a,k] 0).toCone⟩
    letI : g.toRationalMap.IsDominant := hr ▸ inferInstance
    let B := B[b,a]
    let w := w[B,k]
    let c₀ := χ[u]
    let c₁ := c₀.comp w.exponentEquiv.toAddEquiv.toAddMonoidHom.toMultiplicative
    let a₁ := rays[Ω,b,τ,opp,a,k]
    let u₁ := params[b,τ,t,a,u,k]
    B[b,a₁] = (Generator.permute σ[k]).target ((Generator.mutate k).target B) ∧
    c₁ = χ[u₁] ∧
    let ev := f.toRationalMap.comp (Ω.xEvaluation b a c₀)
    ∃ hdom : ev.fromFunctionField (IsLocalRing.closedPoint Z.functionField) ∈
        (w.xRationalMap ℂ).domain,
      ev.compOfDefined (w.xRationalMap ℂ) hdom =
        g.toRationalMap.comp ((M[Ω,b,τ,opp]).xEvaluation b a₁ χ[u₁]) := by
  -- Substitution transports the mutated fan and the target projection together.
  subst τ t
  have hparam (v : Fin (n + 1) → ℂˣ) (j : Fin (n + 1)) :
      (χ[v]) (ofAdd (Pi.single j 1)) = v j := by
    simp [Finsupp.linearEquivFunOnFinite_symm_single]
  have hr' : f.toRationalMap.comp
      (Ω.mutationPartialMap b ((χ[u]) (ofAdd (Pi.single k 1)) : ℂ)
        (a k).primitiveGenerator_ne_zero (a k).hull_primitiveGenerator_mem opp).toRationalMap =
      g.toRationalMap := by
    simpa only [hparam] using hr
  obtain ⟨hmat, hcenters, hdom, hEval⟩ :=
    Ω.comp_xEvaluation_of_resolved_mutation_pivot_first b a k (χ[u])
      opp f g hr' B[b,a] (SkewExchangeMatrix.matrix_ofMatrix _ _).symm
  intro B w c₀ c₁ a₁ u₁
  have hc₁ : c₁ = χ[u₁] := by
    let e := (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin (n + 1))).toAddEquiv.toMultiplicative
    apply (MonoidHom.cancel_right (f := e.toMonoidHom) e.surjective).mp
    apply MonoidHom.ext_finsupp_mint
    intro j
    have he : e (ofAdd (Finsupp.single j 1)) = ofAdd (Pi.single j 1) := by
      simp [e, Finsupp.linearEquivFunOnFinite_single]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he, hparam]
    simpa only [hparam] using hcenters j
  refine ⟨SkewExchangeMatrix.ext ((SkewExchangeMatrix.matrix_ofMatrix _ _).trans hmat), hc₁,
    hdom, ?_⟩
  simpa only [← hc₁] using hEval

variable [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)] {P : Z.IdealSheafData}
  (A : LogarithmicProjection i P) (b : Module.Basis (Fin 2) ℤ N) (ρ : A.fan.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ A.fan.cones) (c : ℂˣ)

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

/-- A specified resolved mutation gives an ordered target model and the independent X word
in its labels. On the resolving surface the word is generically defined on the source
evaluation and gives the target evaluation. Its exponent action gives the target center
parameters, and the isomorphism used for that evaluation also computes the full Picard
pullback in the ordered markings. The first occurrence of the pivot determines the mutation
label even when centers are repeated. -/
theorem exists_word_of_resolved_mutation
    {Ω : Fan i} (hΩ : Ω.IsRegular) (H : Ω.IsSubdivision A.fan)
    {m : ℕ} (a : Fin m → Ω.Ray) (u : Fin m → ℂˣ)
    (r : Z ⟶ X[M[A.fan,b,ρ,hOpp]])
    (hr : A.hom.toRationalMap.comp μ[A.fan,ρ,hOpp] = r.toRationalMap) :
    letI : Nonempty Ω.cones := H.nonempty_cones_of_nonempty A.isComplete.nonempty_cones
    let U := Ω.internalBlowupTower b a u
    ∀ (e : U.1 ≅ Z), e.hom ≫ A.hom = base[U] ≫ π[H] →
      P.comap e.hom = U.2.boundaryι.ker →
      let σ := liftRay(H)
      let opp := oppositeRayMem(H)
      let Ψ := M[Ω,b,σ,opp]
      letI : Nonempty Ψ.cones := ⟨Ω.mutationFanConeEquiv b σ.primitiveGenerator_ne_zero
        σ.hull_primitiveGenerator_mem opp σ.toCone⟩
      letI : IsIntegral U.1 := isIntegral_internalBlowupTower b a u hΩ
      letI : IsModification base[U] := isModification_internalBlowupTower_toBase b a u hΩ
      ∃ (n : ℕ) (hm : n + 1 = m) (k : Fin (n + 1)),
        let ι := finCongr hm
        let a₀ := a ∘ ι
        let c₀ := χ[u ∘ ι]
        a₀ k = σ ∧ u (ι k) = c ∧ (∀ l < k, (a₀ l, u (ι l)) ≠ (σ, c)) ∧
        let a₁ := rays[Ω,b,σ,opp,a₀,k]
        let u₁ := params[b,σ,c,a₀,u ∘ ι,k]
        let W := Ψ.internalBlowupTower b a₁ u₁
        letI : IsDominant base[W] := (isModification_internalBlowupTower_toBase b a₁ u₁
          ((Ω.isRegular_mutationFan_iff b σ.primitiveGenerator_ne_zero
            σ.hull_primitiveGenerator_mem opp).mpr hΩ)).isDominant
        let B := B[b,a₀]
        let w := w[B,k]
        let c₁ := c₀.comp w.exponentEquiv.toAddEquiv.toAddMonoidHom.toMultiplicative
        ∃ g : U.1 ≅ W.1,
          g.inv ≫ e.hom ≫ r = base[W] ≫ π[mutationSubdivision(H)] ∧
          P.comap (g.inv ≫ e.hom) = W.2.boundaryι.ker ∧
          (base[U]).toRationalMap.comp μ[Ω,σ,opp] = (g.hom ≫ base[W]).toRationalMap ∧
          U.2.boundaryι ≫ g.hom = (σ.mutationBoundaryIso b opp c hΩ).hom ≫ W.2.boundaryι ∧
          (∀ d z x,
            let y := mutationPicardEquiv b (fun _ : Fin 1 ↦ σ) 0 opp hΩ (d, fun _ ↦ z)
            pullback g.hom (W.2.toTower.picardHom (d, Fin.cons z x)).toMul =
              (U.2.toTower.picardHom (y.1, k.insertNth (y.2 0) x ∘ ι.symm)).toMul) ∧
          B[b,a₁] = (Generator.permute σ[k]).target ((Generator.mutate k).target B) ∧
          c₁ = χ[u₁] ∧
          let ev := (e.inv ≫ base[U]).toRationalMap.comp (Ω.xEvaluation b a₀ c₀)
          ∃ hdom : ev.fromFunctionField (IsLocalRing.closedPoint Z.functionField) ∈
              (w.xRationalMap ℂ).domain,
            ev.compOfDefined (w.xRationalMap ℂ) hdom =
              (e.inv ≫ g.hom ≫ base[W]).toRationalMap.comp (Ψ.xEvaluation b a₁ χ[u₁]) := by
  let : Nonempty Ω.cones := H.nonempty_cones_of_nonempty A.isComplete.nonempty_cones
  intro U e he hP σ opp Ψ
  let : Nonempty Ψ.cones := ⟨Ω.mutationFanConeEquiv b σ.primitiveGenerator_ne_zero
    σ.hull_primitiveGenerator_mem opp σ.toCone⟩
  let : IsIntegral U.1 := isIntegral_internalBlowupTower b a u hΩ
  let : IsModification base[U] := isModification_internalBlowupTower_toBase b a u hΩ
  obtain ⟨n, hm, k, hk, hc, hfirst, g, hg, hPole, hrat, hboundary, hPicard⟩ :=
    A.exists_ordered_toric_mutation_model_of_factorization b ρ hOpp c hΩ H a u r hr e he hP
  refine ⟨n, hm, k, hk, hc, hfirst, g, hg, hPole, hrat, hboundary, hPicard, ?_⟩
  let ι := finCongr hm
  let a₀ := a ∘ ι
  let a₁ := rays[Ω,b,σ,opp,a₀,k]
  let u₁ := params[b,σ,c,a₀,u ∘ ι,k]
  let W := Ψ.internalBlowupTower b a₁ u₁
  have hrat' : (e.inv ≫ base[U]).toRationalMap.comp μ[Ω,σ,opp] =
      (e.inv ≫ g.hom ≫ base[W]).toRationalMap := by
    calc
      _ = (e.inv.toRationalMap.comp (base[U]).toRationalMap).comp μ[Ω,σ,opp] := by
        simp only [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
      _ = _ := by
        rw [Scheme.RationalMap.comp_assoc, hrat, Scheme.RationalMap.comp_toRationalMap,
          Scheme.Hom.toRationalMap_compHom]
        rfl
  exact compare_ordered_mutation b a₀ (u ∘ ι) k σ opp c hk.symm hc.symm _ _ hrat'

end TauCeti.Toric.Fan.LogarithmicProjection

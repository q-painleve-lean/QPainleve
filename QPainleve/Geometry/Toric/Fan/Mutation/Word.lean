/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Word
public import QPainleve.Algebra.Cluster.Word.RationalMap
public import QPainleve.Geometry.Toric.Fan.Boundary.Valuation
public import QPainleve.Geometry.Toric.Fan.Evaluation
public import QPainleve.Geometry.Toric.Fan.Mutation.Valuation

import QPainleve.Algebra.Cluster.Word.Chart
import QPainleve.AlgebraicGeometry.RationalMap.Restriction
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.Fan.Mutation.Charge
import QPainleve.Geometry.Toric.Fan.Mutation.Evaluation
import QPainleve.Geometry.Toric.Fan.StarSubdivision.RayInsertion
import QPainleve.Geometry.Toric.Fan.Subdivision.FunctionField

/-!
# Boundary orders along toric mutation words

Insert the opposite pivot ray by a regular subdivision before each elementary transformation.
The original rays survive subdivision, and the subsequent mutation sends them by its integral
shear. Inversion retains the rays and reverses the oriented basis. A signed word thus transports
the original boundary rays into a terminal fan, where the orders of the terminal charge characters
at these rays are the entries of the tropical word.
At fixed centers, the word is defined at the generic point of the evaluated surface.
The same function-field pullback compares the independent X rational map with the
terminal evaluation.

The boundary calculation for an elementary transformation follows Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
The signed inversion is from Bershtein, Gavrylenko and Marshakov,
[*Cluster integrable systems, q-Painlevé equations and their quantization*, §3.1]
(https://arxiv.org/abs/1711.02063).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module Multiplicative PointedCone Quiver
open QPainleve.Cluster TauCeti.LaurentRing

namespace TauCeti.Toric.Fan

variable {N V ι : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Fintype ι] [DecidableEq ι]
  (b : Basis (Fin 2) ℤ N)

local notation "d" => b.detDualEquiv
local notation "trop" => Paths.lift (tropicalPrefunctor (A := ℤ) ι)

local notation "K(" Φ ")" => Scheme.functionField (Fan.algebraicRealization Φ)
local notation "χ" => Multiplicative (ι → ℤ) →* ℂˣ
local notation "swapBasis" a:arg => Basis.reindex a (Equiv.swap 0 1)

local notation "center(" c "," w ")" =>
  MonoidHom.comp c (AddMonoidHom.toMultiplicative
    (AddEquiv.toAddMonoidHom (LinearEquiv.toAddEquiv (Path.exponentEquiv w))))
local notation "fieldPoint(" Φ "," Ψ "," q ")" =>
  Spec.map (ConcreteCategory.ofHom (X := K(Ψ)) (Y := K(Φ))
    (RingEquiv.toRingHom (AlgEquiv.toRingEquiv q)))
local notation "eval(" Φ "," a "," s "," c ")" =>
  Scheme.RationalMap.fromFunctionField (Fan.xEvaluation Φ a s c)

private theorem fieldPoint_refl (Φ : Fan i) [Nonempty Φ.cones] :
    fieldPoint(Φ,Φ,(AlgEquiv.refl : K(Φ) ≃ₐ[ℂ] K(Φ))) = 𝟙 (Spec K(Φ)) :=
  Spec.map_id _

private theorem exists_lift_xRationalMap_mutate_of_subdivision {Ω : Fan i} [Nonempty Φ.cones]
    (h : Ω.IsSubdivision Φ) {B : SkewExchangeMatrix ι} (s : ι → Φ.Ray) (p : ι)
    (c : χ) (hop : hull ℝ {i (-(h.liftRay (s p)).primitiveGenerator)} ∈ Ω.cones)
    (hB : B.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s)) :
    let t := h.liftRay ∘ s
    let hv := (t p).isPrimitiveGenerator.ne_zero
    let hp := (t p).hull_primitiveGenerator_mem
    let Ψ := Ω.mutationFan b hv hp hop
    let t' := Ω.mutationFanCenterRays b t p hop
    letI : Nonempty Ω.cones := ⟨(t p).toCone⟩
    letI : Nonempty Ψ.cones := ⟨(t' p).toCone⟩
    let q₀ := Ω.mutationComplementPullbackAlgHom b (c (ofAdd (Pi.single p 1)) : ℂ) hv hp hop
    let w := ((Generator.mutate p).toStep B).toPath
    let f := w.xRationalMap ℂ
    ∀ q : K(Ψ) ≃ₐ[ℂ] K(Φ),
      (∀ a, h.toFanHom.algebraicMap.functionFieldMap (q a) = q₀ a) →
      ∃ l : Spec K(Φ) ⟶ f.toPartialMap.domain,
        l ≫ f.toPartialMap.domain.ι = eval(Φ,b,s,c) ∧
        l ≫ f.toPartialMap.hom = fieldPoint(Φ,Ψ,q) ≫ eval(Ψ,b,t',center(c,w)) := by
  intro t hv hp Ψ t' q₀ w f q hq
  let : Nonempty Ω.cones := ⟨(t p).toCone⟩
  let : Nonempty Ψ.cones := ⟨(t' p).toCone⟩
  have hmat : B.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap t) := by
    simpa only [t, h.rayChargeMap_liftRay] using hB
  have hc : center(c,w) = c.comp (chargeMutationEquiv
      (chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap t)) p
      ).toAddEquiv.toAddMonoidHom.toMultiplicative := by
    simp only [w, Path.exponentEquiv_toPath, Step.exponentEquiv_mutate, hmat]
  obtain ⟨l, hl, hl'⟩ := Ω.exists_lift_xRationalMap_mutate b t p c hop B
    (fun j ↦ congrArg (fun M : Matrix ι ι ℤ ↦ M j p) hmat)
  let u := Spec.map h.toFanHom.algebraicMap.functionFieldMap
  have : IsIso u := inferInstanceAs (IsIso (Spec.map h.toFanHom.algebraicMap.functionFieldMap))
  have hsource : u ≫ eval(Φ,b,s,c) = eval(Ω,b,t,c) := by
    have he := congrArg Scheme.RationalMap.fromFunctionField (h.comp_xEvaluation b s c)
    rw [Scheme.RationalMap.fromFunctionField_comp, Scheme.Hom.functionFieldMap_toRationalMap] at he
    exact he
  have htarget : u ≫ fieldPoint(Φ,Ψ,q) = Spec.map (CommRingCat.ofHom q₀.toRingHom) := by
    dsimp only [u]
    rw [← Spec.map_comp, Spec.map_inj]
    exact CommRingCat.hom_ext (RingHom.ext hq)
  refine ⟨inv u ≫ l, ?_, ?_⟩
  · rw [Category.assoc, hl, ← hsource, IsIso.inv_hom_id_assoc]
  · rw [Category.assoc, hl', hc, ← htarget, Category.assoc, IsIso.inv_hom_id_assoc]

private theorem ord_mutation_of_subdivision {Ω : Fan i} (h : Ω.IsSubdivision Φ)
    (hΦ : Φ.IsRegular) (hΩ : Ω.IsRegular) [Nonempty Φ.cones] (pivot : Ω.Ray)
    (hopp : hull ℝ {i (-pivot.primitiveGenerator)} ∈ Ω.cones) (c : ℂˣ) :
    let hv := pivot.isPrimitiveGenerator.ne_zero
    let hpos := pivot.hull_primitiveGenerator_mem
    let Ψ := Ω.mutationFan b hv hpos hopp
    let hΨ := (Ω.isRegular_mutationFan_iff b hv hpos hopp).2 hΩ
    letI : Nonempty Ω.cones := ⟨pivot.toCone⟩
    letI : Nonempty Ψ.cones := ⟨((Ω.mutationFanRayEquiv b hv hpos hopp) pivot).toCone⟩
    ∃ q : K(Ψ) ≃ₐ[ℂ] K(Φ),
      (∀ a, h.toFanHom.algebraicMap.functionFieldMap (q a) =
        Ω.mutationComplementPullback b (c : ℂ) hv hpos hopp a) ∧
      ∀ (ρ : Φ.Ray) (a : K(Ψ)),
      Φ.algebraicRealization.ord (q a) (Φ.rayBoundaryPoint hΦ ρ).val =
        Ψ.algebraicRealization.ord a
          (Ψ.rayBoundaryPoint hΨ (Ω.mutationFanRayEquiv b hv hpos hopp (h.liftRay ρ))).val := by
  dsimp only
  let hv := pivot.isPrimitiveGenerator.ne_zero
  let hpos := pivot.hull_primitiveGenerator_mem
  have : Nonempty Ω.cones := ⟨pivot.toCone⟩
  have : Nonempty (Ω.mutationFan b hv hpos hopp).cones :=
    ⟨((Ω.mutationFanRayEquiv b hv hpos hopp) pivot).toCone⟩
  have := Ω.isIso_mutationComplementPullback b (c : ℂ) hv hpos hopp
  let m := Ω.mutationComplementPullback b (c : ℂ) hv hpos hopp
  let sub := h.toFanHom.algebraicMap
  let e := asIso m ≪≫ (asIso sub.functionFieldMap).symm
  have he (a : K(Ω.mutationFan b hv hpos hopp)) :
      sub.functionFieldMap (e.hom a) = m a := by
    simp [e]
  let q : K(Ω.mutationFan b hv hpos hopp) ≃ₐ[ℂ] K(Φ) :=
    AlgEquiv.ofRingEquiv (f := e.commRingCatIsoToRingEquiv) fun z ↦
      sub.functionFieldMap.hom.injective <| by
        calc
          sub.functionFieldMap (e.hom (algebraMap ℂ _ z)) =
              m (algebraMap ℂ _ z) := he _
          _ = algebraMap ℂ K(Ω) z :=
            Ω.mutationComplementPullback_algebraMap b (c : ℂ) hv hpos hopp z
          _ = sub.functionFieldMap (algebraMap ℂ _ z) :=
            (sub.functionFieldMap_algebraMap ℂ z).symm
  refine ⟨q, he, fun ρ a ↦ ?_⟩
  have hs : sub.functionFieldMap (q a) = m a := he _
  rw [← h.ord_functionFieldMap_liftRay hΩ hΦ, hs]
  exact Ω.ord_mutationComplementPullback_rayBoundaryPoint b c hv hpos hopp hΩ (h.liftRay ρ) a

private theorem exists_toric_boundary_valuation_transport_mutate {B : SkewExchangeMatrix ι}
    (P : ChargeSeed B N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (s : ι → Φ.Ray)
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = rayChargeMap s) (p : ι) :
    ∃ (Ψ : Fan i) (hΨ : Ψ.IsRegular) (hΨc : Ψ.IsComplete) (t : ι → Ψ.Ray) (f : Φ.Ray ↪ Ψ.Ray),
      (Step.chargeTarget ((Generator.mutate p).toStep B) P).charge = rayChargeMap t ∧
      (∀ ρ, rayBoundaryOrders b t (f ρ) =
        (Generator.mutate p).tropical B (rayBoundaryOrders b s ρ)) ∧
      letI : Nonempty Φ.cones := hc.nonempty_cones
      letI : Nonempty Ψ.cones := hΨc.nonempty_cones
      ∃ q : χ → (K(Ψ) ≃ₐ[ℂ] K(Φ)),
        (∀ (c : χ) (ρ : Φ.Ray) (a : K(Ψ)),
          Φ.algebraicRealization.ord (q c a) (Φ.rayBoundaryPoint hΦ ρ).val =
            Ψ.algebraicRealization.ord a (Ψ.rayBoundaryPoint hΨ (f ρ)).val) ∧
        ∀ c : χ, let F := ((Generator.mutate p).toStep B).toPath.xRationalMap ℂ
          ∃ l : Spec K(Φ) ⟶ F.toPartialMap.domain,
            l ≫ F.toPartialMap.domain.ι = eval(Φ,b,s,c) ∧
            l ≫ F.toPartialMap.hom = fieldPoint(Φ,Ψ,q c) ≫
              eval(Ψ,b,t,center(c,((Generator.mutate p).toStep B).toPath)) := by
  have hrank : finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  obtain ⟨Ω, hΩ, hreg, hcomp, hopp₀⟩ :=
    (s p).exists_regular_subdivision_containing_opposite hΦ hc hrank
  let s₀ := hΩ.liftRay ∘ s
  let h₀ := (s₀ p).isPrimitiveGenerator.ne_zero
  let h₁ := (s₀ p).hull_primitiveGenerator_mem
  let Ψ := Ω.mutationFan b h₀ h₁ hopp₀
  let t := Ω.mutationFanCenterRays b s₀ p hopp₀
  let g : Φ.Ray ↪ Ω.Ray := ⟨hΩ.liftRay, fun ρ τ h ↦
    Ray.primitiveGenerator_injective (by
      simpa only [hΩ.primitiveGenerator_liftRay] using congrArg Ray.primitiveGenerator h)⟩
  let f := g.trans (Ω.mutationFanRayEquiv b h₀ h₁ hopp₀).toEmbedding
  have hf (ρ : Φ.Ray) : f ρ = Ω.mutationFanRayEquiv b h₀ h₁ hopp₀ (hΩ.liftRay ρ) :=
    rfl
  have hB : ∀ j, B.matrix j p = d (s₀ j).primitiveGenerator (s₀ p).primitiveGenerator := by
    intro j
    rw [← P.matrix_eq, chargeExchangeMatrix_apply, hform, hcharge]
    simp [s₀, Basis.detDualEquiv_apply]
  refine ⟨Ψ, (Ω.isRegular_mutationFan_iff b h₀ h₁ hopp₀).2 hreg,
    (Ω.isComplete_mutationFan_iff b h₀ h₁ hopp₀).2 hcomp, t, f, ?_, ?_, ?_⟩
  · rw [Step.chargeTarget_mutate_charge, hform, hcharge,
      ← hΩ.rayChargeMap_liftRay s, ← rayChargeMap_mutationFanCenterRays b s₀ p hopp₀]
  · intro ρ
    have h := Ω.tropical_mutate_eq_rayPairing_mutationFanRayEquiv b s₀ p hopp₀ B hB (hΩ.liftRay ρ)
    have ho : (fun j ↦ d (s₀ j).primitiveGenerator (hΩ.liftRay ρ).primitiveGenerator) =
        rayBoundaryOrders b s ρ := by
      funext j
      simp [s₀, Basis.detDualEquiv_apply]
    rw [ho] at h
    funext j
    simpa only [rayBoundaryOrders_apply, Basis.detDualEquiv_apply, t, hf] using congrFun h.symm j
  · have := hc.nonempty_cones
    have h (c : χ) := ord_mutation_of_subdivision b hΩ hΦ hreg (s₀ p) hopp₀
      (c (ofAdd (Pi.single p 1)))
    choose q hq hval using h
    refine ⟨q, fun c ρ a ↦ by simpa only [hf, Ψ] using hval c ρ a, fun c ↦ ?_⟩
    have he : B.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s) := by
      rw [← P.matrix_eq, hform, hcharge]
    refine exists_lift_xRationalMap_mutate_of_subdivision b hΩ s p c hopp₀ he (q c) ?_
    intro a
    rw [mutationComplementPullbackAlgHom_apply]
    exact hq c a

private theorem exists_lift_xRationalMap_inversion [Nonempty Φ.cones] (B : SkewExchangeMatrix ι)
    (s : ι → Φ.Ray) (c : χ) :
    let w := (Generator.invert.toStep B).toPath
    let F := w.xRationalMap ℂ
    ∃ l : Spec K(Φ) ⟶ F.toPartialMap.domain,
      l ≫ F.toPartialMap.domain.ι = eval(Φ,b,s,c) ∧
      l ≫ F.toPartialMap.hom = eval(Φ,swapBasis b,s,center(c,w)) := by
  intro w F
  have hc : center(c,w) = c⁻¹ := by
    ext x
    simp [w, Path.exponentEquiv_toPath, Step.exponentEquiv_invert,
      AddMonoidHom.coe_toMultiplicative]
  dsimp only [F, w]
  rw [hc, Path.xRationalMap_invert, xEvaluation_reindex_swap,
    Scheme.RationalMap.fromFunctionField_compHom]
  let f := QPainleve.CharacterTorus.map ℂ (AddEquiv.neg (ι →₀ ℤ)).toAddMonoidHom
  exact f.exists_lift_toRationalMap (eval(Φ,b,s,c))

private theorem exists_lift_xRationalMap_permutation [Nonempty Φ.cones] (B : SkewExchangeMatrix ι)
    (s : ι → Φ.Ray) (σ : Equiv.Perm ι)
    (hsingle : ∀ j, LinearEquiv.funCongrLeft ℤ ℤ σ.symm (Pi.single j 1) = Pi.single (σ j) 1)
    (c : χ) :
    let w := ((Generator.permute σ).toStep B).toPath
    let F := w.xRationalMap ℂ
    ∃ l : Spec K(Φ) ⟶ F.toPartialMap.domain,
      l ≫ F.toPartialMap.domain.ι = eval(Φ,b,s,c) ∧
      l ≫ F.toPartialMap.hom = eval(Φ,b,s ∘ σ,center(c,w)) := by
  intro w F
  obtain ⟨l, hl, hl'⟩ := Quiver.Path.exists_lift_xRationalMap_permute ℂ B σ
  refine ⟨eval(Φ,b,s,c) ≫ l, by simp only [F, w, Category.assoc, hl, Category.comp_id], ?_⟩
  have heval : (Φ.xEval b s c).comp (rename σ) =
      Φ.xEval b (s ∘ σ) center(c,w) := by
    apply algHom_ext
    intro j
    simp only [AlgHom.comp_apply, rename_X, xEval_X, MonoidHom.comp_apply,
      AddMonoidHom.coe_toMultiplicative, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearEquiv.coe_toAddEquiv, w, Path.exponentEquiv_toPath, toAdd_ofAdd]
    -- The multiplicative synonym in the center character is transported by `ofAdd`.
    have hj : Step.exponentEquiv ((Generator.permute σ).toStep B) (Pi.single j 1) =
        Pi.single (σ j) 1 := by
      rw [Step.exponentEquiv_permute, hsingle]
    erw [hj]
    rfl
  dsimp only [F, w]
  rw [Category.assoc, hl', fromFunctionField_xEvaluation,
    fromFunctionField_xEvaluation, ← Spec.map_comp]
  exact congrArg (fun a ↦ Spec.map (CommRingCat.ofHom (AlgHom.toRingHom a))) heval

private theorem exists_toric_boundary_valuation_transport_step {B C : SkewExchangeMatrix ι}
    (e : B ⟶ C)
    (P : ChargeSeed B N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (s : ι → Φ.Ray)
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = rayChargeMap s) :
    let b' := if e.generator.inversionCount = 0 then b else swapBasis b
    ∃ (Ψ : Fan i) (hΨ : Ψ.IsRegular) (hΨc : Ψ.IsComplete) (t : ι → Ψ.Ray) (f : Φ.Ray ↪ Ψ.Ray),
      (Step.chargeTarget e P).form = b'.detDualEquiv.toLinearMap ∧
      (Step.chargeTarget e P).charge = rayChargeMap t ∧
      (∀ ρ, rayBoundaryOrders b' t (f ρ) = Step.tropical e (rayBoundaryOrders b s ρ)) ∧
      letI : Nonempty Φ.cones := hc.nonempty_cones
      letI : Nonempty Ψ.cones := hΨc.nonempty_cones
      ∃ q : χ → (K(Ψ) ≃ₐ[ℂ] K(Φ)),
        (∀ (c : χ) (ρ : Φ.Ray) (a : K(Ψ)),
          Φ.algebraicRealization.ord (q c a) (Φ.rayBoundaryPoint hΦ ρ).val =
            Ψ.algebraicRealization.ord a (Ψ.rayBoundaryPoint hΨ (f ρ)).val) ∧
        ∀ c : χ, let F := e.toPath.xRationalMap ℂ
          ∃ l : Spec K(Φ) ⟶ F.toPartialMap.domain,
            l ≫ F.toPartialMap.domain.ι = eval(Φ,b,s,c) ∧
            l ≫ F.toPartialMap.hom = fieldPoint(Φ,Ψ,q c) ≫ eval(Ψ,b',t,center(c,e.toPath)) := by
  obtain ⟨g, rfl⟩ := e
  have hg : g.toStep B = (⟨g, rfl⟩ : Step B (g.target B)) :=
    Step.ext (Generator.toStep_generator g B)
  rw [← hg]
  cases g with
  | invert =>
    let : Nonempty Φ.cones := hc.nonempty_cones
    simp only [Generator.toStep_generator, Generator.inversionCount_invert, Nat.one_ne_zero,
      ite_false]
    refine ⟨Φ, hΦ, hc, s, Function.Embedding.refl _, ?_, by simpa, ?_, ?_⟩
    · ext x
      simp [hform]
    · intro ρ
      rw [rayBoundaryOrders_reindex_swap]
      funext j
      simp [Step.tropical_apply]
    · refine ⟨fun _ ↦ AlgEquiv.refl, by simp, fun c ↦ ?_⟩
      simpa only [fieldPoint_refl, Category.id_comp] using
        exists_lift_xRationalMap_inversion b B s c
  | mutate p =>
    simp only [Generator.toStep_generator, Generator.inversionCount_mutate, ite_true]
    obtain ⟨Ψ, hreg, hcomp, t, f, hq, ho, hfield⟩ :=
      exists_toric_boundary_valuation_transport_mutate b P hΦ hc s hform hcharge p
    exact ⟨Ψ, hreg, hcomp, t, f, by simpa using hform, hq, by simpa using ho, hfield⟩
  | permute σ =>
    simp only [Generator.toStep_generator, Generator.inversionCount_permute, ite_true]
    let : Nonempty Φ.cones := hc.nonempty_cones
    have hsingle (j : ι) :
        LinearEquiv.funCongrLeft ℤ ℤ σ.symm (Pi.single j 1) = Pi.single (σ j) 1 := by
      ext a
      simp [LinearEquiv.funCongrLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]
    refine ⟨Φ, hΦ, hc, s ∘ σ, Function.Embedding.refl _, by simpa using hform, ?_, ?_, ?_⟩
    · rw [Step.chargeTarget_permute_charge, hcharge]
      apply (Pi.basisFun ℤ ι).ext
      intro j
      simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hsingle,
        rayChargeMap_single, Function.comp_apply]
    · intro ρ
      ext j
      simp [rayBoundaryOrders_apply]
    · refine ⟨fun _ ↦ AlgEquiv.refl, by simp, fun c ↦ ?_⟩
      simpa only [fieldPoint_refl, Category.id_comp] using
        exists_lift_xRationalMap_permutation b B s σ hsingle c

omit [Fintype ι] in
private theorem terminal_basis_cons {B C D : SkewExchangeMatrix ι} (w : Word B C) (e : C ⟶ D) :
    (if Even (w.cons e).inversionCount then b else swapBasis b) =
      let b' := if Even w.inversionCount then b else swapBasis b
      if e.generator.inversionCount = 0 then b' else swapBasis b' := by
  have hswap : swapBasis (swapBasis b) = b := by
    ext j
    simp [Basis.reindex_apply]
  obtain ⟨g, rfl⟩ := e
  cases g <;> by_cases hw : Even w.inversionCount <;>
    simp [Path.inversionCount_cons, hw, Nat.even_add_one, hswap]

/-- For a signed word from a complete regular surface fan, there is a complete regular
terminal fan realizing the transported charges. Its basis is reversed precisely for odd
inversion count. All initial rays map injectively to terminal rays, and the determinant orders
at each image are the tropical word applied to the corresponding initial orders.
For each center character, the pullbacks along
the subdivisions and mutations give an isomorphism on function fields preserving
orders at every transported ray. The generic point of the fixed-center X evaluation
lies in the domain of the independent word map, and its value equals the terminal
evaluation pulled back by that same function-field isomorphism. -/
theorem exists_toric_boundary_valuation_transport {B C : SkewExchangeMatrix ι}
    (w : Word B C) (P : ChargeSeed B N)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (s : ι → Φ.Ray)
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = rayChargeMap s) :
    let b' := if Even w.inversionCount then b else swapBasis b
    ∃ (Ψ : Fan i) (hΨ : Ψ.IsRegular) (hΨc : Ψ.IsComplete) (t : ι → Ψ.Ray) (f : Φ.Ray ↪ Ψ.Ray),
      (w.chargeTarget P).form = b'.detDualEquiv.toLinearMap ∧
      (w.chargeTarget P).charge = rayChargeMap t ∧
      (∀ ρ, rayBoundaryOrders b' t (f ρ) =
        DFunLike.coe (F := Equiv.Perm (ι → ℤ)) ((trop).map w) (rayBoundaryOrders b s ρ)) ∧
      letI : Nonempty Φ.cones := hc.nonempty_cones
      letI : Nonempty Ψ.cones := hΨc.nonempty_cones
      ∃ q : χ → (K(Ψ) ≃ₐ[ℂ] K(Φ)),
        (∀ (c : χ) (ρ : Φ.Ray) (a : K(Ψ)),
          Φ.algebraicRealization.ord (q c a) (Φ.rayBoundaryPoint hΦ ρ).val =
            Ψ.algebraicRealization.ord a (Ψ.rayBoundaryPoint hΨ (f ρ)).val) ∧
        ∀ c : χ, let F := w.xRationalMap ℂ
          ∃ l : Spec K(Φ) ⟶ F.toPartialMap.domain,
            l ≫ F.toPartialMap.domain.ι = eval(Φ,b,s,c) ∧
            l ≫ F.toPartialMap.hom = fieldPoint(Φ,Ψ,q c) ≫ eval(Ψ,b',t,center(c,w)) := by
  induction w with
  | nil =>
    let : Nonempty Φ.cones := hc.nonempty_cones
    have heven : Even (0 : ℕ) := ⟨0, rfl⟩
    simp only [Path.inversionCount_nil, heven, ite_true]
    refine ⟨Φ, hΦ, hc, s, Function.Embedding.refl _, ?_, ?_, ?_, ?_⟩
    · simpa using hform
    · simpa using hcharge
    · simp [Paths.lift_nil, SingleObj.id_as_one]
    · refine ⟨fun _ ↦ AlgEquiv.refl, by simp, fun c ↦ ?_⟩
      have he : center(c,(Path.nil : Word B B)) = c :=
        MonoidHom.ext fun a ↦ by simp [Path.exponentEquiv_nil, AddMonoidHom.coe_toMultiplicative]
      rw [Path.xRationalMap_nil, he, fieldPoint_refl, Category.id_comp]
      let T := QPainleve.CharacterTorus.scheme ℂ (ι →₀ ℤ)
      simpa only [Category.comp_id] using (𝟙 T : T ⟶ T).exists_lift_toRationalMap (eval(Φ,b,s,c))
  | cons w e ih =>
    dsimp only at ih ⊢
    rw [terminal_basis_cons b w e]
    let b₀ := if Even w.inversionCount then b else swapBasis b
    obtain ⟨Ω, hΩ, hΩc, t, f, hp, hq, ho, hfield⟩ := ih
    obtain ⟨Ψ, hΨ, hΨc, t', g, hp', hq', ho', hfield'⟩ :=
      exists_toric_boundary_valuation_transport_step b₀ e _ hΩ hΩc t hp hq
    refine ⟨Ψ, hΨ, hΨc, t', f.trans g, ?_, ?_, ?_, ?_⟩
    · simpa using hp'
    · simpa using hq'
    · intro ρ
      rw [Function.Embedding.trans_apply, ho', ho, tropical_map_cons_apply]
    · obtain ⟨q, hq, hqeval⟩ := hfield
      obtain ⟨r, hr, hreval⟩ := hfield'
      refine ⟨fun c ↦ (r center(c,w)).trans (q c), ?_, fun c ↦ ?_⟩
      · intro c ρ a
        rw [AlgEquiv.trans_apply, hq, hr, Function.Embedding.trans_apply]
      let : Nonempty Φ.cones := hc.nonempty_cones
      let : Nonempty Ω.cones := hΩc.nonempty_cones
      let : Nonempty Ψ.cones := hΨc.nonempty_cones
      obtain ⟨l, hl, hl'⟩ := hqeval c
      obtain ⟨m, hm, hm'⟩ := hreval center(c,w)
      have hmatch : l ≫ (w.xRationalMap ℂ).toPartialMap.hom =
          (fieldPoint(Φ,Ω,q c) ≫ m) ≫ (e.toPath.xRationalMap ℂ).toPartialMap.domain.ι := by
        rw [Category.assoc, hm, hl']
      obtain ⟨a, ha, ha'⟩ := (w.xRationalMap ℂ).exists_lift_comp
        (e.toPath.xRationalMap ℂ) l (fieldPoint(Φ,Ω,q c) ≫ m) hmatch
      have hx : (w.cons e).xRationalMap ℂ =
          (w.xRationalMap ℂ).comp (e.toPath.xRationalMap ℂ) := by
        rw [← Path.comp_toPath_eq_cons, Path.xRationalMap_comp]
      have hc : center(center(c,w),e.toPath) = center(c,w.cons e) := by
        ext x
        simp [Path.exponentEquiv_toPath, Path.exponentEquiv_cons]
      refine hx ▸ ⟨a, ha.trans hl, ?_⟩
      rw [ha', Category.assoc, hm', hc, ← Category.assoc, ← Spec.map_comp]
      rfl

end TauCeti.Toric.Fan

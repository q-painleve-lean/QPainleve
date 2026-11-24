/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Exponent
public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Defined
public import QPainleve.Geometry.Toric.Fan.Mutation.Evaluation

import QPainleve.Algebra.Cluster.Word.Chart
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.Mutation.Charge

/-!
# X evaluation along resolved toric mutations

Two morphisms to the toric models of an elementary transformation give the cluster
X mutation on their fixed-center evaluations when their rational comparison is the
specified toric mutation. This applies to the regular projections of an ordered
internal blowup model, including models with infinitely near centers.

The comparison pulls back `Fan.exists_lift_xRationalMap_mutate` to the function
field of the resolving surface and uses `FanHom.comp_xEvaluation` for the change
of labels. The elementary transformation is that of
[Gross, Hacking and Keel, §3.1][GHK].

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative PointedCone
open QPainleve.Cluster TauCeti.AlgebraicGeometry TauCeti.LaurentRing

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (b : Module.Basis (Fin 2) ℤ N) {ι : Type} [Fintype ι] [DecidableEq ι]
  (s : ι → Φ.Ray) (p : ι) (c : Multiplicative (ι → ℤ) →* ℂˣ)
  (hOpp : hull ℝ {i (-(s p).primitiveGenerator)} ∈ Φ.cones)

local notation "hv" => Ray.primitiveGenerator_ne_zero (s p)
local notation "hp" => Ray.hull_primitiveGenerator_mem (s p)
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "t" => Φ.mutationFanCenterRays b s p hOpp
local notation "ε" => chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s)
local notation "cₚ" => c (ofAdd (Pi.single p 1))
local notation "c′" => MonoidHom.comp c (AddMonoidHom.toMultiplicative
  (AddEquiv.toAddMonoidHom (LinearEquiv.toAddEquiv (chargeMutationEquiv ε p))))
local notation "μ" => Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap b (cₚ : ℂ) hv hp hOpp)

variable (Φ) in
/-- On a common resolution of a specified toric mutation, the source fixed-center
evaluation is generically in the domain of the independent X mutation. Composing
there gives the pullback of the mutated fixed-center evaluation along the specified
target projection. -/
theorem comp_xEvaluation_of_resolved_mutation {Z : Scheme} [IsIntegral Z]
    (f : Z ⟶ Φ.algebraicRealization) [IsDominant f] (g : Z ⟶ (Ψ).algebraicRealization)
    (h : letI : Nonempty Φ.cones := ⟨(s p).toCone⟩
         f.toRationalMap.comp μ = g.toRationalMap)
    (B : SkewExchangeMatrix ι) (hB : ∀ j, B.matrix j p = ε j p) :
    letI : Nonempty Φ.cones := ⟨(s p).toCone⟩
    letI : Nonempty (Ψ).cones := ⟨(t p).toCone⟩
    letI : g.toRationalMap.IsDominant := h ▸ inferInstance
    let w : QPainleve.CharacterTorus.scheme ℂ (ι →₀ ℤ) ⤏
        QPainleve.CharacterTorus.scheme ℂ (ι →₀ ℤ) :=
      ((Generator.mutate p).toStep B).toPath.xRationalMap ℂ
    let ev : Z ⤏ QPainleve.CharacterTorus.scheme ℂ (ι →₀ ℤ) :=
      f.toRationalMap.comp (Φ.xEvaluation b s c)
    ∃ hdom : ev.fromFunctionField (IsLocalRing.closedPoint Z.functionField) ∈ w.domain,
      ev.compOfDefined w hdom = g.toRationalMap.comp ((Ψ).xEvaluation b t c′) := by
  let : Nonempty Φ.cones := ⟨(s p).toCone⟩
  let : Nonempty (Ψ).cones := ⟨(t p).toCone⟩
  intro w ev
  obtain ⟨l, hl, hl'⟩ := Φ.exists_lift_xRationalMap_mutate b s p c hOpp B hB
  let k := Spec.map f.toRationalMap.functionFieldMap
  let a := k ≫ l
  have ha : a ≫ w.toPartialMap.domain.ι = ev.fromFunctionField := by
    rw [Scheme.RationalMap.fromFunctionField_comp, Category.assoc, hl]
  have hdom : ev.fromFunctionField (IsLocalRing.closedPoint Z.functionField) ∈ w.domain := by
    let x : Spec Z.functionField := IsLocalRing.closedPoint _
    rw [← w.toPartialMap_domain, ← congrArg (fun m : Spec Z.functionField ⟶ _ ↦ m x) ha]
    exact (a x).property
  refine ⟨hdom, Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
  have : g.toRationalMap.IsDominant := h ▸ inferInstance
  have hfield := (Scheme.RationalMap.functionFieldMap_eq_iff _ _).mpr h
  rw [Scheme.RationalMap.functionFieldMap_comp, functionFieldMap_mutationPartialMap_toRationalMap]
    at hfield
  rw [Scheme.RationalMap.fromFunctionField_compOfDefined _ _ hdom a ha, Category.assoc, hl',
    Scheme.RationalMap.fromFunctionField_comp, ← hfield, Spec.map_comp_assoc]
  have hμ : CommRingCat.ofHom
      (Φ.mutationComplementPullbackAlgHom b (cₚ : ℂ) hv hp hOpp).toRingHom =
      Φ.mutationComplementPullback b (cₚ : ℂ) hv hp hOpp := by
    apply CommRingCat.hom_ext
    ext z
    exact Φ.mutationComplementPullbackAlgHom_apply b (cₚ : ℂ) hv hp hOpp z
  simp only [k, hμ]

section Ordered

variable {n : ℕ} (r : Fin (n + 1) → Φ.Ray) (k : Fin (n + 1))
  (a : Multiplicative (Fin (n + 1) → ℤ) →* ℂˣ)
  (opp : hull ℝ {i (-(r k).primitiveGenerator)} ∈ Φ.cones)

local notation "v" => Ray.primitiveGenerator (r k)
local notation "h₀" => Ray.primitiveGenerator_ne_zero (r k)
local notation "h₁" => Ray.hull_primitiveGenerator_mem (r k)
local notation "Ω" => Φ.mutationFan b h₀ h₁ opp
local notation "r′" => Φ.mutationFanCenterRays b r k opp
local notation "aₖ" => a (ofAdd (Pi.single k 1))
local notation "E" => chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap r)
local notation "a′" => MonoidHom.comp a (AddMonoidHom.toMultiplicative
  (AddEquiv.toAddMonoidHom (LinearEquiv.toAddEquiv (chargeMutationEquiv E k))))
local notation "σ" => Equiv.trans (finSuccEquiv n) (Equiv.symm (finSuccEquiv' k))
local notation "reorder" => LinearEquiv.funCongrLeft ℤ ℤ (Equiv.symm σ)
local notation "d" => MonoidHom.comp a′ (AddMonoidHom.toMultiplicative
  (AddEquiv.toAddMonoidHom (LinearEquiv.toAddEquiv reorder)))
local notation "reverseRay" => Φ.mutationFanCenterRays b (fun _ : Unit ↦ r k) () opp ()
local notation "tailRay" => fun j : Fin n ↦
  Φ.mutationFanRayEquiv b h₀ h₁ opp (r (k.succAbove j))
local notation "tailParam" => fun j : Fin n ↦ a (ofAdd (Pi.single (k.succAbove j) 1)) *
  aₖ ^ max (b.det ![Ray.primitiveGenerator (r (k.succAbove j)), v]) 0
local notation "T" => QPainleve.CharacterTorus.scheme ℂ (Fin (n + 1) →₀ ℤ)

private theorem reordered_mutation_rays :
    Fin.cons reverseRay (tailRay) = r′ ∘ σ := by
  funext j
  refine Fin.cases ?_ (fun l ↦ ?_) j
  · simp [mutationFanCenterRays_self]
  · simpa only [Fin.cons_succ, Function.comp_apply, Equiv.trans_apply, finSuccEquiv_succ,
      finSuccEquiv'_symm_some] using
        (mutationFanCenterRays_of_ne Φ b r k opp (k.succAbove_ne l)).symm

private theorem reordered_mutation_center_single (j : Fin (n + 1)) :
    d (ofAdd (Pi.single j 1)) = a′ (ofAdd (Pi.single (σ j) 1)) := by
  have hsingle : reorder (Pi.single j 1) = Pi.single (σ j) 1 := by
    ext l
    simp only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Pi.single_apply,
      Equiv.symm_apply_eq]
  exact congrArg (fun x ↦ a′ (ofAdd x)) hsingle

private theorem reordered_mutation_centers (j : Fin (n + 1)) :
    d (ofAdd (Pi.single j 1)) = (Fin.cons aₖ⁻¹ (tailParam) : Fin (n + 1) → ℂˣ) j := by
  have hω : b.detDualEquiv.toLinearMap.IsAlt := b.detDualEquiv_self
  rw [reordered_mutation_center_single b r k a]
  refine Fin.cases ?_ (fun l ↦ ?_) j
  · simp
  · simp only [Equiv.trans_apply, finSuccEquiv_succ, finSuccEquiv'_symm_some, Fin.cons_succ]
    simpa only [posPart_def, chargeExchangeMatrix_apply, rayChargeMap_single,
      LinearEquiv.coe_coe, Module.Basis.detDualEquiv_apply] using
      centerMutation_character_apply_of_ne _ (rayChargeMap r) k ℂ hω a (k.succAbove_ne l)

private theorem xEvaluation_reordered_mutation :
    letI : Nonempty (Ω).cones := ⟨(r′ k).toCone⟩
    (Ω).xEvaluation b (Fin.cons reverseRay (tailRay)) d =
      ((Ω).xEvaluation b r′ a′).compHom
        (Spec.map (CommRingCat.ofHom (rename (R := ℂ) σ).toRingHom)) := by
  let : Nonempty (Ω).cones := ⟨(r′ k).toCone⟩
  rw [reordered_mutation_rays b r k opp]
  have : IsDominant (FanHom.id (Ω)).algebraicMap := by
    rw [FanHom.algebraicMap_id]
    infer_instance
  have hid : (𝟙 (Ω).algebraicRealization : (Ω).algebraicRealization ⟶
      (Ω).algebraicRealization).toRationalMap =
      Scheme.RationalMap.id (Ω).algebraicRealization := by
    rw [← Scheme.RationalMap.id_compHom, Scheme.RationalMap.compHom_id]
  simpa only [FanHom.algebraicMap_id, hid, Scheme.RationalMap.id_comp]
    using (FanHom.id (Ω)).comp_xEvaluation b b r′ (r′ ∘ σ) σ a′ d
      (reordered_mutation_center_single b r k a) (by
        intro j
        simp only [FanHom.id_latticeMap, AddMonoidHom.comp_id, Function.comp_apply])

private theorem chargeExchangeMatrix_reordered_mutation
    (B : SkewExchangeMatrix (Fin (n + 1))) (hB : E = B.matrix) :
    chargeExchangeMatrix b.detDualEquiv.toLinearMap
      (rayChargeMap (Fin.cons reverseRay (tailRay))) =
      ((Generator.permute σ).target ((Generator.mutate k).target B)).matrix := by
  rw [reordered_mutation_rays b r k opp, Generator.target_permute,
    SkewExchangeMatrix.reindex_matrix, Equiv.symm_symm, Generator.target_mutate,
    SkewExchangeMatrix.mutate_matrix, ← hB,
    ← chargeExchangeMatrix_chargeMutation _ b.detDualEquiv_self,
    ← rayChargeMap_mutationFanCenterRays b r k opp]
  ext j l
  simp only [chargeExchangeMatrix_apply, rayChargeMap_single, Matrix.submatrix_apply,
    Function.comp_apply]

variable (Φ) in
/-- In the ordered target model of a resolved mutation, the reverse pivot comes
first and the other centers keep their order. In these labels the fixed-center
X map is the independent mutation followed by the corresponding relabeling.
The terminal exchange matrix and the center character of the word are those of
the ordered blowup model. -/
theorem comp_xEvaluation_of_resolved_mutation_pivot_first {Z : Scheme} [IsIntegral Z]
    (f : Z ⟶ Φ.algebraicRealization) [IsDominant f] (g : Z ⟶ (Ω).algebraicRealization)
    (h : letI : Nonempty Φ.cones := ⟨(r k).toCone⟩
         f.toRationalMap.comp
           (Φ.mutationPartialMap b (aₖ : ℂ) h₀ h₁ opp).toRationalMap = g.toRationalMap)
    (B : SkewExchangeMatrix (Fin (n + 1))) (hB : E = B.matrix) :
    letI : Nonempty Φ.cones := ⟨(r k).toCone⟩
    letI : Nonempty (Ω).cones := ⟨(r′ k).toCone⟩
    letI : g.toRationalMap.IsDominant := h ▸ inferInstance
    let m := (Generator.mutate k).toStep B
    let w := m.toPath.comp ((Generator.permute σ).toStep _).toPath
    let ev : Z ⤏ T := f.toRationalMap.comp (Φ.xEvaluation b r a)
    let d' := a.comp w.exponentEquiv.toAddEquiv.toAddMonoidHom.toMultiplicative
    chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap (Fin.cons reverseRay (tailRay))) =
      ((Generator.permute σ).target ((Generator.mutate k).target B)).matrix ∧
    (∀ j, d' (ofAdd (Pi.single j 1)) = (Fin.cons aₖ⁻¹ (tailParam) : Fin (n + 1) → ℂˣ) j) ∧
    ∃ hdom : ev.fromFunctionField (IsLocalRing.closedPoint Z.functionField) ∈
        (w.xRationalMap ℂ).domain,
      ev.compOfDefined (w.xRationalMap ℂ) hdom =
        g.toRationalMap.comp ((Ω).xEvaluation b (Fin.cons reverseRay (tailRay)) d') := by
  let : Nonempty Φ.cones := ⟨(r k).toCone⟩
  let : Nonempty (Ω).cones := ⟨(r′ k).toCone⟩
  have : g.toRationalMap.IsDominant := h ▸ inferInstance
  intro m w ev d'
  have hc : d' = d := by
    apply MonoidHom.ext
    intro x
    simp only [d', w, m, Quiver.Path.exponentEquiv_comp, Quiver.Path.exponentEquiv_toPath,
      Step.exponentEquiv_permute, Step.exponentEquiv_mutate, ← hB, MonoidHom.comp_apply,
      AddMonoidHom.coe_toMultiplicative, AddEquiv.coe_toAddMonoidHom,
      LinearEquiv.coe_toAddEquiv, Function.comp_apply, toAdd_ofAdd]
    rfl
  rw [hc]
  refine ⟨chargeExchangeMatrix_reordered_mutation b r k opp B hB,
    reordered_mutation_centers b r k a, ?_⟩
  obtain ⟨hd, hm⟩ := Φ.comp_xEvaluation_of_resolved_mutation b r k a opp f g h B
    (fun j ↦ congrArg (fun M : Matrix _ _ ℤ ↦ M j k) hB.symm)
  let j : T ⟶ T := Spec.map (CommRingCat.ofHom (rename (R := ℂ) σ).toRingHom)
  let F := m.toPath.xRationalMap ℂ
  obtain ⟨hj, he⟩ := (ev.compOfDefined F hd).compOfDefined_toRationalMap j
  obtain ⟨hw, hcomp⟩ := ev.compOfDefined_comp F j.toRationalMap hd hj
  have hword : w.xRationalMap ℂ = F.comp j.toRationalMap := by
    simp only [w, Quiver.Path.xRationalMap_comp, Quiver.Path.xRationalMap_permute, F, j]
  refine ⟨hword.symm ▸ hw, ?_⟩
  simp only [hword, ← hcomp, he]
  refine (congrArg (·.compHom j) hm).trans ?_
  rw [← Scheme.RationalMap.comp_compHom, xEvaluation_reordered_mutation b r k a opp]

end Ordered

end TauCeti.Toric.Fan

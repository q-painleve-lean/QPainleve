/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Isometry
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.InternalCurve
public import QPainleve.AlgebraicGeometry.Chow.Nef.Anticanonical

import QPainleve.AlgebraicGeometry.Chow.RationalSurface.AmpleCone.Basic
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Ample classes on nodal auxiliary models

Extending a Picard isometry through nodal blowups preserves the ample classes
when the base pairs have no internal `(-2)`-curves and the reduced total boundary
classes correspond componentwise. The same isometry transports the real nef cone,
which allows one to transport disjoint configurations of exceptional curves.

This is the ample class comparison in the corner blowup argument of
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*, Theorem 4.7][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S4.Thmtheorem7
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass
open scoped TensorProduct

universe u

section Topology

variable {L : Type*} [AddCommGroup L] [Module ℝ L] [TopologicalSpace L]
  [IsModuleTopology ℝ L]

local instance : IsTopologicalAddGroup L := IsModuleTopology.isTopologicalAddGroup ℝ L

local instance : T2Space L := TauCeti.ModuleTopology.t2Space (Module.Free.chooseBasis ℝ L)

namespace QPainleve.BlowupTower

local notation "S(" k ")" => Spec (CommRingCat.of k)
local notation "g(" k ", " X ")" => (X ↘ S(k))
local notation "V(" X ")" => (ℝ ⊗[ℤ] Additive (LineBundleClass X))
local notation "K(" k ", " X ")" => mk (canonicalBundle k X 2)
local notation "B(" k ", " X ")" => Chow.intersectionBilinForm k X
local notation "P(" D ", " p ")" => Additive.ofMul (primeDivisorClass
  (Scheme.IdealSheafData.boundaryPrimeEmbedding D p))

section Towers

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y Z W : Scheme.{u}}
  [X.Over S(k)] [Z.Over S(k)] [X.IsProjectiveOver k] [Z.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (g(k, X))] [SmoothOfRelativeDimension 2 (g(k, Z))]
  [hRatX : Scheme.IsRationalOver (g(k, X))] [hRatZ : Scheme.IsRationalOver (g(k, Z))]
  {D : X.IdealSheafData} {F : Z.IdealSheafData}
  {n : ℕ} {T : BlowupTower X n Y} {U : BlowupTower Z n W}
  [TopologicalSpace V(Y)] [IsModuleTopology ℝ V(Y)]
  [TopologicalSpace V(W)] [IsModuleTopology ℝ V(W)]

local notation "D'" => Scheme.IdealSheafData.radical (D.comap (BlowupTower.toBase T))
local notation "F'" => Scheme.IdealSheafData.radical (F.comap (BlowupTower.toBase U))

/-- On ordered nodal blowup towers over root-free anticanonical pairs, the
extended Picard isometry identifies the canonical classes, nef cones and ample
classes if it matches the reduced total boundary components and the base
isometry matches one pair of ample classes. -/
theorem image_nefCone_eq_and_isAmple_iff_picardIsometryCongr_of_nodal
    (hT : IsNodalBoundaryTower D (g(k, X)) (𝟙 X) T)
    (hU : IsNodalBoundaryTower F (g(k, Z)) (𝟙 Z) U)
    (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier)
    (hnd : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ g(k, X)))
    (hnf : AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ g(k, Z)))
    (hcanD : mk hD.toInvertibleSheaf = K(k, X))
    (hcanF : mk hF.toInvertibleSheaf = K(k, Z))
    (σ : (D').boundaryPrimes ≃ (F').boundaryPrimes) :
    let : Smooth (g(k, X)) := SmoothOfRelativeDimension.smooth 2 _
    let : Smooth (g(k, Z)) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral X := hRatX.isIntegral_of_smooth
    let : IsIntegral Z := hRatZ.isIntegral_of_smooth
    ∀ (e : B(k, X).IsometryEquiv B(k, Z)) {H : LineBundleClass X},
      H.IsAmple → (e (Additive.ofMul H)).toMul.IsAmple →
    (∀ p : CodimensionOnePoint X, (p : X) ∉ D.support →
      Chow.realIntersectionBilinForm k X (Chow.realPrimeDivisorClass k p)
        (Chow.realPrimeDivisorClass k p) ≠ -2) →
    (∀ p : CodimensionOnePoint Z, (p : Z) ∉ F.support →
      Chow.realIntersectionBilinForm k Z (Chow.realPrimeDivisorClass k p)
        (Chow.realPrimeDivisorClass k p) ≠ -2) →
    let : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
    let : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
    let : Y.Over S(k) := ⟨T.toBase ≫ g(k, X)⟩
    let : W.Over S(k) := ⟨U.toBase ≫ g(k, Z)⟩
    let : Y.IsProjectiveOver k := T.isProjectiveOver k
    let : W.IsProjectiveOver k := U.isProjectiveOver k
    let : IsIntegral Y := hT.isClosedPointTower.isIntegral (g(k, X))
    let : IsIntegral W := hU.isClosedPointTower.isIntegral (g(k, Z))
    let : SmoothOfRelativeDimension 2 (g(k, Y)) :=
      hT.isClosedPointTower.smoothOfRelativeDimension (g(k, X))
    let : SmoothOfRelativeDimension 2 (g(k, W)) :=
      hU.isClosedPointTower.smoothOfRelativeDimension (g(k, Z))
    let : IsNoetherian Y := isNoetherian_of_finiteType (g(k, Y))
    let : IsNoetherian W := isNoetherian_of_finiteType (g(k, W))
    let := (g(k, Y)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := (g(k, W)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let : Scheme.IsRationalOver (g(k, Y)) := hT.isClosedPointTower.isRationalOver (g(k, X))
    let : Scheme.IsRationalOver (g(k, W)) := hU.isClosedPointTower.isRationalOver (g(k, Z))
    let : Module.Finite ℤ (Additive (LineBundleClass Y)) := Y.finite_picard_of_isRationalOver k
    let : Module.Finite ℤ (Additive (LineBundleClass W)) := W.finite_picard_of_isRationalOver k
    let e' := picardIsometryCongr k hT.isClosedPointTower hU.isClosedPointTower e
    (∀ p, e' P(D', p) = P(F', σ p)) →
      e' (Additive.ofMul K(k, Y)) = Additive.ofMul K(k, W) ∧
      (e'.baseChange ℝ) '' (Chow.nefCone k (X := Y) : Set V(Y)) = Chow.nefCone k (X := W) ∧
      ∀ A : LineBundleClass Y, A.IsAmple ↔ (e' (Additive.ofMul A)).toMul.IsAmple := by
  intro _ _ _ _ e H hH hHe hrootD hrootF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e' hσ
  obtain ⟨A, hA, hAe⟩ :=
    exists_isAmple_picardIsometryCongr k hT.isClosedPointTower hU.isClosedPointTower e hH hHe
  have hD' := (hT.radical_comap_toBase hD hnd).1
  have hF' := (hU.radical_comap_toBase hF hnf).1
  have hcanD' := (hT.canonicalClass_radical_comap_toBase_iff hD hnd).mpr hcanD
  have hcanF' := (hU.canonicalClass_radical_comap_toBase_iff hF hnf).mpr hcanF
  have : IsReduced (D').subscheme := (hT.radical_comap_toBase hD hnd).2.isReduced
  have : IsReduced (F').subscheme := (hU.radical_comap_toBase hF hnf).2.isReduced
  have hK := hD'.map_ofMul_inv_toInvertibleSheaf_of_boundaryPrimes hF'
    e'.toLinearEquiv.toAddMonoidHom σ hσ
  have hK' : e' (Additive.ofMul K(k, Y)) = Additive.ofMul K(k, W) := by
    simpa only [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
      LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv, hcanD', hcanF', ofMul_inv,
      map_neg, neg_inj] using hK
  have hboundary :
      e'.baseChange ℝ '' (Chow.realPrimeDivisorClass k ''
        {p : CodimensionOnePoint Y | (p : Y) ∈ (D').support}) =
      Chow.realPrimeDivisorClass k '' {p : CodimensionOnePoint W | (p : W) ∈ (F').support} := by
    rw [← (D').range_boundaryPrimeEmbedding, ← (F').range_boundaryPrimeEmbedding]
    simp only [← Set.range_comp]
    rw [← σ.surjective.range_comp (Chow.realPrimeDivisorClass k ∘ (F').boundaryPrimeEmbedding)]
    congr 1
    funext p
    simp only [Function.comp_apply, Chow.realPrimeDivisorClass_def,
      LinearMap.BilinForm.IsometryEquiv.baseChange_tmul, hσ]
  have hrD :=
    (hT.forall_realPrimeDivisorClass_self_ne_neg_two_iff k hD hnd hcanD).mpr hrootD
  have hrF :=
    (hU.forall_realPrimeDivisorClass_self_ne_neg_two_iff k hF hnf hcanF).mpr hrootF
  have hnef := Chow.image_nefCone_eq_of_anticanonical k hD' hcanD' hF' hcanF'
    hA e' hAe (congrArg Additive.toMul hK') hboundary hrD hrF
  exact ⟨hK', hnef, isAmple_iff_of_image_nefCone_eq k e' hnef⟩

end Towers

section Point

variable {k : Type u} [Field k] [IsAlgClosed k] {X Z : Scheme.{u}}
  [X.Over S(k)] [Z.Over S(k)] [X.IsProjectiveOver k] [Z.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (g(k, X))] [SmoothOfRelativeDimension 2 (g(k, Z))]
  [hRatX : Scheme.IsRationalOver (g(k, X))] [hRatZ : Scheme.IsRationalOver (g(k, Z))]
  {D : X.IdealSheafData} {F : Z.IdealSheafData} {p : X} {q : Z}

local notation "I(" p ")" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ p)
local notation "T(" p ")" => BlowupTower.nil.snoc (I(p))
local notation "Y(" p ")" => Scheme.IdealSheafData.blowup (I(p))

/-- Blowing up corresponding nodes of root-free anticanonical pairs gives a Picard isometry
identifying the canonical classes, nef cones and ample classes. The correspondence at the
centers is by incidence with boundary components and includes self-nodes. -/
theorem image_nefCone_eq_and_isAmple_iff_picardIsometryCongr_of_matching_nodes
    [TopologicalSpace V(Y(p))] [IsModuleTopology ℝ V(Y(p))]
    [TopologicalSpace V(Y(q))] [IsModuleTopology ℝ V(Y(q))]
    (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier)
    (hnd : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ g(k, X)))
    (hnf : AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ g(k, Z)))
    (hcanD : mk hD.toInvertibleSheaf = K(k, X))
    (hcanF : mk hF.toInvertibleSheaf = K(k, Z))
    (hp : IsClosed ({p} : Set X)) (hq : IsClosed ({q} : Set Z))
    (hpn : D.IsNodeOfReducedBoundary (g(k, X)) p)
    (hqn : F.IsNodeOfReducedBoundary (g(k, Z)) q)
    (σ : D.boundaryPrimes ≃ F.boundaryPrimes)
    (hcenter : ∀ a : D.boundaryPrimes, p ∈ closure {a.val} ↔ q ∈ closure {(σ a).val}) :
    let : Smooth (g(k, X)) := SmoothOfRelativeDimension.smooth 2 _
    let : Smooth (g(k, Z)) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral X := hRatX.isIntegral_of_smooth
    let : IsIntegral Z := hRatZ.isIntegral_of_smooth
    ∀ (e : B(k, X).IsometryEquiv B(k, Z)) {H : LineBundleClass X},
      H.IsAmple → (e (Additive.ofMul H)).toMul.IsAmple →
    (∀ p : CodimensionOnePoint X, (p : X) ∉ D.support →
      Chow.realIntersectionBilinForm k X (Chow.realPrimeDivisorClass k p)
        (Chow.realPrimeDivisorClass k p) ≠ -2) →
    (∀ p : CodimensionOnePoint Z, (p : Z) ∉ F.support →
      Chow.realIntersectionBilinForm k Z (Chow.realPrimeDivisorClass k p)
        (Chow.realPrimeDivisorClass k p) ≠ -2) →
    (let := LocallyOfFiniteType.isLocallyNoetherian (g(k, X))
     let := LocallyOfFiniteType.isLocallyNoetherian (g(k, Z))
     let := (g(k, X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
     let := (g(k, Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
     ∀ a, e P(D, a) = P(F, σ a)) →
    let : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
    let : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
    let hT : IsClosedPointTower X T(p) := .snoc .nil p hp rfl
    let hU : IsClosedPointTower Z T(q) := .snoc .nil q hq rfl
    let : Y(p).Over S(k) := ⟨(T(p)).toBase ≫ g(k, X)⟩
    let : Y(q).Over S(k) := ⟨(T(q)).toBase ≫ g(k, Z)⟩
    let : Y(p).IsProjectiveOver k := (T(p)).isProjectiveOver k
    let : Y(q).IsProjectiveOver k := (T(q)).isProjectiveOver k
    let : IsIntegral Y(p) := hT.isIntegral (g(k, X))
    let : IsIntegral Y(q) := hU.isIntegral (g(k, Z))
    let : SmoothOfRelativeDimension 2 (g(k, Y(p))) := hT.smoothOfRelativeDimension (g(k, X))
    let : SmoothOfRelativeDimension 2 (g(k, Y(q))) := hU.smoothOfRelativeDimension (g(k, Z))
    let : Scheme.IsRationalOver (g(k, Y(p))) := hT.isRationalOver (g(k, X))
    let : Scheme.IsRationalOver (g(k, Y(q))) := hU.isRationalOver (g(k, Z))
    let : Module.Finite ℤ (Additive (LineBundleClass Y(p))) :=
      (Y(p)).finite_picard_of_isRationalOver k
    let : Module.Finite ℤ (Additive (LineBundleClass Y(q))) :=
      (Y(q)).finite_picard_of_isRationalOver k
    let e' := picardIsometryCongr k hT hU e
    e' (Additive.ofMul K(k, Y(p))) = Additive.ofMul K(k, Y(q)) ∧
    (e'.baseChange ℝ) '' (Chow.nefCone k (X := Y(p)) : Set V(Y(p))) =
      Chow.nefCone k (X := Y(q)) ∧
    ∀ A : LineBundleClass Y(p), A.IsAmple ↔ (e' (Additive.ofMul A)).toMul.IsAmple := by
  intro _ _ _ _ e H hH hHe hrootD hrootF hσ _ _ hT hU _ _ _ _ _ _ _ _ _ _ _ _ e'
  have hTn : IsNodalBoundaryTower D (g(k, X)) (𝟙 X) T(p) :=
    .snoc .nil p hp rfl (by simpa only [toBase_nil, comap_id, Category.id_comp] using hpn)
  have hUn : IsNodalBoundaryTower F (g(k, Z)) (𝟙 Z) T(q) :=
    .snoc .nil q hq rfl (by simpa only [toBase_nil, comap_id, Category.id_comp] using hqn)
  obtain ⟨σ', hσ'⟩ := picardIsometryCongr_nodal_boundaryPrimes σ hcenter e hσ
    hp hq hD hF hnd hnf hpn hqn
  let D' := (D.comap (T(p)).toBase).radical
  let F' := (F.comap (T(q)).toBase).radical
  let D₀ := D.comap (I(p)).blowupToBase
  let F₀ := F.comap (I(q)).blowupToBase
  have hd : D'.boundaryPrimes = D₀.boundaryPrimes :=
    boundaryPrimes_eq_of_support_eq (by
      simp only [D', D₀, support_radical, toBase_snoc, toBase_nil, Category.comp_id])
  have hf : F₀.boundaryPrimes = F'.boundaryPrimes :=
    boundaryPrimes_eq_of_support_eq (by
      simp only [F', F₀, support_radical, toBase_snoc, toBase_nil, Category.comp_id])
  let d := Set.equivOfEq hd
  let f := Set.equivOfEq hf
  apply image_nefCone_eq_and_isAmple_iff_picardIsometryCongr_of_nodal hTn hUn
    hD hF hnd hnf hcanD hcanF (d.trans (σ'.trans f)) e hH hHe hrootD hrootF
  intro a
  have ha : D₀.boundaryPrimeEmbedding (d a) = D'.boundaryPrimeEmbedding a := Subtype.ext (by
    simp only [coe_boundaryPrimeEmbedding, d, Set.equivOfEq_apply])
  have hb : ∀ b : F₀.boundaryPrimes, F'.boundaryPrimeEmbedding (f b) =
      F₀.boundaryPrimeEmbedding b := fun b ↦ Subtype.ext (by
    simp only [coe_boundaryPrimeEmbedding, f, Set.equivOfEq_apply])
  rw [Equiv.trans_apply, Equiv.trans_apply, hb, ← ha]
  exact (hσ' (d a)).1

end Point

end QPainleve.BlowupTower

end Topology

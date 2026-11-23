/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Complement
public import QPainleve.Geometry.Toric.Fan.Ruling.Centers
public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter

import QPainleve.Algebra.Polynomial.Laurent
import QPainleve.AlgebraicGeometry.Blowup.Projective.Divisors
import QPainleve.Geometry.Toric.Fan.Separated
import QPainleve.LinearAlgebra.Dual.Basis
import TauCeti.AlgebraicGeometry.Blowup.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Toric mutation at the pivot fiber

The opposite-ray center blowups over the base torus of the pivot ruling are identified
by the projective-line elementary transformation. In torus coordinates this map is the
binomial twist of Gross, Hacking and Keel, [*Birational geometry of cluster algebras*][GHK],
§3.1.

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module Multiplicative PointedCone
open AddMonoidAlgebra LaurentPolynomial
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ)

local notation "v" => ρ.primitiveGenerator
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "m" => LinearMap.toAddMonoidHom (Basis.detDualEquiv b v)
local notation "h₀" => detCharacter_nonneg_or_nonpos Φ b hv hp hOpp
local notation "h₁" => mutationDetCharacter_nonneg_or_nonpos Φ b hv hp hOpp
local notation "L" => LaurentPolynomial ℂ
local notation "f" => (1 + C (c : ℂ) * T 1 : L)

private theorem pivotBinomial_ne_zero : f ≠ 0 := by
  intro he
  have hc := congrArg (fun p : L ↦ p.coeff 0) he
  simp [← LaurentPolynomial.single_eq_C_mul_T] at hc

private theorem pivot_ray_mem_mutationFan :
    hull ℝ {i v} ∈ (Ψ).cones := by
  simpa [← b.detDualEquiv_apply, b.detDualEquiv_self] using
    (Φ.hull_singleton_mem_mutationFan_iff b hv hp hOpp v).mpr hp

local notation "ρ'" => mutationFanCenterRays Φ b (fun _ : Unit ↦ ρ) () hOpp ()

private theorem opposite_ray_mem_mutationFan :
    hull ℝ {i (-v)} ∈ (Ψ).cones := by
  simpa only [mutationFanCenterRays_primitiveGenerator_self] using
    (ρ').hull_primitiveGenerator_mem

local notation "π₀" => pullback.fst (Φ.characterRuling m h₀) projectiveLineTorusι
local notation "π₁" => pullback.fst (characterRuling Ψ m h₁) projectiveLineTorusι
local notation "hdim" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)

private theorem pivotCharacter_apply_opposite :
    m (ρ').primitiveGenerator = 0 := by
  simp only [mutationFanCenterRays_primitiveGenerator_self, LinearMap.toAddMonoidHom_coe,
    map_neg, b.detDualEquiv_self, neg_zero]

/-- The binomial center ideal on the original pivot ray in the whole toric surface. -/
def Ray.mutationSourceCenterIdeal : Φ.algebraicRealization.IdealSheafData :=
  (ρ.binomialCenter hdim (b.detDualEquiv_self v) (ρ.surjective_detCharacter b) c).ker

/-- The global source center is the kernel of the pivot's binomial point. -/
theorem Ray.mutationSourceCenterIdeal_eq :
    ρ.mutationSourceCenterIdeal b c =
      (ρ.binomialCenter hdim (b.detDualEquiv_self v) (ρ.surjective_detCharacter b) c).ker :=
  (rfl)

/-- The center ideal on the opposite ray of the mutated fan, using the original ruling
character. -/
def Ray.mutationTargetCenterIdeal : (Ψ).algebraicRealization.IdealSheafData :=
  ((ρ').binomialCenter hdim (pivotCharacter_apply_opposite b ρ hOpp)
    (ρ.surjective_detCharacter b) c).ker

/-- The original pivot center ideal restricted to the ruling over the base torus. -/
def Ray.mutationPivotSourceIdeal :
    (pullback (Φ.characterRuling m h₀) projectiveLineTorusι).IdealSheafData :=
  (ρ.mutationSourceCenterIdeal b c).comap π₀

/-- The opposite pivot center ideal restricted to the mutated ruling over the base torus. -/
def Ray.mutationPivotTargetIdeal :
    (pullback ((Ψ).characterRuling m h₁) projectiveLineTorusι).IdealSheafData :=
  (ρ.mutationTargetCenterIdeal b hOpp c).comap π₁

/-- The source ideal is the pullback of the binomial center in its ray's determinant
character. -/
theorem Ray.mutationPivotSourceIdeal_def :
    ρ.mutationPivotSourceIdeal b hOpp c =
      (ρ.binomialCenter hdim (b.detDualEquiv_self v) (ρ.surjective_detCharacter b) c).ker.comap
        (π₀) := (rfl)

/-- In the opposite ray's own determinant character the transformed center has parameter
`c⁻¹`. -/
theorem Ray.mutationTargetCenterIdeal_eq :
    ρ.mutationTargetCenterIdeal b hOpp c =
      ((ρ').binomialCenter hdim (b.detDualEquiv_self (ρ').primitiveGenerator)
        ((ρ').surjective_detCharacter b) c⁻¹).ker := by
  have hm : (b.detDualEquiv (ρ').primitiveGenerator).toAddMonoidHom = -m := by
    simp only [mutationFanCenterRays_primitiveGenerator_self, map_neg]
    rfl
  unfold mutationTargetCenterIdeal
  rw [← (ρ').binomialCenter_neg_inv hdim (pivotCharacter_apply_opposite b ρ hOpp)
    (ρ.surjective_detCharacter b) c]
  congr
  exact hm.symm

/-- The restricted target center is the pullback of the opposite ray's binomial ideal
with parameter `c⁻¹`. -/
theorem Ray.mutationPivotTargetIdeal_def :
    ρ.mutationPivotTargetIdeal b hOpp c =
      ((ρ').binomialCenter hdim (b.detDualEquiv_self (ρ').primitiveGenerator)
        ((ρ').surjective_detCharacter b) c⁻¹).ker.comap (π₁) := by
  rw [mutationPivotTargetIdeal, mutationTargetCenterIdeal_eq]

local notation "I₀" => Ray.mutationPivotSourceIdeal b ρ hOpp c
local notation "I₁" => Ray.mutationPivotTargetIdeal b ρ hOpp c

/-- The open inclusion of the source blowup over the base torus into the global blowup. -/
def Ray.mutationPivotSourceBlowupι : (I₀).blowup ⟶ (ρ.mutationSourceCenterIdeal b c).blowup :=
  (ρ.mutationSourceCenterIdeal b c).blowupMap π₀

/-- The open inclusion of the target blowup over the base torus into the global blowup. -/
def Ray.mutationPivotTargetBlowupι :
    (I₁).blowup ⟶ (ρ.mutationTargetCenterIdeal b hOpp c).blowup :=
  (ρ.mutationTargetCenterIdeal b hOpp c).blowupMap π₁

/-- The source pivot blowup is the restriction along the ruling's inverse image of the torus. -/
theorem Ray.isPullback_mutationPivotSourceBlowupι :
    IsPullback (I₀).blowupToBase (ρ.mutationPivotSourceBlowupι b hOpp c) π₀
      (ρ.mutationSourceCenterIdeal b c).blowupToBase :=
  (ρ.mutationSourceCenterIdeal b c).isPullback_blowupMap_of_flat π₀

/-- The target pivot blowup is the restriction along the ruling's inverse image of the torus. -/
theorem Ray.isPullback_mutationPivotTargetBlowupι :
    IsPullback (I₁).blowupToBase (ρ.mutationPivotTargetBlowupι b hOpp c) π₁
      (ρ.mutationTargetCenterIdeal b hOpp c).blowupToBase :=
  (ρ.mutationTargetCenterIdeal b hOpp c).isPullback_blowupMap_of_flat π₁

instance Ray.isOpenImmersion_mutationPivotSourceBlowupι :
    IsOpenImmersion (ρ.mutationPivotSourceBlowupι b hOpp c) :=
  MorphismProperty.of_isPullback (ρ.isPullback_mutationPivotSourceBlowupι b hOpp c)
    (inferInstanceAs (IsOpenImmersion (π₀)))

instance Ray.isOpenImmersion_mutationPivotTargetBlowupι :
    IsOpenImmersion (ρ.mutationPivotTargetBlowupι b hOpp c) :=
  MorphismProperty.of_isPullback (ρ.isPullback_mutationPivotTargetBlowupι b hOpp c)
    (inferInstanceAs (IsOpenImmersion (π₁)))

/-- The source chart inclusion commutes with the blowup projections. -/
@[reassoc (attr := simp)]
theorem Ray.mutationPivotSourceBlowupι_blowupToBase :
    ρ.mutationPivotSourceBlowupι b hOpp c ≫ (ρ.mutationSourceCenterIdeal b c).blowupToBase =
      (I₀).blowupToBase ≫ π₀ :=
  (ρ.isPullback_mutationPivotSourceBlowupι b hOpp c).w.symm

/-- The target chart inclusion commutes with the blowup projections. -/
@[reassoc (attr := simp)]
theorem Ray.mutationPivotTargetBlowupι_blowupToBase :
    ρ.mutationPivotTargetBlowupι b hOpp c ≫ (ρ.mutationTargetCenterIdeal b hOpp c).blowupToBase =
      (I₁).blowupToBase ≫ π₁ :=
  (ρ.isPullback_mutationPivotTargetBlowupι b hOpp c).w.symm

private theorem exists_pivotBasis : ∃ d : Basis (Fin 2) ℤ N,
    d 0 = v ∧ m = (d.coord 1).toAddMonoidHom :=
  b.exists_basis_zero_eq_coord_one_eq ρ.isPrimitiveGenerator.isPrimitive
    (b.detDualEquiv_self v) (ρ.surjective_detCharacter b)

local notation "d" => Classical.choose (exists_pivotBasis b ρ)

private theorem pivotBasis_zero : d 0 = v :=
  (Classical.choose_spec (exists_pivotBasis b ρ)).1

private theorem pivotBasis_coord_one : m = (Basis.coord d 1).toAddMonoidHom :=
  (Classical.choose_spec (exists_pivotBasis b ρ)).2

private theorem pivotBasis_pos {F : Fan i} (hF : hull ℝ {i v} ∈ F.cones) :
    hull ℝ {i (d 0)} ∈ F.cones := by rw [pivotBasis_zero]; exact hF

private theorem pivotBasis_neg {F : Fan i} (hF : hull ℝ {i (-v)} ∈ F.cones) :
    hull ℝ {-i (d 0)} ∈ F.cones := by rw [pivotBasis_zero, ← map_neg]; exact hF

local notation "J(" j ")" => projectiveLine.coordinateSectionCenter f j

local notation "ep₀" => pivotBasis_pos b ρ hp
local notation "en₀" => pivotBasis_neg b ρ hOpp
local notation "ep₁" => pivotBasis_pos b ρ (pivot_ray_mem_mutationFan b ρ hOpp)
local notation "en₁" => pivotBasis_neg b ρ (opposite_ray_mem_mutationFan b ρ hOpp)
local notation "E₀" => characterRulingLaurentIso Φ m h₀ d (pivotBasis_coord_one b ρ) ep₀ en₀
local notation "E₁" => characterRulingLaurentIso Ψ m h₁ d (pivotBasis_coord_one b ρ) ep₁ en₁

private def sourceLaurentBlowupIso : (I₀).blowup ≅ (J(0)).blowup :=
  ρ.characterRulingLaurentBlowupIso h₀ d
    (pivotBasis_coord_one b ρ) ep₀ en₀ 0 (by simp [pivotBasis_zero])
    hdim (b.detDualEquiv_self v) (ρ.surjective_detCharacter b) c

private def targetLaurentBlowupIso : (I₁).blowup ≅ (J(1)).blowup :=
  (ρ').characterRulingLaurentBlowupIso h₁ d
    (pivotBasis_coord_one b ρ) ep₁ en₁ 1 (by simp [pivotBasis_zero]) hdim
    (pivotCharacter_apply_opposite b ρ hOpp) (ρ.surjective_detCharacter b) c

local notation "e₀" => sourceLaurentBlowupIso b ρ hOpp c
local notation "e₁" => targetLaurentBlowupIso b ρ hOpp c

@[reassoc]
private theorem sourceLaurentBlowupIso_hom_blowupToBase :
    (e₀).hom ≫ (J(0)).blowupToBase = (I₀).blowupToBase ≫ (E₀).hom :=
  ρ.characterRulingLaurentBlowupIso_hom_comp_blowupToBase h₀ d
    (pivotBasis_coord_one b ρ) ep₀ en₀ 0 (by simp [pivotBasis_zero])
    hdim (b.detDualEquiv_self v) (ρ.surjective_detCharacter b) c

@[reassoc]
private theorem targetLaurentBlowupIso_hom_blowupToBase :
    (e₁).hom ≫ (J(1)).blowupToBase = (I₁).blowupToBase ≫ (E₁).hom :=
  (ρ').characterRulingLaurentBlowupIso_hom_comp_blowupToBase h₁ d
    (pivotBasis_coord_one b ρ) ep₁ en₁ 1 (by simp [pivotBasis_zero]) hdim
    (pivotCharacter_apply_opposite b ρ hOpp) (ρ.surjective_detCharacter b) c

/-- Over the base torus of the pivot ruling, the actual toric center blowups are isomorphic
by the elementary transformation of the projective line. Both center ideals use
the same ruling binomial, with the target center on the opposite section. -/
def Ray.mutationPivotIso : (I₀).blowup ≅ (I₁).blowup :=
  (e₀) ≪≫ projectiveLine.elementaryTransform f 0
    (pivotBinomial_ne_zero c) ≪≫ (e₁).symm

section Divisors

open Scheme Scheme.IdealSheafData

local notation "a₀" => (-1 : ℂˣ) * c⁻¹
local notation "q" => projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (Units.val a₀)
local notation "g" =>
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({f} : Set L))))
local notation "r" => (projectiveLine L ↘ Spec (CommRingCat.of L))

private theorem comap_pivotFiber_projectiveLineTorusIsoSpecLaurent :
    (g).ker.comap projectiveLineTorusIsoSpecLaurent.hom =
      (q).ker.comap projectiveLineTorusι := by
  let j := projectiveLineTorusPoint (a₀)
  have hj : j ≫ projectiveLineTorusι = q :=
    projectiveLineTorusPoint_comp_projectiveLineTorusι _
  have hclosed : IsClosedImmersion (q) :=
    isClosedImmersion_of_comp_eq_id (projectiveLine ℂ ↘ Spec (.of ℂ)) _
      (by simp [projectiveLine.polynomialPoint_over])
  have hq : j.ker = (q).ker.comap projectiveLineTorusι :=
    ker_eq_comap_of_isPullback (q)
      (IsPullback.of_vert_isIso_mono (snd := 𝟙 _) ⟨by rw [hj, Category.id_comp]⟩)
  have hg : (g).ker = (j ≫ projectiveLineTorusIsoSpecLaurent.hom).ker := by
    rw [projectiveLineTorusPoint_comp_projectiveLineTorusIsoSpecLaurent, Hom.ker_Spec_map,
      Hom.ker_Spec_map, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, Ideal.mk_ker]
    exact congrArg (fun K : Ideal L ↦ ofIdealTop
      (K.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom)) (ker_laurentEval_neg_inv c).symm
  rw [hg, Hom.comap_ker_comp_of_isClosedImmersion, hq]

private theorem comap_pivotFiber_sourceLaurentBlowupIso :
    (g).ker.comap ((e₀).hom ≫ (J(0)).blowupToBase ≫ r) =
      (q).ker.comap ((I₀).blowupToBase ≫ π₀ ≫ Φ.characterRuling m h₀) := by
  rw [sourceLaurentBlowupIso_hom_blowupToBase_assoc,
    characterRulingLaurentIso_hom_comp_toBase, ← Category.assoc (I₀).blowupToBase,
    comap_comp, comap_pivotFiber_projectiveLineTorusIsoSpecLaurent, ← comap_comp,
    Category.assoc, ← pullback.condition]

local notation "E(" I ")" => IdealSheafData.comap I (IdealSheafData.blowupToBase I)

private theorem comap_exceptional_sourceLaurentBlowupIso :
    E(J(0)).comap (e₀).hom = E(I₀) :=
  ρ.comap_exceptionalIdeal_characterRulingLaurentBlowupIso h₀ d
    (pivotBasis_coord_one b ρ) ep₀ en₀ 0 (by simp [pivotBasis_zero])
    hdim (b.detDualEquiv_self v) (ρ.surjective_detCharacter b) c

private theorem comap_exceptional_targetLaurentBlowupIso :
    E(J(1)).comap (e₁).hom = E(I₁) :=
  (ρ').comap_exceptionalIdeal_characterRulingLaurentBlowupIso h₁ d
    (pivotBasis_coord_one b ρ) ep₁ en₁ 1 (by simp [pivotBasis_zero]) hdim
    (pivotCharacter_apply_opposite b ρ hOpp) (ρ.surjective_detCharacter b) c

/-- On the pivot blowup over the ruling torus, the total transform of the pivot fiber
is the sum of the source exceptional divisor and the pullback of the target exceptional
divisor. This is an identity of their ideal sheaves. -/
theorem Ray.comap_pivotFiber_mutationPivotIso :
    (q).ker.comap ((I₀).blowupToBase ≫ π₀ ≫ Φ.characterRuling m h₀) =
      E(I₀) * E(I₁).comap (ρ.mutationPivotIso b hOpp c).hom := by
  have he : (g).ker.comap ((J(0)).blowupToBase ≫ r) =
      E(J(0)) * E(J(1)).comap
        (projectiveLine.elementaryTransform f 0 (pivotBinomial_ne_zero c)).hom :=
    projectiveLine.comap_baseDivisor_elementaryTransform f 0 (pivotBinomial_ne_zero c)
  have he' := congrArg (fun J : (J(0)).blowup.IdealSheafData ↦ J.comap (e₀).hom) he
  have hinv : E(I₁).comap (e₁).inv = E(J(1)) := by
    rw [← comap_exceptional_targetLaurentBlowupIso b ρ hOpp c, ← comap_comp,
      Iso.inv_hom_id, comap_id]
  rw [← comap_comp, comap_pivotFiber_sourceLaurentBlowupIso,
    comap_mul, comap_exceptional_sourceLaurentBlowupIso, ← comap_comp] at he'
  simpa only [mutationPivotIso, Iso.trans_hom, Iso.symm_hom, comap_comp, hinv] using he'

end Divisors

section Torus

local notation "G" => AddMonoidAlgebra ℂ (N →+ ℤ)
local notation "S" => Localization.Away (single (0 : N →+ ℤ) (1 : ℂ) + single m (c : ℂ))
local notation "𝕋" => Spec (CommRingCat.of S)
local notation "ℓ" => Spec.algebraMap G S
local notation "a" => LinearMap.toAddMonoidHom (Basis.coord d 0)
local notation "z(" n ")" => (algebraMap G S) (single n 1)
local notation "zu(" n ")" =>
  MonoidHom.toHomUnits (MonoidHom.comp (RingHom.toMonoidHom (algebraMap G S))
    (AddMonoidAlgebra.of ℂ (N →+ ℤ))) (ofAdd n)
local notation "k" => (laurentEval zu(m) : L →ₐ[ℂ] S)
local notation "A" => @mutationTorusChartAlgEquiv N _ b v (c : ℂ)
local notation "t" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (AlgEquiv.toAlgHom A)))
local notation "eG(" F ")" => AlgEquiv.trans (denseTorusCoordinateRingEquiv (lattice F))
  (AlgEquiv.symm (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ (N →+ ℤ)))
local notation "aG(" F ")" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (AlgEquiv.toAlgHom (eG(F)))))

private theorem laurentEval_pivotBinomial : k f =
    (awayBinomialUnit 1 (c : ℂ) m : S) := by
  have hz : (zu(m) : S) = z(m) := rfl
  have hc : (algebraMap ℂ G) (c : ℂ) * single m 1 = single m (c : ℂ) := by
    rw [← Algebra.smul_def]
    simp
  rw [map_add, map_one, map_mul, laurentEval_T_one, hz, coe_awayBinomialUnit,
    AlgHom.apply_laurentPolynomial_C, IsScalarTower.algebraMap_eq ℂ G S]
  simp only [RingHom.comp_apply, ← map_mul, hc, ← AddMonoidAlgebra.one_def, map_add, map_one]

private theorem polynomialPoint_pivotBase (F : Fan i)
    (hs : ∀ σ : F.cones, (∀ x ∈ σ.val, 0 ≤ F.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, F.lattice.realCharacter m x ≤ 0)
    (hFpos : hull ℝ {i (d 0)} ∈ F.cones) (hFneg : hull ℝ {-i (d 0)} ∈ F.cones)
    (hF : Nonempty F.cones) :
    ℓ ≫ aG(F) ≫ F.denseTorusιRulingTorus m hs hF ≫
        (F.characterRulingLaurentIso m hs d (pivotBasis_coord_one b ρ) hFpos hFneg).hom =
      projectiveLine.polynomialPoint L (AlgHom.toRingHom k) 1 z(-a) := by
  rw [F.additiveDenseTorus_comp_characterRulingLaurentIso m hs d (pivotBasis_coord_one b ρ)
    hFpos hFneg hF, projectiveLine.SpecMap_polynomialPoint]
  have hk : ((Algebra.algHom ℂ G S).comp
      (laurentEval ((AddMonoidAlgebra.of ℂ (N →+ ℤ)).toHomUnits (ofAdd m)))) = k := by
    apply laurentEval_unique
    rw [AlgHom.comp_apply, laurentEval_T_one]
    rfl
  have hk' : (algebraMap G S).comp
      (laurentEval ((AddMonoidAlgebra.of ℂ (N →+ ℤ)).toHomUnits (ofAdd m))).toRingHom =
      (AlgHom.toRingHom k) := congrArg AlgHom.toRingHom hk
  rw [hk']
  have hz : (zu(-a) : S) = z(-a) := rfl
  rw [← hz, ofAdd_neg, map_inv]
  exact projectiveLine.polynomialPoint_rev (AlgHom.toRingHom k) 0 zu(a)

private theorem polynomialPoint_twist :
    t ≫ projectiveLine.polynomialPoint L (AlgHom.toRingHom k) 1 z(-a) =
      projectiveLine.polynomialPoint L (AlgHom.toRingHom k) 1 (k f * z(-a)) := by
  rw [projectiveLine.SpecMap_polynomialPoint]
  have ha : a v = 1 := by
    calc a v = a (d 0) := congrArg a (pivotBasis_zero b ρ).symm
      _ = 1 := by simp
  have hk : (A).toAlgHom.comp k = k := by
    apply laurentEval_unique
    simp [MonoidHom.coe_toHomUnits, AddMonoidAlgebra.of_apply,
      LinearMap.toAddMonoidHom_coe, b.detDualEquiv_self]
  have hk' : (A).toAlgHom.toRingHom.comp (AlgHom.toRingHom k) =
      (AlgHom.toRingHom k) := congrArg AlgHom.toRingHom hk
  rw [hk']
  congr 1
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.toAlgHom_apply]
  rw [mutationTorusChartAlgEquiv_single, laurentEval_pivotBinomial,
    AddMonoidHom.neg_apply, ha, neg_neg, zpow_one, mul_comm]

private def sourcePolynomialLift : 𝕋 ⟶ (projectiveLine.coordinateSectionCenter f 0).blowup :=
  Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (AlgHom.toRingHom k) z(-a))) ≫
    projectiveLine.sectionBlowupOppositeChartι f 0

private theorem sourcePolynomialLift_blowupToBase :
    sourcePolynomialLift b ρ c ≫ (projectiveLine.coordinateSectionCenter f 0).blowupToBase =
      projectiveLine.polynomialPoint L (AlgHom.toRingHom k) 1 z(-a) := by
  rw [sourcePolynomialLift, Category.assoc, projectiveLine.sectionBlowupOppositeChartι_blowupToBase,
    projectiveLine.polynomialPoint_def]
  rfl

/-- The common dense torus with the pivot binomial inverted, included in the pivot blowup
over the base torus. -/
def Ray.mutationPivotTorusι : 𝕋 ⟶ (I₀).blowup :=
  sourcePolynomialLift b ρ c ≫ (e₀).inv

/-- The inclusion of the localized torus in the pivot blowup projects to the usual
torus chart of the source fan. -/
@[reassoc]
theorem Ray.mutationPivotTorusι_blowupToBase :
    (ρ.mutationPivotTorusι b hOpp c) ≫ (I₀).blowupToBase =
      ℓ ≫ aG(Φ) ≫ Φ.denseTorusιRulingTorus m h₀ ⟨ρ.toCone⟩ := by
  rw [← cancel_mono (E₀).hom]
  simp only [mutationPivotTorusι, Category.assoc]
  rw [← sourceLaurentBlowupIso_hom_blowupToBase, Iso.inv_hom_id_assoc,
    sourcePolynomialLift_blowupToBase, polynomialPoint_pivotBase]

/-- On the common localized torus, the pivot isomorphism induces the binomial twist
on every character. The equality is one of morphisms into the actual target ruling
neighborhood. -/
@[reassoc]
theorem Ray.mutationPivotIso_hom_onTorus :
    (ρ.mutationPivotTorusι b hOpp c) ≫ (ρ.mutationPivotIso b hOpp c).hom ≫ (I₁).blowupToBase =
      t ≫ ℓ ≫ aG(Ψ) ≫ (Ψ).denseTorusιRulingTorus m h₁
        ⟨(ρ').toCone⟩ := by
  rw [← cancel_mono (E₁).hom]
  simp only [mutationPivotTorusι, mutationPivotIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  have hproj : sourcePolynomialLift b ρ c ≫
        (projectiveLine.elementaryTransform f 0 (pivotBinomial_ne_zero c)).hom ≫
        (J(1)).blowupToBase =
      projectiveLine.polynomialPoint L (AlgHom.toRingHom k) 1 (k f * z(-a)) :=
    projectiveLine.elementaryTransform_hom_blowupToBase_eq_polynomialPoint
      _ _ _ (sourcePolynomialLift_blowupToBase b ρ c)
  rw [← targetLaurentBlowupIso_hom_blowupToBase, Iso.inv_hom_id_assoc,
    hproj, polynomialPoint_pivotBase, polynomialPoint_twist]

local notation "U₀" => mutationComplement Φ b h₀ (c : ℂ)
local notation "U₁" => mutationComplement Ψ b h₁ (c : ℂ)
local notation "C₀" => Φ.mutationComplementTorusι b (c : ℂ) h₀ (Nonempty.intro (Ray.toCone Φ ρ))
local notation "P₀" => Scheme.IdealSheafData.blowupToBase I₀ ≫ π₀
local notation "P₁" => Scheme.IdealSheafData.blowupToBase I₁ ≫ π₁
local notation "rL" => (projectiveLine L ↘ Spec (CommRingCat.of L)) ≫
  Spec.algebraMap (Polynomial ℂ) L ≫ projectiveLine.polynomialChartι ℂ 0

/-- The pivot transformation preserves the ruling to the projective line, so in
particular it is a morphism over the coefficient field. -/
@[reassoc]
theorem Ray.mutationPivotIso_hom_comp_ruling :
    (ρ.mutationPivotIso b hOpp c).hom ≫ P₁ ≫ (Ψ).characterRuling m h₁ =
      P₀ ≫ Φ.characterRuling m h₀ := by
  have hsource :
      (e₀).hom ≫ (J(0)).blowupToBase ≫ rL = P₀ ≫ Φ.characterRuling m h₀ := by
    rw [sourceLaurentBlowupIso_hom_blowupToBase_assoc, Category.assoc,
      characterRulingLaurentIso_hom_comp_toRuling]
  have htarget :
      (e₁).hom ≫ (J(1)).blowupToBase ≫ rL = P₁ ≫ (Ψ).characterRuling m h₁ := by
    rw [targetLaurentBlowupIso_hom_blowupToBase_assoc, Category.assoc,
      characterRulingLaurentIso_hom_comp_toRuling]
  rw [← htarget, ← hsource, mutationPivotIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg ((e₀).hom ≫ ·)
    (projectiveLine.elementaryTransform_hom_over_assoc f 0 (pivotBinomial_ne_zero c) _)

local notation "W" => pullback P₀ (Scheme.Opens.ι U₀)

private theorem center_comap_mutationComplement_eq_top {F : Fan i}
    (h : ∀ σ : F.cones, (∀ x ∈ σ.val, 0 ≤ F.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, F.lattice.realCharacter m x ≤ 0)
    (p : Spec (CommRingCat.of ℂ) ⟶ F.algebraicRealization)
    (hpq : p ≫ F.characterRuling m h =
      projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (-(↑c⁻¹ : ℂ))) :
    p.ker.comap (F.mutationComplement b h (c : ℂ)).ι = ⊤ := by
  let q := projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (-(↑c⁻¹ : ℂ))
  let K := q.ker.comap (F.characterRuling m h)
  have hle : K ≤ p.ker := by
    dsimp only [K, q]
    rw [← hpq, Scheme.Hom.ker_comp]
    exact Scheme.IdealSheafData.comap_map_le _ _
  have htop : K.comap (F.mutationComplement b h (c : ℂ)).ι = ⊤ := by
    rw [Scheme.IdealSheafData.comap_eq_top_iff, ← mutationComplement_eq_compl_support]
    simp
  exact top_le_iff.mp (htop ▸ Scheme.IdealSheafData.comap_mono _ hle)

/-- The source center is absent from the complement of the pivot fiber. -/
theorem Ray.mutationSourceCenterIdeal_comap_complement :
    (ρ.mutationSourceCenterIdeal b c).comap (U₀).ι = ⊤ :=
  center_comap_mutationComplement_eq_top b ρ c h₀ _
    (ρ.binomialCenter_comp_characterRuling h₀ hdim (b.detDualEquiv_self v)
      (ρ.surjective_detCharacter b) c)

/-- The target center is absent from the complement of the same pivot fiber. -/
theorem Ray.mutationTargetCenterIdeal_comap_complement :
    (ρ.mutationTargetCenterIdeal b hOpp c).comap (U₁).ι = ⊤ :=
  center_comap_mutationComplement_eq_top b ρ c h₁ _
    ((ρ').binomialCenter_comp_characterRuling h₁ hdim (pivotCharacter_apply_opposite b ρ hOpp)
      (ρ.surjective_detCharacter b) c)

private theorem comap_pivotSourceIdeal_on_complement :
    (I₀).comap (pullback.fst π₀ (U₀).ι) = ⊤ := by
  rw [Ray.mutationPivotSourceIdeal, ← Scheme.IdealSheafData.comap_comp, pullback.condition,
    Scheme.IdealSheafData.comap_comp, ρ.mutationSourceCenterIdeal_comap_complement b hOpp c,
    Scheme.IdealSheafData.comap_top]

private theorem isOpenImmersion_pivotOverlap_snd :
    IsOpenImmersion (pullback.snd P₀ (U₀).ι) := by
  let g := pullback.fst π₀ (U₀).ι
  let q := pullback.snd π₀ (U₀).ι
  have : IsIso (((I₀).comap g).blowupToBase) := by
    apply (Scheme.IdealSheafData.isIso_blowupToBase_iff _).mpr
    rw [comap_pivotSourceIdeal_on_complement b ρ hOpp c]
    exact Scheme.IdealSheafData.isEffectiveCartier_top _
  have H := ((I₀).isPullback_blowupMap_of_flat g).flip.paste_vert
    (IsPullback.of_hasPullback π₀ (U₀).ι)
  have h : IsOpenImmersion (H.isoPullback.hom ≫ pullback.snd P₀ (U₀).ι) := by
    rw [H.isoPullback_hom_snd]
    exact inferInstanceAs (IsOpenImmersion (_ ≫ q))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion H.isoPullback.hom]
  exact h

private theorem mutationPivotTorusι_comp_ambient :
    (ρ.mutationPivotTorusι b hOpp c) ≫ P₀ = Φ.mutationTorusι b (c : ℂ) ⟨ρ.toCone⟩ := by
  rw [Ray.mutationPivotTorusι_blowupToBase_assoc, denseTorusιRulingTorus_fst,
    mutationTorusι_def]
  rfl

private def pivotOverlapTorusι : 𝕋 ⟶ W :=
  pullback.lift (ρ.mutationPivotTorusι b hOpp c) C₀ (by
    rw [mutationPivotTorusι_comp_ambient, mutationComplementTorusι_comp_ι])

private theorem isDominant_pivotOverlapTorusι_comp_snd :
    IsDominant (pivotOverlapTorusι b ρ hOpp c ≫ pullback.snd P₀ (U₀).ι) := by
  rw [pivotOverlapTorusι, pullback.lift_snd]
  exact Φ.isDominant_mutationComplementTorusι b (c : ℂ) h₀ hv ⟨ρ.toCone⟩

/-- The elementary transformation of the pivot blowups and the toric mutation on
the fiber complements agree on their entire scheme-theoretic overlap. -/
theorem Ray.mutationPivotIso_hom_agrees_on_overlap :
    pullback.fst P₀ (U₀).ι ≫ (ρ.mutationPivotIso b hOpp c).hom ≫ P₁ =
      pullback.snd P₀ (U₀).ι ≫ (Φ.mutationComplementIso b (c : ℂ) hv hp hOpp).hom ≫ (U₁).ι := by
  have := isOpenImmersion_pivotOverlap_snd b ρ hOpp c
  have : IsReduced W := isReduced_of_isOpenImmersion (pullback.snd P₀ (U₀).ι)
  let j := pivotOverlapTorusι b ρ hOpp c
  have : IsDominant (j ≫ pullback.snd P₀ (U₀).ι) :=
    isDominant_pivotOverlapTorusι_comp_snd b ρ hOpp c
  have : IsDominant j := IsDominant.of_comp_of_isOpenImmersion j (pullback.snd P₀ (U₀).ι)
  apply AlgebraicGeometry.ext_of_isDominant j
  simp only [j, pivotOverlapTorusι, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  rw [Ray.mutationPivotIso_hom_onTorus_assoc, denseTorusιRulingTorus_fst,
    mutationComplementTorusι_comp_mutationComplementIso_hom_assoc Φ b (c : ℂ)
      hv hp hOpp ⟨ρ.toCone⟩ ⟨(ρ').toCone⟩, mutationComplementTorusι_comp_ι,
    mutationTorusι_def]
  rfl

/-- The complement comparison preserves the map to the projective-line ruling. -/
@[reassoc]
theorem Ray.mutationComplementIso_hom_comp_ruling :
    (Φ.mutationComplementIso b (c : ℂ) hv hp hOpp).hom ≫ (U₁).ι ≫
        (Ψ).characterRuling m h₁ =
      (U₀).ι ≫ Φ.characterRuling m h₀ := by
  let p := pullback.snd P₀ (U₀).ι
  have : IsDominant (pivotOverlapTorusι b ρ hOpp c ≫ p) :=
    isDominant_pivotOverlapTorusι_comp_snd b ρ hOpp c
  have : IsDominant p := IsDominant.of_comp (pivotOverlapTorusι b ρ hOpp c) p
  apply AlgebraicGeometry.ext_of_isDominant p
  have heq := congrArg (fun g ↦ g ≫ (Ψ).characterRuling m h₁)
    (ρ.mutationPivotIso_hom_agrees_on_overlap b hOpp c)
  have hr := ρ.mutationPivotIso_hom_comp_ruling b hOpp c
  have hcond : pullback.fst P₀ (U₀).ι ≫ P₀ ≫ Φ.characterRuling m h₀ =
      p ≫ (U₀).ι ≫ Φ.characterRuling m h₀ := by
    dsimp only [p]
    rw [pullback.condition_assoc]
  simp only [Category.assoc] at hr hcond heq
  rw [hr, hcond] at heq
  exact heq.symm

end Torus

end TauCeti.Toric.Fan

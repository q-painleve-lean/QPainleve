/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Component
public import QPainleve.LinearAlgebra.Determinant.Dual

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.IdealSheaf.Section
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Internal centers on toric boundaries

An ordered basis of the rank-two lattice determines a primitive determinant character
for each ray. The resulting binomial points define effective Cartier ideals on the
reduced boundary. Their supports in any closed embedding of the boundary are disjoint
exactly when the ray or the parameter differs.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- The determinant character of a primitive ray generator takes every integral value. -/
theorem Ray.surjective_detCharacter (ρ : Φ.Ray) (b : Module.Basis (Fin 2) ℤ N) :
    Function.Surjective (b.detDualEquiv ρ.primitiveGenerator).toAddMonoidHom :=
  b.surjective_detDualEquiv_of_isPrimitive ρ.primitiveGenerator_isPrimitive

variable (b : Module.Basis (Fin 2) ℤ N)

local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))

/-- The same binomial point on a fixed ray can be written in the determinant character
of any other lattice basis. -/
theorem Ray.exists_binomialCenter_eq_of_basis (ρ : Φ.Ray) (d : Module.Basis (Fin 2) ℤ N)
    (c : ℂˣ) :
    letI : Nonempty Φ.cones := ⟨ρ.toCone⟩
    ∃ a : ℂˣ,
      ρ.binomialCenter rankTwo (b.detDualEquiv_self ρ.primitiveGenerator)
          (ρ.surjective_detCharacter b) a =
        ρ.binomialCenter rankTwo (d.detDualEquiv_self ρ.primitiveGenerator)
          (ρ.surjective_detCharacter d) c := by
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  let p := ρ.binomialCenterOnBoundary rankTwo (d.detDualEquiv_self ρ.primitiveGenerator)
    (ρ.surjective_detCharacter d) c
  let D := Φ.boundaryIdeal ⟨ρ.toCone⟩
  have hp : p ≫ D.subschemeι =
      ρ.binomialCenter rankTwo (d.detDualEquiv_self ρ.primitiveGenerator)
        (ρ.surjective_detCharacter d) c :=
    ρ.binomialCenterOnBoundary_comp_subschemeι rankTwo
      (d.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter d) c
  have hbase : p ≫ D.subschemeι ≫ Φ.algebraicRealizationStructureMap = 𝟙 _ := by
    rw [← Category.assoc, hp]
    exact ρ.binomialCenter_comp_structureMap rankTwo
      (d.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter d) c
  let x : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
  have hchart : D.subschemeι (p x) ∈ Set.range (Φ.affineToricChartι ρ.toCone) := by
    rw [← Scheme.Hom.comp_apply p D.subschemeι x, hp]
    have he := ρ.binomialCenter_def rankTwo (d.detDualEquiv_self ρ.primitiveGenerator)
      (ρ.surjective_detCharacter d) c
    exact ⟨_, congrArg (fun g : Spec (.of ℂ) ⟶ Φ.algebraicRealization ↦ g x) he.symm⟩
  obtain ⟨a, ha⟩ := ρ.exists_binomialCenterOnBoundary_eq_of_mem_rayChart rankTwo
    (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b) p hbase hchart
  refine ⟨a, ?_⟩
  have he := ρ.binomialCenterOnBoundary_comp_subschemeι rankTwo
    (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b) a
  exact he.symm.trans ((congrArg (· ≫ D.subschemeι) ha).trans hp)

variable [h₀ : Nonempty Φ.cones]

local notation "boundary" => Φ.boundaryIdeal h₀
local notation "χ(" ρ ")" => LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator ρ))

/-- The Cartier ideal on the reduced boundary with orbit coordinate `z^v = -c⁻¹`,
where the character `z^v` has exponent `det(v, ·)` for the ray generator `v`. -/
def Ray.internalCenter (ρ : Φ.Ray) (c : ℂˣ) :
    {J : (boundary).subscheme.IdealSheafData // J.IsEffectiveCartier} :=
  ⟨(ρ.binomialCenterOnBoundary rankTwo (m := χ(ρ)) (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c).ker,
    ρ.isEffectiveCartier_ker_binomialCenterOnBoundary rankTwo (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c⟩

@[simp]
theorem Ray.internalCenter_val (ρ : Φ.Ray) (c : ℂˣ) :
    (ρ.internalCenter b c).val =
      (ρ.binomialCenterOnBoundary rankTwo (m := χ(ρ)) (b.detDualEquiv_self _)
        (ρ.surjective_detCharacter b) c).ker := (rfl)

/-- A binomial center is the reduced ideal of a closed point in the smooth
locus of the toric boundary. -/
theorem Ray.exists_closedPoint_formallySmooth_internalCenter (ρ : Φ.Ray) (c : ℂˣ) :
    ∃ p : (boundary).subscheme, IsClosed ({p} : Set (boundary).subscheme) ∧
      (((boundary).subschemeι ≫ Φ.algebraicRealizationStructureMap).stalkMap p).hom.FormallySmooth ∧
      (ρ.internalCenter b c).val = ((boundary).subscheme.fromSpecResidueField p).ker := by
  let z := ρ.binomialCenterOnBoundary rankTwo (b.detDualEquiv_self ρ.primitiveGenerator)
    (ρ.surjective_detCharacter b) c
  let j := ρ.orbitToBoundary rankTwo (b.detDualEquiv_self ρ.primitiveGenerator)
    (ρ.surjective_detCharacter b)
  have : IsClosedImmersion z := ρ.isClosedImmersion_binomialCenterOnBoundary rankTwo _ _ c
  have : IsOpenImmersion j := ρ.isOpenImmersion_orbitToBoundary rankTwo _ _
  obtain ⟨p, hp, hi⟩ := ρ.exists_closedPoint_ker_binomialCenterOnBoundary rankTwo
    (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c
  refine ⟨p, hp, ?_, (ρ.internalCenter_val b c).trans hi⟩
  have hzp : p ∈ Set.range z := by
    rw [← z.isClosedEmbedding.isClosed_range.closure_eq, ← z.support_ker, hi,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hp]
    exact Set.mem_singleton _
  obtain ⟨q, rfl⟩ := ρ.range_binomialCenterOnBoundary_subset_range_orbitToBoundary rankTwo
    (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c hzp
  have : SmoothOfRelativeDimension 1 (j ≫ (boundary).subschemeι ≫
      Φ.algebraicRealizationStructureMap) :=
    ρ.smoothOfRelativeDimension_orbitToBoundary rankTwo _ _
  have : Smooth (j ≫ (boundary).subschemeι ≫ Φ.algebraicRealizationStructureMap) :=
    SmoothOfRelativeDimension.smooth 1 _
  apply (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ (j.stalkMap q)).mp
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
  apply Scheme.Hom.mem_smoothLocus.mp
  rw [Scheme.Hom.smoothLocus_eq_top]
  exact TopologicalSpace.Opens.mem_top q

/-- The reduced toric boundary has a regular stalk at each binomial center. -/
theorem Ray.isRegularLocalRing_stalk_of_mem_support_internalCenter (ρ : Φ.Ray) (c : ℂˣ)
    {p : (boundary).subscheme} (hp : p ∈ (ρ.internalCenter b c).val.support) :
    IsRegularLocalRing ((boundary).subscheme.presheaf.stalk p) := by
  let z := ρ.binomialCenterOnBoundary rankTwo (b.detDualEquiv_self ρ.primitiveGenerator)
    (ρ.surjective_detCharacter b) c
  let j := ρ.orbitToBoundary rankTwo (b.detDualEquiv_self ρ.primitiveGenerator)
    (ρ.surjective_detCharacter b)
  have : IsClosedImmersion z := ρ.isClosedImmersion_binomialCenterOnBoundary rankTwo _ _ c
  have : IsOpenImmersion j := ρ.isOpenImmersion_orbitToBoundary rankTwo _ _
  have hz : p ∈ Set.range z := by
    rwa [Ray.internalCenter_val, ← SetLike.mem_coe, Scheme.Hom.support_ker,
      z.isClosedEmbedding.isClosed_range.closure_eq] at hp
  obtain ⟨q, rfl⟩ := ρ.range_binomialCenterOnBoundary_subset_range_orbitToBoundary rankTwo
    (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b) c hz
  have : SmoothOfRelativeDimension 1 (j ≫ (boundary).subschemeι ≫
      Φ.algebraicRealizationStructureMap) :=
    ρ.smoothOfRelativeDimension_orbitToBoundary rankTwo _ _
  have : Smooth (j ≫ (boundary).subschemeι ≫ Φ.algebraicRealizationStructureMap) :=
    SmoothOfRelativeDimension.smooth 1 _
  exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion j q).mpr
    (isRegularLocalRing_stalk_of_smooth (j ≫ (boundary).subschemeι ≫
      Φ.algebraicRealizationStructureMap) q)

/-- An internal center restricts to an effective Cartier ideal on every ray divisor. -/
theorem Ray.isEffectiveCartier_comap_internalCenter (ρ : Φ.Ray) (c : ℂˣ)
    (hΦ : Φ.IsRegular) (τ : Φ.Ray) :
    ((ρ.internalCenter b c).val.comap (τ.boundaryComponentι hΦ)).IsEffectiveCartier := by
  rw [Ray.internalCenter_val]
  exact ρ.isEffectiveCartier_comap_ker_binomialCenterOnBoundary hΦ rankTwo
    (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c τ

/-- Reversing the ordered basis and inverting the parameter gives the same Cartier
center on the reduced boundary. -/
@[simp]
theorem Ray.internalCenter_reindex_swap (ρ : Φ.Ray) (c : ℂˣ) :
    ρ.internalCenter (b.reindex (Equiv.swap 0 1)) c⁻¹ = ρ.internalCenter b c := by
  apply Subtype.ext
  simp only [internalCenter_val]
  have hχ :
      ((b.reindex (Equiv.swap 0 1)).detDualEquiv ρ.primitiveGenerator).toAddMonoidHom =
        -χ(ρ) := by
    ext x
    simp
  -- Generalize the orbit character so its vanishing and surjectivity proofs transport with it.
  have h (m : N →+ ℤ) (hm : m = -χ(ρ))
      (hz : m ρ.primitiveGenerator = 0) (hs : Function.Surjective m) :
      ρ.binomialCenterOnBoundary rankTwo hz hs c⁻¹ =
        ρ.binomialCenterOnBoundary rankTwo (m := χ(ρ)) (b.detDualEquiv_self _)
          (ρ.surjective_detCharacter b) c := by
    subst m
    exact ρ.binomialCenterOnBoundary_neg_inv rankTwo (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c
  exact congrArg Scheme.Hom.ker (h _ hχ _ _)

/-- In the original fan scheme, the center ideal is the kernel of the binomial point
in the primitive determinant character. -/
theorem Ray.map_internalCenter_subschemeι (ρ : Φ.Ray) (c : ℂˣ) :
    (ρ.internalCenter b c).val.map (boundary).subschemeι =
      (ρ.binomialCenter rankTwo (m := χ(ρ)) (b.detDualEquiv_self _)
        (ρ.surjective_detCharacter b) c).ker := by
  rw [Ray.internalCenter_val, Scheme.IdealSheafData.map_ker]
  exact congrArg Scheme.Hom.ker (ρ.binomialCenterOnBoundary_comp_subschemeι rankTwo
    (m := χ(ρ)) (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c)

/-- A change of lattice basis can be absorbed into the parameter of the same
Cartier center on the toric boundary. -/
theorem Ray.exists_internalCenter_eq_of_basis (ρ : Φ.Ray)
    (d : Module.Basis (Fin 2) ℤ N) (c : ℂˣ) :
    ∃ a : ℂˣ, ρ.internalCenter b a = ρ.internalCenter d c := by
  obtain ⟨a, ha⟩ := ρ.exists_binomialCenter_eq_of_basis b d c
  refine ⟨a, Subtype.ext ?_⟩
  let ι := (Φ.boundaryIdeal h₀).subschemeι
  have hpoint (e : Module.Basis (Fin 2) ℤ N) (u : ℂˣ) :
      let h := e.detDualEquiv_self ρ.primitiveGenerator
      let hs := ρ.surjective_detCharacter e
      ρ.binomialCenterOnBoundary rankTwo h hs u ≫ ι = ρ.binomialCenter rankTwo h hs u :=
    ρ.binomialCenterOnBoundary_comp_subschemeι _ _ _ _
  simp only [Ray.internalCenter_val]
  apply congrArg Scheme.Hom.ker
  apply (cancel_mono ι).mp
  rw [hpoint, hpoint]
  exact ha

/-- The internal center ideal on a fixed ray determines its parameter. -/
theorem Ray.internalCenter_injective (ρ : Φ.Ray) :
    Function.Injective (fun c : ℂˣ ↦ (ρ.internalCenter b c).val) := by
  intro c d h
  have hker := congrArg (fun J ↦ Scheme.IdealSheafData.map J (boundary).subschemeι) h
  rw [ρ.map_internalCenter_subschemeι, ρ.map_internalCenter_subschemeι] at hker
  let hc := b.detDualEquiv_self ρ.primitiveGenerator
  let hp := ρ.surjective_detCharacter b
  exact ρ.binomialCenter_injective rankTwo hc hp
    (((ρ.binomialCenter rankTwo hc hp c).ker_eq_ker_iff_of_comp_eq_id
      (ρ.binomialCenter rankTwo hc hp d) (ρ.binomialCenter_comp_structureMap _ _ _ _)
      (ρ.binomialCenter_comp_structureMap _ _ _ _)).mp hker)

/-- Two ordered inputs give disjoint center supports on any embedded copy of the boundary
exactly when the ray or the parameter differs. In particular the test also applies on a
strict transform after any of the preceding internal blowups. -/
theorem disjoint_support_map_internalCenter_iff {Y : Scheme}
    (j : (boundary).subscheme ⟶ Y) [IsClosedImmersion j] (ρ τ : Φ.Ray) (c d : ℂˣ) :
    Disjoint (((ρ.internalCenter b c).val.map j).support : Set Y)
      (((τ.internalCenter b d).val.map j).support : Set Y) ↔ (ρ, c) ≠ (τ, d) := by
  let pt : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
  let center (ρ : Φ.Ray) (c : ℂˣ) :=
    ρ.binomialCenterOnBoundary rankTwo (m := χ(ρ)) (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c
  have hsupport (ρ : Φ.Ray) (c : ℂˣ) :
      (((ρ.internalCenter b c).val.map j).support : Set Y) = {j (center ρ c pt)} := by
    have : IsClosedImmersion (center ρ c) :=
      ρ.isClosedImmersion_binomialCenterOnBoundary rankTwo (b.detDualEquiv_self _)
        (ρ.surjective_detCharacter b) c
    rw [Ray.internalCenter_val, Scheme.IdealSheafData.map_ker, Scheme.Hom.support_ker,
      (center ρ c ≫ j).isClosedEmbedding.isClosed_range.closure_eq]
    exact Set.range_eq_singleton fun x ↦ congrArg (center ρ c ≫ j) (Subsingleton.elim x pt)
  rw [hsupport, hsupport, Set.disjoint_singleton, j.isClosedEmbedding.injective.ne_iff]
  apply not_congr
  constructor
  · intro h
    let p (ρ : Φ.Ray) (c : ℂˣ) :=
      ρ.binomialCenter rankTwo (m := χ(ρ)) (b.detDualEquiv_self _)
        (ρ.surjective_detCharacter b) c
    have hpc (ρ : Φ.Ray) (c : ℂˣ) : p ρ c pt = (boundary).subschemeι (center ρ c pt) :=
      congrArg (fun f : Spec (.of ℂ) ⟶ Φ.algebraicRealization ↦ f pt)
        (ρ.binomialCenterOnBoundary_comp_subschemeι rankTwo (b.detDualEquiv_self _)
          (ρ.surjective_detCharacter b) c).symm
    have hpt : p ρ c pt = p τ d pt := by rw [hpc, hpc, h]
    have hker : (p ρ c).ker = (p τ d).ker :=
      (p ρ c).ker_eq_ker_fromSpecResidueField.trans
        ((congrArg (fun x ↦ (Φ.algebraicRealization.fromSpecResidueField x).ker) hpt).trans
        (p τ d).ker_eq_ker_fromSpecResidueField.symm)
    have he : p ρ c = p τ d :=
      ((p ρ c).ker_eq_ker_iff_of_comp_eq_id (p τ d)
        (ρ.binomialCenter_comp_structureMap _ _ _ _) (τ.binomialCenter_comp_structureMap _ _ _ _)
        ).mp hker
    have hρ := ρ.eq_of_binomialCenter_eq rankTwo (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c (b.detDualEquiv_self _)
      (τ.surjective_detCharacter b) d he
    subst τ
    exact Prod.ext rfl (ρ.binomialCenter_injective _ _ _ he)
  · intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl

end TauCeti.Toric.Fan

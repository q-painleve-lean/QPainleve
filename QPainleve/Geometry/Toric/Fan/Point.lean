/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.Geometry.Toric.Algebraic.Fan.Scheme
public import TauCeti.Geometry.Toric.Analytic.Cone.Orbit.Basic
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Distinguished points of fan schemes

The distinguished complex point of a cone defines a scheme morphism into the fan scheme.
Its membership in the open cone charts follows from Tau Ceti's localization of a face
chart at a monomial. For a maximal cone it is a closed immersion with reduced image.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

/-- The rational point of a fan scheme given by the distinguished point of a cone in its
affine chart. -/
def distinguishedPointHom (σ : Φ.cones) : Spec (.of ℂ) ⟶ Φ.algebraicRealization :=
  Spec.map (CommRingCat.ofHom (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom) ≫
    Φ.affineToricChartι σ

/-- The distinguished point is the composite of its affine point with the cone chart. -/
theorem distinguishedPointHom_def (σ : Φ.cones) :
    Φ.distinguishedPointHom σ =
      Spec.map (CommRingCat.ofHom (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom) ≫
        Φ.affineToricChartι σ := (rfl)

private theorem notMem_range_faceAffineToricSchemeMap_distinguishedPoint
    {σ τ : PointedCone ℝ V} (hσ : IsToricCone i σ) (h : τ.IsFaceOf σ) (hne : τ ≠ σ)
    (x : Spec (.of ℂ)) :
    Spec.map (CommRingCat.ofHom (distinguishedPoint Φ.lattice (⊤ : σ.Face)).toRingHom) x ∉
      Set.range (faceAffineToricSchemeMap Φ.lattice h) := by
  obtain ⟨m, hm, he⟩ := hσ.rational.exists_mem_dualSemigroup_inf_ker_eq Φ.lattice h
  have hmem : ¬ ∀ y, y ∈ (⊤ : σ.Face) → Φ.lattice.realCharacter m y = 0 := by
    intro han
    apply hne
    rw [← he]
    exact inf_eq_left.mpr fun y hy ↦ LinearMap.mem_ker.mpr (han y hy)
  -- The face chart inverts a character that vanishes at the distinguished point.
  have heval := distinguishedPoint_apply_single Φ.lattice (⊤ : σ.Face) ⟨m, hm⟩
  simp only [hmem, ite_false] at heval
  subst τ
  rw [range_faceAffineToricSchemeMap Φ.lattice hσ.fg ⟨m, hm⟩]
  intro hx
  have hy := (PrimeSpectrum.mem_basicOpen _ _).mp hx
  apply hy
  rw [Spec.map_apply]
  -- The comap on prime ideals uses the evaluation of the inverted monomial.
  change distinguishedPoint Φ.lattice (⊤ : σ.Face) (MonoidAlgebra.single (ofAdd ⟨m, hm⟩) 1) ∈
    x.asIdeal
  rw [heval]
  exact x.asIdeal.zero_mem

private theorem notMem_chart_distinguishedPointHom (σ τ : Φ.cones)
    (hστ : ¬ σ ≤ τ) (x : Spec (.of ℂ)) :
    Φ.distinguishedPointHom σ x ∉ Set.range (Φ.affineToricChartι τ) := by
  intro hx
  let p := Spec.map
    (CommRingCat.ofHom (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom)
  have hinter : Φ.affineToricChartι σ (p x) ∈ Set.range (Φ.affineToricChartι (σ ⊓ τ)) := by
    rw [← Φ.range_affineToricChartι_inter_range_affineToricChartι]
    exact ⟨⟨_, rfl⟩, by simpa only [distinguishedPointHom_def, Scheme.Hom.comp_apply] using hx⟩
  let h := Φ.inf_isFaceOf_left σ.property τ.property
  rw [← Φ.faceAffineToricSchemeMap_comp_affineToricChartι h] at hinter
  obtain ⟨y, hy⟩ := hinter
  have hne : σ.val ⊓ τ.val ≠ σ.val := fun he ↦ hστ ((inf_eq_left.mp he : σ.val ≤ τ.val))
  exact Φ.notMem_range_faceAffineToricSchemeMap_distinguishedPoint
    (Φ.isToricCone σ.property) h hne x
      ⟨y, (Φ.affineToricChartι σ).isOpenEmbedding.injective (by
        simpa only [Scheme.Hom.comp_apply] using hy)⟩

/-- The distinguished point attached to `σ` belongs to the chart of `τ` exactly when
`σ` is a face of `τ`. -/
theorem distinguishedPointHom_mem_range_affineToricChartι_iff (σ τ : Φ.cones)
    (x : Spec (.of ℂ)) :
    Φ.distinguishedPointHom σ x ∈ Set.range (Φ.affineToricChartι τ) ↔ σ ≤ τ := by
  refine ⟨fun hx ↦ by_contra fun hn ↦ Φ.notMem_chart_distinguishedPointHom σ τ hn x hx,
    fun h ↦ ?_⟩
  let hface := Φ.isFaceOf_of_le τ.property σ.property h
  let p := Spec.map
    (CommRingCat.ofHom (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom)
  refine ⟨faceAffineToricSchemeMap Φ.lattice hface (p x), ?_⟩
  rw [← Scheme.Hom.comp_apply, Φ.faceAffineToricSchemeMap_comp_affineToricChartι hface,
    distinguishedPointHom_def, Scheme.Hom.comp_apply]

private theorem preimage_range_distinguishedPointHom_eq_empty (σ τ : Φ.cones)
    (hστ : ¬ σ ≤ τ) :
    Φ.affineToricChartι τ ⁻¹' Set.range (Φ.distinguishedPointHom σ) = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun z ⟨x, hx⟩ ↦
    hστ ((Φ.distinguishedPointHom_mem_range_affineToricChartι_iff σ τ x).1 ⟨z, hx.symm⟩)

/-- The distinguished point of a maximal cone is a closed subscheme with residue field
`ℂ`. -/
theorem isClosedImmersion_distinguishedPointHom (σ : Φ.cones)
    (hmax : ∀ τ : Φ.cones, σ ≤ τ → σ = τ) :
    IsClosedImmersion (Φ.distinguishedPointHom σ) := by
  let p := Spec.map
    (CommRingCat.ofHom (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom)
  have hp : IsClosedImmersion p := by
    apply IsClosedImmersion.spec_of_surjective
    intro z
    exact ⟨algebraMap ℂ _ z, AlgHom.commutes _ z⟩
  let f := Φ.distinguishedPointHom σ
  have hclosed : IsClosed (Set.range f) := by
    have hcover : TopologicalSpace.IsOpenCover
        (fun τ : Φ.cones ↦ (Φ.affineToricChartι τ).opensRange) := by
      apply TopologicalSpace.IsOpenCover.mk
      apply top_unique
      intro y _
      obtain ⟨τ, z, rfl⟩ := Φ.exists_affineToricChartι_apply_eq y
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨τ, ⟨z, rfl⟩⟩
    rw [hcover.isClosed_iff_coe_preimage]
    intro τ
    let j := Φ.affineToricChartι τ
    suffices IsClosed (j ⁻¹' Set.range f) by
      let e : Φ.affineToricChart τ ≃ₜ ↥(j.opensRange : Set Φ.algebraicRealization) :=
        j.isOpenEmbedding.isEmbedding.toHomeomorph.trans
          (Homeomorph.setCongr j.coe_opensRange.symm)
      have hmap : (j : _ → _) ∘ e.symm = Subtype.val := by
        funext x
        exact congrArg Subtype.val (e.apply_symm_apply x)
      have hpre := this.preimage e.symm.continuous
      rw [← Set.preimage_comp, hmap] at hpre
      exact hpre
    by_cases he : τ = σ
    · subst τ
      dsimp only [j]
      have hpre : Φ.affineToricChartι σ ⁻¹' Set.range f = Set.range p := by
        ext y
        constructor
        · rintro ⟨x, hx⟩
          refine ⟨x, (Φ.affineToricChartι σ).isOpenEmbedding.injective ?_⟩
          simpa only [f, distinguishedPointHom_def, Scheme.Hom.comp_apply] using hx
        · rintro ⟨x, rfl⟩
          exact ⟨x, by simp only [f, p, distinguishedPointHom_def, Scheme.Hom.comp_apply]⟩
      exact hpre ▸ p.isClosedEmbedding.isClosed_range
    · dsimp only [j]
      have hpre := Φ.preimage_range_distinguishedPointHom_eq_empty σ τ
        (fun h ↦ he (hmax τ h).symm)
      exact hpre ▸ isClosed_empty
  have : IsPreimmersion f := by
    unfold f
    rw [Φ.distinguishedPointHom_def]
    infer_instance
  exact IsClosedImmersion.of_isPreimmersion f hclosed

/-- The closed immersion of a maximal cone's distinguished point cuts out its reduced
vanishing ideal. -/
theorem ker_distinguishedPointHom_eq_vanishingIdeal (σ : Φ.cones)
    (hmax : ∀ τ : Φ.cones, σ ≤ τ → σ = τ) :
    let _ := Φ.isClosedImmersion_distinguishedPointHom σ hmax
    (Φ.distinguishedPointHom σ).ker =
      vanishingIdeal ⟨_, (Φ.distinguishedPointHom σ).isClosedEmbedding.isClosed_range⟩ := by
  dsimp only
  let p := Φ.distinguishedPointHom σ
  have := Φ.isClosedImmersion_distinguishedPointHom σ hmax
  have hs : (p.ker.support : Set Φ.algebraicRealization) = Set.range p :=
    p.support_ker.trans p.isClosedEmbedding.isClosed_range.closure_eq
  have he : p.ker.support = ⟨_, p.isClosedEmbedding.isClosed_range⟩ :=
    SetLike.coe_injective hs
  rw [← he]
  exact p.ker_eq_vanishingIdeal_support

end TauCeti.Toric.Fan

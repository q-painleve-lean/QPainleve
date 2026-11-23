/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Rescaling
public import QPainleve.Geometry.Toric.Fan.Boundary.Normalization
public import QPainleve.Geometry.Toric.Fan.Boundary.PointDivisor

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import QPainleve.AlgebraicGeometry.CartierDivisor.Pullback
import QPainleve.Geometry.Toric.Fan.Adjacency
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Branch coordinates for toric boundary periods

The component of the normalization indexed by a ray inherits its projective
coordinate from the open orbit. The actual branch over an adjacent toric node
lies at zero or infinity in this coordinate. The zero ideals and the ratios of
binomial sections in these fibers give the local center contributions to the
boundary period in [Gross, Hacking and Keel, Proposition 2.9][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
  (hdim : Module.finrank ℤ N = 2) {m : N →+ ℤ}
  (hm : m ρ.primitiveGenerator = 0) (hprim : Function.Surjective m)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "D" => Φ.boundaryIdeal inferInstance
local notation "C" => Scheme.IdealSheafData.subscheme D
local notation "I" => Scheme.singularLocus ℂ C
local notation "ν" => Scheme.IdealSheafData.blowupToBase I

variable [PrestableFamily ((Φ.boundaryIdeal inferInstance).subscheme ↘ Spec (.of ℂ))]

local notation "U" => Scheme.blowupComponent (K := ℂ) C (Φ.boundaryNormalizationComponentEquiv hΦ ρ)
local notation "e" =>
  (ρ.boundaryNormalizationComponentIso hΦ ≪≫ ρ.boundaryIsoProjectiveLine hΦ hdim hm hprim)
local notation "p[" a "]" => projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) a 0
local notation "B" => Scheme.branchScheme ℂ C
local notation "j" => Scheme.branchSchemeToBlowup ℂ C
local notation "g" => Scheme.branchSchemeToSingularLocus ℂ C
local notation "nodal" => PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := C ↘ S)
local notation "q[" z "]" => Scheme.branchRationalPoint C nodal z
local notation "L" => Proj.symmetricAlgebraTwistingBundle ℂ (Fin 2 → ℂ) 1
local notation "s[" c "]" => projectiveLine.binomialSection ℂ (↑(c : ℂˣ)⁻¹ : ℂ)

/-- A binomial center is away from the nodes, so its Cartier ideal restricts to
the unit ideal on the singular locus. -/
theorem Ray.comap_ker_binomialCenterOnBoundary_singularLocus (c : ℂˣ) :
    (ρ.binomialCenterOnBoundary hdim hm hprim c).ker.comap (I).subschemeι = ⊤ := by
  let t := ρ.orbitToBoundary hdim hm hprim
  let f := C ↘ S
  let p := ρ.binomialCenterOnBoundary hdim hm hprim c
  have hsm := ρ.smoothOfRelativeDimension_orbitToBoundary hdim hm hprim
  have : SmoothOfRelativeDimension 1 (t ≫ f) := by
    simpa only [t, f, over_eq_subschemeι_comp, Φ.algebraicRealization_over] using hsm
  have : Smooth (t ≫ f) := SmoothOfRelativeDimension.smooth 1 _
  have hdisj : Set.range p ⊆ f.smoothLocus := by
    refine (ρ.range_binomialCenterOnBoundary_subset_range_orbitToBoundary hdim hm hprim c).trans ?_
    rintro _ ⟨y, rfl⟩
    apply (t.mem_preimage).mp
    rw [t.preimage_smoothLocus_eq f, (t ≫ f).smoothLocus_eq_top]
    exact TopologicalSpace.Opens.mem_top y
  rw [comap_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ, Scheme.Hom.coe_preimage,
    TopologicalSpace.Closeds.coe_compl, Scheme.Hom.support_ker,
    p.isClosedEmbedding.isClosed_range.closure_eq, Set.eq_univ_iff_forall]
  intro x hx
  have hs : (I).subschemeι x ∈ (I).support := (I).range_subschemeι.le (Set.mem_range_self x)
  exact ((C).mem_support_singularLocus_iff_notMem_smoothLocus _).mp hs (hdisj hx)

/-- On every other normalization component, the binomial center ideal restricts to
the unit ideal. -/
theorem Ray.comap_ker_binomialCenterOnBoundary_normalizationComponent_eq_top_of_ne
    (τ : Φ.Ray) (h : ρ ≠ τ) (c : ℂˣ) :
    (ρ.binomialCenterOnBoundary hdim hm hprim c).ker.comap
      (((C).blowupComponent (K := ℂ) (Φ.boundaryNormalizationComponentEquiv hΦ τ)).ι ≫
        ν) = ⊤ := by
  rw [← τ.boundaryNormalizationComponentIso_hom_boundaryComponentι hΦ, comap_comp,
    ρ.comap_ker_binomialCenterOnBoundary_eq_top_of_ne hΦ hdim hm hprim c τ h, comap_top]

attribute [local instance] Ray.isProper_boundaryComponent_of_prestableFamily

/-- On the normalized component for the center's ray, the center ideal is the zero
ideal of `X₀ + c⁻¹ X₁` in the projective coordinate of that component. -/
theorem Ray.comap_ker_binomialCenterOnBoundary_normalizationComponent (c : ℂˣ) :
    (ρ.binomialCenterOnBoundary hdim hm hprim c).ker.comap ((U).ι ≫ ν) =
      ((InvertibleSheaf.pullback (e).hom).obj L).zeroIdeal
        ((e).hom.pullbackSections (L).obj ⊤ s[c]) := by
  calc
    _ = ((ρ.binomialCenterOnBoundary hdim hm hprim c).ker.comap
        (ρ.boundaryComponentι hΦ)).comap (ρ.boundaryNormalizationComponentIso hΦ).hom := by
      rw [← comap_comp, ρ.boundaryNormalizationComponentIso_hom_boundaryComponentι]
    _ = _ := by
      rw [ρ.comap_ker_binomialCenterOnBoundary_eq_zeroIdeal hΦ hdim hm hprim c,
        InvertibleSheaf.zeroIdeal_pullbackSections, ← comap_comp, ← Iso.trans_hom]
      exact (InvertibleSheaf.zeroIdeal_pullbackSections L _ s[c]).symm

variable {σ : Φ.cones} (hρ : ρ.toCone ≤ σ) (τ : Φ.Ray) (hτ : τ.toCone ≤ σ)
  (a : Fin 2) (ha : 0 < (if a = 1 then 1 else -1 : ℤ) * m τ.primitiveGenerator)

include hρ hτ ha in
/-- The coordinate endpoint determined by the sign of the character on the other ray
is the point over the distinguished node in this normalization component. -/
@[reassoc]
theorem Ray.polynomialPoint_comp_boundaryNormalizationComponent_subschemeι :
    p[a] ≫ (e).inv ≫ (U).ι ≫ ν ≫ (D).subschemeι = Φ.distinguishedPointHom σ := by
  rw [Iso.trans_inv, Category.assoc,
    ρ.boundaryNormalizationComponentIso_inv_ι_blowupToBase_assoc,
    ρ.boundaryComponentι_subschemeι]
  fin_cases a
  · apply ρ.polynomialPoint_comp_boundaryIsoProjectiveLine_inv_subschemeι_of_neg hΦ hdim hm hprim
      hρ τ hτ
    simpa using ha
  · apply ρ.polynomialPoint_comp_boundaryIsoProjectiveLine_inv_subschemeι_of_pos hΦ hdim hm hprim
      hρ τ hτ
    simpa using ha

include hρ hτ ha in
/-- The branch of the indicated ray at a two-ray cone has the given coordinate
endpoint as its image in the normalization. -/
theorem Ray.existsUnique_branch_at_normalizationEndpoint :
    ∃! z : B, q[z] ≫ j = p[a] ≫ (e).inv ≫ (U).ι := by
  have hne : ρ ≠ τ := by
    rintro rfl
    simp [hm] at ha
  have hc := Φ.card_toricRay_eq_two_of_ray_ne_of_le hΦ hdim hne hρ hτ
  obtain ⟨q, ⟨hq, hbase⟩, hu⟩ :=
    Φ.existsUnique_branchScheme_point_of_comp_eq_distinguishedPointHom hΦ nodal hdim hc
      (p[a] ≫ (e).inv ≫ (U).ι)
      (by simpa only [Category.assoc] using
        (ρ.polynomialPoint_comp_boundaryNormalizationComponent_subschemeι hΦ hdim hm hprim
          hρ τ hτ a ha))
  let z := q (IsLocalRing.closedPoint ℂ)
  let b := g ≫ (I).subschemeι ≫ (C ↘ S)
  have : Etale ((I).subschemeι ≫ (C ↘ S)) := (C).etale_singularLocus_subschemeι_comp nodal
  have := (C).etale_branchSchemeToSingularLocus nodal
  have : Etale b := inferInstanceAs (Etale (g ≫ (I).subschemeι ≫ (C ↘ S)))
  have hqbase (y : B) : q[y] ≫ b = 𝟙 S := by
    simpa only [b, comp_over] using (C).branchRationalPoint_comp nodal y
  have he : q[z] = q :=
    ext_of_apply_closedPoint_eq b (hqbase z) (by simpa only [b, Category.assoc] using hbase)
      ((C).branchRationalPoint_apply nodal z _)
  refine ⟨z, (congrArg (· ≫ j) he).trans hq, fun y hy ↦ ?_⟩
  have hyq := hu q[y] ⟨hy, by simpa only [b, Category.assoc] using hqbase y⟩
  exact ((C).branchRationalPoint_apply nodal y _).symm.trans
    (congrArg (fun f : S ⟶ B ↦ f (IsLocalRing.closedPoint ℂ)) hyq)

include hρ hτ ha in
/-- A branch on the indicated normalization component above the distinguished node
is its prescribed coordinate endpoint. -/
theorem Ray.branchRationalPoint_comp_toBlowup_eq_normalizationEndpoint
    (z : B) (hz : j z ∈ Set.range (U).ι)
    (hnode : (D).subschemeι (ν (j z)) = Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ)) :
    q[z] ≫ j = p[a] ≫ (e).inv ≫ (U).ι := by
  let l₀ := p[a] ≫ (e).inv
  have hrange : Set.range (q[z] ≫ j) ⊆ Set.range (U).ι := by
    rintro _ ⟨x, rfl⟩
    simpa only [Scheme.Hom.comp_apply, Scheme.branchRationalPoint_apply] using hz
  let l := IsOpenImmersion.lift (U).ι (q[z] ≫ j) hrange
  have hl : l ≫ (U).ι = q[z] ≫ j := IsOpenImmersion.lift_fac _ _ _
  have hbase : l ≫ (U).toScheme ↘ S = 𝟙 S := by
    rw [Scheme.blowupComponent_over]
    calc
      _ = (q[z] ≫ j) ≫ ν ≫ (C ↘ S) := by simpa only [Category.assoc] using
          (congrArg (· ≫ ν ≫ (C ↘ S)) hl)
      _ = _ := by
        rw [Category.assoc, ← (C).branchSchemeToSingularLocus_subschemeι_assoc ℂ]
        simpa only [comp_over] using (C).branchRationalPoint_comp nodal z
  have hnode₀ := ρ.polynomialPoint_comp_boundaryNormalizationComponent_subschemeι hΦ hdim hm hprim
    hρ τ hτ a ha
  let f := (U).ι ≫ ν ≫ (D).subschemeι
  have hf : Function.Injective f := by
    dsimp only [f]
    rw [← ρ.boundaryNormalizationComponentIso_hom_boundaryComponentι_assoc,
      ρ.boundaryComponentι_subschemeι]
    exact ((Φ.rayBoundaryIdeal hΦ ρ).subschemeι).isClosedEmbedding.injective.comp
      (ρ.boundaryNormalizationComponentIso hΦ).hom.isClosedEmbedding.injective
  have hproj₀ : l₀ ≫ f = Φ.distinguishedPointHom σ := by
    simpa only [l₀, f, Category.assoc] using hnode₀
  have hbase₀ : l₀ ≫ (U).toScheme ↘ S = 𝟙 S := calc
    _ = (l₀ ≫ f) ≫ Φ.algebraicRealization ↘ S := by
      rw [Scheme.blowupComponent_over]
      have hb : (C ↘ S) = (D).subschemeι ≫ (Φ.algebraicRealization ↘ S) :=
        (D).over_eq_subschemeι_comp
      simpa only [f, Category.assoc] using (congrArg (fun t ↦ l₀ ≫ (U).ι ≫ ν ≫ t) hb)
    _ = _ := by
      rw [hproj₀, Φ.algebraicRealization_over,
        Φ.distinguishedPointHom_comp_algebraicRealizationStructureMap]
  let x : S := IsLocalRing.closedPoint ℂ
  have hpt : f (l x) = f (l₀ x) := by
    have hproj : l ≫ f = (q[z] ≫ j) ≫ ν ≫ (D).subschemeι := by
      simpa only [f, Category.assoc] using (congrArg (· ≫ ν ≫ (D).subschemeι) hl)
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hproj, hproj₀]
    simpa only [Scheme.Hom.comp_apply, Scheme.branchRationalPoint_apply] using hnode
  have he : l = l₀ := ext_of_apply_closedPoint_eq ((U).toScheme ↘ S) hbase hbase₀ (hf hpt)
  simp only [← hl, he, l₀, Category.assoc]

/-- The binomial sections for centers `c` and `d` have ratio one at the pole and
`d / c` at zero on the normalized component. -/
theorem Ray.pullbackSections_binomialCenter_eq_smul_at_normalizationEndpoint
    (a : Fin 2) (c d : ℂˣ) :
    let l := p[a] ≫ (e).inv
    l.pullbackSections ((InvertibleSheaf.pullback (e).hom).obj L).obj ⊤
        ((e).hom.pullbackSections (L).obj ⊤ s[c]) =
      (Scheme.ΓSpecIso (.of ℂ)).inv (if a = 0 then 1 else ((d / c : ℂˣ) : ℂ)) •
        l.pullbackSections ((InvertibleSheaf.pullback (e).hom).obj L).obj ⊤
          ((e).hom.pullbackSections (L).obj ⊤ s[d]) := by
  dsimp only
  have hl : (p[a] ≫ (e).inv) ≫ (e).hom = p[a] := by simp
  let v₀ := (Scheme.ΓSpecIso (.of ℂ)).inv (if a = 0 then 1 else ((d / c : ℂˣ) : ℂ))
  let ev := (p[a]).pullbackSectionsLE (L).obj ⊤ ⊤ (p[a]).preimage_top.ge
  have hp₀ : ev s[c] = (Scheme.ΓSpecIso (.of ℂ)).inv
      (if a = 0 then 1 else (↑c⁻¹ : ℂ) * ↑(d⁻¹)⁻¹) • ev s[d] :=
    projectiveLine.pullbackSections_binomialSection_zero_eq_smul ℂ a (↑c⁻¹ : ℂ) d⁻¹
  have hp : ev s[c] = v₀ • ev s[d] := by
    simpa only [v₀, inv_inv, div_eq_mul_inv, Units.val_mul, mul_comm] using hp₀
  have hle (t : Γ((L).obj, ⊤)) :
      ev t = (p[a]).pullbackSections (L).obj ⊤ t := by
    let M := ((Scheme.Modules.pullback p[a]).obj (L).obj).presheaf
    let x := (p[a]).pullbackSections (L).obj ⊤ t
    -- The preimage of the top open is top, so the restriction is the identity.
    have h : (homOfLE (p[a]).preimage_top.ge).op = 𝟙 (Opposite.op (⊤ : (S).Opens)) :=
      Subsingleton.elim _ _
    have hmap := (congrArg M.map h).trans (M.map_id (Opposite.op (⊤ : (S).Opens)))
    exact (Scheme.Hom.pullbackSectionsLE_apply _ _ _ _ _ _).trans
      (congrArg (fun f ↦ f x) hmap)
  have hp' :
      (p[a]).pullbackSections (L).obj ⊤ s[c] =
        (Scheme.ΓSpecIso (.of ℂ)).inv (if a = 0 then 1 else ((d / c : ℂˣ) : ℂ)) •
          (p[a]).pullbackSections (L).obj ⊤ s[d] := by
    exact (hle _).symm.trans (hp.trans (congrArg (v₀ • ·) (hle _)))
  let f := p[a] ≫ (e).inv
  let u := (Scheme.Modules.pullbackCongr hl).inv.app (L).obj
  let v := (Scheme.Modules.pullbackComp f (e).hom).inv.app (L).obj
  have hc := Scheme.Hom.pullbackSections_comp_of_eq (M := (L).obj) (e).hom f hl s[c]
  have hd := Scheme.Hom.pullbackSections_comp_of_eq (M := (L).obj) (e).hom f hl s[d]
  calc
    _ = v.app ⊤ (u.app ⊤ ((p[a]).pullbackSections (L).obj ⊤ s[c])) := hc.symm
    _ = _ := (congrArg (fun t ↦ v.app ⊤ (u.app ⊤ t)) hp').trans
      ((congrArg (v.app ⊤) (Scheme.Modules.Hom.app_smul u _ _)).trans
        ((Scheme.Modules.Hom.app_smul v _ _).trans (congrArg (_ • ·) hd)))

end TauCeti.Toric.Fan

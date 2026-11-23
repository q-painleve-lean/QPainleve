/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.StrictTransform
public import TauCeti.AlgebraicGeometry.Blowup.AffineCharts
public import TauCeti.RingTheory.Ideal.AssociatedGraded
import QPainleve.RingTheory.Ideal.AffineBlowup.StrictTransform
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality

/-!
# Total and strict transforms on blowup charts

On an order-one affine chart the total-transform ideal of a hypersurface is its
strict-transform ideal times the exceptional ideal to the order of the local equation.
The comparison uses Tau Ceti's schematic closure theorem for the strict-transform morphism
([The Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)).
-/

public section

open CategoryTheory Limits
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

private theorem compl_support_ofIdealTop_span {B : Type u} [CommRing B] (a : B) :
    (ofIdealTop ((Ideal.span {a}).map (Scheme.ΓSpecIso (.of B)).inv.hom)).support.compl =
      (PrimeSpectrum.basicOpen a : (Spec (.of B)).Opens) := by
  apply TopologicalSpace.Opens.ext
  -- The open complement has the complement of the support as its carrier.
  change ((ofIdealTop ((Ideal.span {a}).map (Scheme.ΓSpecIso (.of B)).inv.hom)).support :
    Set (Spec (.of B)))ᶜ = (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum B))
  rw [coe_support_ofIdealTop, Spec_zeroLocus, ← Ideal.coe_comap,
    Ideal.comap_map_of_bijective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of B)).inv),
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl, PrimeSpectrum.zeroLocus_span]
  rfl

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I D : X.IdealSheafData)
variable {B : Type u} [CommRing B] (c : Spec (.of B) ⟶ I.blowup) [IsOpenImmersion c]
variable {e f : B}

private theorem ker_blowupMap_comap_of_principal
    (hD : D.comap (c ≫ I.blowupToBase) =
      ofIdealTop ((Ideal.span {f}).map (Scheme.ΓSpecIso (.of B)).inv.hom))
    (hE : I.comap (c ≫ I.blowupToBase) =
      ofIdealTop ((Ideal.span {e}).map (Scheme.ΓSpecIso (.of B)).inv.hom)) :
    let q := Ideal.Quotient.mk (Ideal.span {f})
    ((I.blowupMap D.subschemeι).ker).comap c =
      (Spec.map (CommRingCat.ofHom ((algebraMap _ (Localization.Away (q e))).comp q))).ker := by
  dsimp only
  let Q := B ⧸ Ideal.span {f}
  let q : B →+* Q := Ideal.Quotient.mk (Ideal.span {f})
  let d := Spec.map (CommRingCat.ofHom q)
  let p := pullback.snd D.subschemeι I.blowupToBase
  let W := (pullback.fst D.subschemeι I.blowupToBase ≫ D.subschemeι) ⁻¹ᵁ I.support.compl
  let l := Spec.map (CommRingCat.ofHom (algebraMap Q (Localization.Away (q e))))
  have hd : d.ker = D.comap (c ≫ I.blowupToBase) := by
    dsimp only [d, q]
    rw [hD, Scheme.Hom.ker_Spec_map, CommRingCat.hom_ofHom, Ideal.mk_ker]
  have hle : D.subschemeι.ker ≤ (d ≫ c ≫ I.blowupToBase).ker := by
    rw [Scheme.Hom.ker_comp, ker_subschemeι, le_map_iff_comap_le, hd]
  let k := IsClosedImmersion.lift D.subschemeι (d ≫ c ≫ I.blowupToBase) hle
  let j : Spec (.of Q) ⟶ pullback D.subschemeι I.blowupToBase :=
    pullback.lift k (d ≫ c) (by simp [k])
  have hj : j ≫ p = d ≫ c := by simp [j, p]
  have hp : IsPullback d j c p := by
    have : IsClosedImmersion d :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    apply isPullback_of_isClosedImmersion d p j c hj.symm
    dsimp only [p]
    rw [ker_eq_comap_of_isPullback _ (IsPullback.of_hasPullback _ _).flip,
      ker_subschemeι, ← comap_comp, hd]
  -- The complement of the exceptional divisor pulls back to the principal open on the quotient.
  have hpre : j ⁻¹ᵁ W = l.opensRange := by
    have hproj : j ≫ pullback.fst D.subschemeι I.blowupToBase ≫ D.subschemeι =
        d ≫ c ≫ I.blowupToBase := by
      rw [pullback.condition, ← Category.assoc, ← Category.assoc, hj, Category.assoc]
    dsimp only [W, d, l]
    rw [← Scheme.Hom.comp_preimage, hproj, Scheme.Hom.comp_preimage,
      ← compl_support_comap, hE, compl_support_ofIdealTop_span, SpecMap_preimage_basicOpen]
    exact (Scheme.Hom.opensRange_localizationAway (R := .of Q) (q e)).symm
  have hrange : Set.range (l ≫ j) ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    have hx : l x ∈ j ⁻¹ᵁ W := hpre.symm ▸ ⟨x, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι, Scheme.Hom.comp_apply]
    exact hx
  let t := IsOpenImmersion.lift W.ι (l ≫ j) hrange
  have hpb : IsPullback t l W.ι j :=
    IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ _).symm
      (by simpa only [Scheme.Opens.opensRange_ι] using hpre)
  have : IsLocallyNoetherian I.blowup :=
    LocallyOfFiniteType.isLocallyNoetherian I.blowupToBase
  have hc : (Spec.map (CommRingCat.ofHom ((algebraMap _ (Localization.Away (q e))).comp q))).ker =
      (W.ι ≫ p).ker.comap c := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact ker_eq_comap_of_isPullback_of_isOpenImmersion c (hpb.flip.paste_horiz hp)
  rw [ker_blowupMap, ← hc]

/-- On a native affine blowup chart indexed by a regular center element of order one, the total
transform of a principal ideal of order `m` is the product of the actual strict-transform ideal
and the `m`th power of the exceptional ideal. The ideals on both sides are restricted to the
same chart in the scheme blowup. -/
theorem comap_eq_pow_mul_ker_blowupMap_on_affineBlowupChart
    {U : X.Opens} (hU : IsAffineOpen U) {a f : Γ(X, U)}
    [NoZeroDivisors (Ideal.AssociatedGraded (I.ideal ⟨U, hU⟩))]
    (ha : a ∈ I.ideal ⟨U, hU⟩) (ha₂ : a ∉ I.ideal ⟨U, hU⟩ ^ 2)
    (haReg : a ∈ nonZeroDivisors Γ(X, U))
    (hD : D.ideal ⟨U, hU⟩ = Ideal.span {f}) {m : ℕ}
    (hf : f ∈ I.ideal ⟨U, hU⟩ ^ m) (hf' : f ∉ I.ideal ⟨U, hU⟩ ^ (m + 1)) :
    let c := affineBlowupι (Localization.Away a) ha ≫ I.blowupChart hU
    D.comap (c ≫ I.blowupToBase) =
      (I.comap (c ≫ I.blowupToBase)) ^ m * ((I.blowupMap D.subschemeι).ker).comap c := by
  let J : Ideal Γ(X, U) := I.ideal ⟨U, hU⟩
  let B := J.affineBlowup a (Localization.Away a)
  let c := affineBlowupι (Localization.Away a) ha ≫ I.blowupChart hU
  let φ := CommRingCat.ofHom (algebraMap Γ(X, U) B)
  have hπ : c ≫ I.blowupToBase = Spec.map φ ≫ hU.fromSpec := by
    dsimp only [c, φ]
    rw [Category.assoc, blowupChart_blowupToBase, toSpecCoeff_reesAlgebra]
    simp only [Category.assoc, affineBlowupι_toSpecZero_assoc]
  have hD' : D.comap (c ≫ I.blowupToBase) =
      ofIdealTop ((Ideal.span {algebraMap Γ(X, U) B f}).map
        (Scheme.ΓSpecIso (.of B)).inv.hom) := by
    rw [hπ, comap_SpecMap_fromSpec_eq_ofIdealTop, hD, CommRingCat.hom_ofHom,
      Ideal.map_span, Set.image_singleton]
  have hI' : I.comap (c ≫ I.blowupToBase) =
      ofIdealTop ((J.map (algebraMap Γ(X, U) B)).map (Scheme.ΓSpecIso (.of B)).inv.hom) := by
    rw [hπ, comap_SpecMap_fromSpec_eq_ofIdealTop, CommRingCat.hom_ofHom]
  have hE := hI'.trans (by rw [Ideal.map_algebraMap_affineBlowup ha])
  have : IsOpenImmersion c := IsOpenImmersion.comp _ _
  have hstr := ker_blowupMap_comap_of_principal I D c hD' hE
  dsimp only at hstr ⊢
  rw [hstr, hI', hπ, comap_SpecMap_fromSpec_eq_ofIdealTop, hD, CommRingCat.hom_ofHom,
    Scheme.Hom.ker_Spec_map, CommRingCat.hom_ofHom, ← ofIdealTop_pow, ← Ideal.map_pow,
    ← ofIdealTop_mul, ← Ideal.map_mul,
    ← Ideal.map_span_singleton_eq_pow_mul_ker_away_quotient_affineBlowup ha ha₂ haReg hf hf']

/-- Over an affine open where the center is generated by regular order-one elements, the
total-transform ideal factors as the strict-transform ideal times the exceptional ideal to
the order of the local equation. The equality holds on the entire inverse image of the open. -/
theorem comap_eq_pow_mul_ker_blowupMap_on_blowupChart
    {U : X.Opens} (hU : IsAffineOpen U) {f : Γ(X, U)}
    [NoZeroDivisors (Ideal.AssociatedGraded (I.ideal ⟨U, hU⟩))]
    {ι : Type*} (a : ι → Γ(X, U)) (ha : Ideal.span (Set.range a) = I.ideal ⟨U, hU⟩)
    (ha₂ : ∀ i, a i ∉ I.ideal ⟨U, hU⟩ ^ 2) (haReg : ∀ i, a i ∈ nonZeroDivisors Γ(X, U))
    (hD : D.ideal ⟨U, hU⟩ = Ideal.span {f}) {m : ℕ}
    (hf : f ∈ I.ideal ⟨U, hU⟩ ^ m) (hf' : f ∉ I.ideal ⟨U, hU⟩ ^ (m + 1)) :
    let c := I.blowupChart hU
    D.comap (c ≫ I.blowupToBase) =
      (I.comap (c ≫ I.blowupToBase)) ^ m * ((I.blowupMap D.subschemeι).ker).comap c := by
  let J : Ideal Γ(X, U) := I.ideal ⟨U, hU⟩
  have hmem (i : ι) : a i ∈ J := by
    dsimp only [J]
    rw [← ha]
    exact Ideal.subset_span (Set.mem_range_self i)
  let chart (i : ι) := affineBlowupι (Localization.Away (a i)) (hmem i)
  let cover : (Proj (reesAlgebra.grade J)).OpenCover :=
    .mkOfCovers ι (fun i ↦ Spec (.of (J.affineBlowup (a i) (Localization.Away (a i))))) chart
      (fun x ↦ by
        have htop := iSup_opensRange_affineBlowupι (s := a) ha
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (htop.ge (Set.mem_univ x))
        exact ⟨i, hi⟩)
      (fun _ ↦ inferInstance)
  refine ext_of_comap_openCover cover fun i ↦ ?_
  -- The factorization on each chart uses the restrictions of the same three global ideals.
  dsimp only [cover, Scheme.Cover.mkOfCovers_f]
  rw [comap_mul, comap_pow, ← comap_comp, ← comap_comp, ← comap_comp, ← Category.assoc]
  exact I.comap_eq_pow_mul_ker_blowupMap_on_affineBlowupChart D hU (hmem i) (ha₂ i)
    (haReg i) hD hf hf'

end AlgebraicGeometry.Scheme.IdealSheafData

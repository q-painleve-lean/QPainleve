/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.Boundary
public import QPainleve.Geometry.Toric.Fan.Mutation.Chart
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic
import QPainleve.AlgebraicGeometry.Gluing
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Basic
import QPainleve.Geometry.Toric.BaseChange.Fan
import TauCeti.Algebra.Group.UniqueProds.TorsionFree
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Toric mutation on the complement of the pivot fiber

The affine mutation maps glue over the open where the pivot linear form on the
ruling base is nonvanishing. Their restrictions to the common open torus are
the binomial twist of Gross, Hacking and Keel, [*Birational geometry of cluster
algebras*][GHK], §3.1 and the proof of Theorem 5.6.

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open AddMonoidAlgebra Multiplicative
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

variable {K : Type} [CommRing K] {N V : Type} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule K (Fin 2 → K)

private def pivotForm (c : K) : SymmetricAlgebra K (Fin 2 → K) :=
  projectiveLine.coord K 0 + c • projectiveLine.coord K 1

/-- The nonvanishing locus of the pivot linear form `X₀ + c X₁` on the ruling base. -/
def mutationRulingComplement (c : K) : (projectiveLine K).Opens :=
  Proj.basicOpen 𝒜 (pivotForm c)

/-- The missing point has affine coordinate `-c⁻¹` in chart zero. -/
theorem mutationRulingComplement_eq_compl_support (c : Kˣ) :
    mutationRulingComplement (c : K) =
      (projectiveLine.polynomialPoint K (RingHom.id K) 0 (-(↑c⁻¹ : K))).ker.support.compl :=
  projectiveLine.basicOpen_coord_add_smul_eq_compl_support c

private theorem pivotForm_mem (c : K) : pivotForm c ∈ 𝒜 1 :=
  (𝒜 1).add_mem (projectiveLine.coord_mem K 0) ((𝒜 1).smul_mem c (projectiveLine.coord_mem K 1))

private def sideIndex (side : Bool) : Fin 2 := if side then 1 else 0

variable (Φ : Fan i) (b : Module.Basis (Fin 2) ℤ N) {v : N}

local notation "m" => (LinearMap.toAddMonoidHom (Module.Basis.detDualEquiv b v))

/-- The open of a fan realization lying over the complement of the pivot fiber
on the projective line. The defining linear form is `X₀ + c X₁`. -/
def mutationComplement
    (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0) (c : K) :
    (Φ.finiteFanScheme K).Opens :=
  Φ.characterRuling K m h ⁻¹ᵁ mutationRulingComplement c

/-- Restriction of the character ruling to the complement of the pivot fiber. -/
def mutationComplementToRuling
    (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0) (c : K) :
    (Φ.mutationComplement b h c).toScheme ⟶ (mutationRulingComplement c).toScheme :=
  Φ.characterRuling K m h ∣_ mutationRulingComplement c

/-- The ruling on the fiber complement is the pullback along the base open inclusion. -/
theorem isPullback_mutationComplementToRuling
    (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0) (c : K) :
    IsPullback (Φ.mutationComplementToRuling b h c) (Φ.mutationComplement b h c).ι
      (mutationRulingComplement c).ι (Φ.characterRuling K m h) :=
  isPullback_morphismRestrict _ _

/-- The mutation complement is the inverse image of the indicated projective basic open. -/
theorem mutationComplement_eq
    (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0) (c : K) :
    Φ.mutationComplement b h c =
      Φ.characterRuling K m h ⁻¹ᵁ
        Proj.basicOpen 𝒜 (projectiveLine.coord K 0 + c • projectiveLine.coord K 1) :=
  (rfl)

/-- For a unit center parameter, the pivot fiber is the scheme fiber over the
point `[1 : -c⁻¹]` of the projective line. -/
theorem mutationComplement_eq_compl_support
    (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0) (c : Kˣ) :
    Φ.mutationComplement b h (c : K) =
      (((projectiveLine.polynomialPoint K (RingHom.id K) 0 (-(↑c⁻¹ : K))).ker.comap
        (Φ.characterRuling K m h)).support.compl) := by
  unfold mutationComplement
  rw [mutationRulingComplement_eq_compl_support, Scheme.IdealSheafData.compl_support_comap]

variable (σ : Φ.cones) (side : Bool)
  (hs : mutationChartCharacter b (v := v) side ∈ dualSemigroup Φ.lattice σ.val)
  (c : K)

local notation "R(" κ ")" => AddMonoidAlgebra K (dualSemigroup (lattice Φ) κ)
local notation "q" => (Subtype.mk (mutationChartCharacter b (v := v) side) hs :
  dualSemigroup (lattice Φ) (Subtype.val σ))
local notation "B" => (mutationChartBinomial Φ side c q)
local notation "L" => (Localization.Away B)
local notation "LS" => Spec (CommRingCat.of L)
local notation "loc" => Spec.map (CommRingCat.ofHom (algebraMap (R(σ.val)) L))

local notation "chart[" Ξ "," κ "]" => Fan.affineChartι K Ξ κ

/-- The inverse image of the mutation complement in an additive cone chart is
the basic open of its regular pivot binomial. -/
theorem affineChartι_preimage_mutationComplement
    (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0) :
    chart[Φ, σ] ⁻¹ᵁ Φ.mutationComplement b h c = PrimeSpectrum.basicOpen B := by
  have hm : (if sideIndex side = 0 then m else -m) =
      mutationChartCharacter b (v := v) side := by
    cases side <;> simp [sideIndex]
  let j := sideIndex side
  rw [mutationComplement, mutationRulingComplement,
    ← Scheme.Hom.comp_preimage (Φ.affineChartι K σ),
    Φ.affineToricChartι_comp_characterRuling K m h σ j (hm.symm ▸ hs),
    Scheme.Hom.comp_preimage,
    projectiveLine.polynomialChartι_preimage_basicOpen_of_mem
      (pivotForm_mem c), SpecMap_preimage_basicOpen]
  congr 1
  have ha : (⟨_, hm.symm ▸ hs⟩ : dualSemigroup Φ.lattice σ.val) = q := Subtype.ext hm
  change Polynomial.aeval (single (⟨_, hm.symm ▸ hs⟩ : dualSemigroup Φ.lattice σ.val) (1 : K))
      (projectiveLine.dehomogenize K j (pivotForm c)) = _
  rw [ha]
  have hscalar (a : dualSemigroup Φ.lattice σ.val) :
      algebraMap K (R(σ.val)) c * single a 1 = single a c := by
    rw [← Algebra.smul_def]
    simp
  cases side
  · simp only [j, sideIndex, Bool.false_eq_true, ↓reduceIte, pivotForm]
    rw [projectiveLine.dehomogenize_coord_zero_add_smul]
    simp only [map_add, map_mul, map_one, Polynomial.aeval_X, Polynomial.aeval_C,
      mutationChartBinomial_eq, Bool.cond_false]
    exact congrArg (1 + ·) (hscalar _)
  · simp only [j, sideIndex, ↓reduceIte, pivotForm]
    rw [projectiveLine.dehomogenize_coord_one_add_smul]
    simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C,
      mutationChartBinomial_eq, Bool.cond_true, add_comm]

variable (h : ∀ τ : Φ.cones,
  (∀ x ∈ τ.val, 0 ≤ Φ.lattice.realCharacter (b.detDualEquiv v).toAddMonoidHom x) ∨
  ∀ x ∈ τ.val, Φ.lattice.realCharacter (b.detDualEquiv v).toAddMonoidHom x ≤ 0)

local notation "U" => (mutationComplement Φ b (v := v) h c)

private def complementChartToFan : LS ⟶ (Φ.finiteFanScheme K) :=
  loc ≫ chart[Φ, σ]

include h in
private theorem range_complementChartToFan :
    Set.range (complementChartToFan Φ b σ side hs c) =
      Set.range (Φ.affineChartι K σ) ∩ (U : Set (Φ.finiteFanScheme K)) := by
  rw [complementChartToFan]
  have hcomp : ⇑(loc ≫ chart[Φ, σ]) =
      (chart[Φ, σ]) ∘ loc := funext (Scheme.Hom.comp_apply _ _)
  -- The affine localization map on points is prime ideal contraction.
  have hloc : Set.range ⇑loc =
      (PrimeSpectrum.basicOpen B : Set (PrimeSpectrum (R(σ.val)))) :=
    PrimeSpectrum.localization_away_comap_range L B
  rw [hcomp, Set.range_comp, hloc,
    ← affineChartι_preimage_mutationComplement Φ b σ side hs c h]
  change chart[Φ, σ] '' (chart[Φ, σ] ⁻¹' (U : Set (Φ.finiteFanScheme K))) = _
  rw [Set.image_preimage_eq_inter_range, Set.inter_comm]

/-- The basic open of the pivot binomial in an additive chart maps into the
fiber complement. -/
def mutationComplementChartι : LS ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι (complementChartToFan Φ b σ side hs c) (by
    rw [range_complementChartToFan Φ b σ side hs c h, Scheme.Opens.range_ι]
    exact Set.inter_subset_right)

/-- The localized chart inclusion composed with the open inclusion into the fan realization. -/
@[reassoc (attr := simp)]
theorem mutationComplementChartι_comp_ι :
    (Φ.mutationComplementChartι b σ side hs c h) ≫ (U).ι =
      loc ≫ chart[Φ, σ] :=
  IsOpenImmersion.lift_fac _ _ _

instance isOpenImmersion_mutationComplementChartι :
    IsOpenImmersion (Φ.mutationComplementChartι b σ side hs c h) := by
  have : IsOpenImmersion (Φ.mutationComplementChartι b σ side hs c h ≫ (U).ι) := by
    rw [mutationComplementChartι_comp_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (U).ι

section Torus

local notation "G" => AddMonoidAlgebra K (N →+ ℤ)
local notation "P" => (single (0 : N →+ ℤ) (1 : K) + single m c)
local notation "T" => Localization.Away P
local notation "𝕋" => Spec (CommRingCat.of T)

private def torusToChart : 𝕋 ⟶ LS :=
  Spec.map (CommRingCat.ofHom (mutationChartToTorus Φ b side c q rfl).toRingHom)

local notation "zeroι[" Ξ "," h₀ "]" =>
  Fan.affineChartι K Ξ (Subtype.mk ⊥ (Fan.bot_mem Ξ (Subtype.property (Nonempty.some h₀))))
local notation "toTorusRing" =>
  AddMonoidAlgebra.mapDomainAlgHom K K (AddSubmonoid.subtype (dualSemigroup (lattice Φ) ⊥))

/-- The dense torus with the pivot binomial inverted, included into the fan scheme. -/
def mutationTorusι (h₀ : Nonempty Φ.cones) : 𝕋 ⟶ Φ.finiteFanScheme K :=
  Spec.map (CommRingCat.ofHom ((Algebra.algHom K G T).comp toTorusRing).toRingHom) ≫
    zeroι[Φ, h₀]

/-- The localized torus inclusion factors through the zero-cone chart. -/
theorem mutationTorusι_def (h₀ : Nonempty Φ.cones) :
    Φ.mutationTorusι b (v := v) c h₀ =
      Spec.algebraMap G T ≫ Spec.map (CommRingCat.ofHom (toTorusRing).toRingHom) ≫
        zeroι[Φ, h₀] := by
  rw [mutationTorusι, Spec.algebraMap, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  rfl

private theorem torusToChart_comp_complementChartToFan :
    torusToChart Φ b σ side hs c ≫ complementChartToFan Φ b σ side hs c =
      mutationTorusι Φ b (v := v) c ⟨σ⟩ := by
  let hf := (Φ.isToricCone σ.property).salient.bot_isFaceOf
  rw [torusToChart, complementChartToFan, mutationTorusι,
    ← Fan.faceAffineChartMap_comp_affineChartι K (τ := ⟨⊥, Φ.bot_mem σ.property⟩) (σ := σ) hf,
    faceAffineChartMap_def]
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 2
  let f := mutationChartToTorus Φ b side c q rfl
  let g := faceAffineChartRingMap K Φ.lattice hf
  suffices f.comp (Algebra.algHom K _ _) = ((Algebra.algHom K G T).comp toTorusRing).comp g by
    exact congrArg (fun f ↦ CommRingCat.ofHom f.toRingHom) this
  apply (AddMonoidAlgebra.lift K T (dualSemigroup Φ.lattice σ.val)).symm.injective
  apply MonoidHom.ext
  intro x
  change f (algebraMap _ _ (single x.toAdd 1)) = algebraMap G T (toTorusRing (g (single x.toAdd 1)))
  simp only [f, g, faceAffineChartRingMap_single, mapDomainAlgHom_apply, mapDomain_single,
    mutationChartToTorus_single]
  rfl

private theorem isDominant_mutationTorusι [IsDomain K] (hv : v ≠ 0) (h₀ : Nonempty Φ.cones) :
    IsDominant (mutationTorusι Φ b (v := v) c h₀) := by
  have hm : m ≠ 0 := by
    intro he
    apply hv
    apply b.detDualEquiv.injective
    ext x
    rw [map_zero, LinearMap.zero_apply]
    exact DFunLike.congr_fun he x
  have hp : P ≠ 0 := by
    classical
    intro he
    have hc := congrArg (fun a : G ↦ a.coeff 0) he
    simp [AddMonoidAlgebra.coeff_single, hm.symm] at hc
  let f := (Algebra.algHom K G T).comp toTorusRing
  have := Function.Injective.isAddTorsionFree (AddMonoidHom.coeFn N ℤ) DFunLike.coe_injective
  have hinj : Function.Injective f :=
    (IsLocalization.injective T (powers_le_nonZeroDivisors_of_noZeroDivisors hp)).comp
      (mapDomain_injective Subtype.val_injective)
  have : IsDominant (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    rw [isDominant_iff]
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
      ((RingHom.injective_iff_ker_eq_bot _).mp hinj ▸ bot_le)
  exact inferInstanceAs (IsDominant (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ zeroι[Φ, h₀]))

include h in
private theorem torusToChart_comp_mutationComplementChartι (τ : Φ.cones)
    (t : Bool) (ht : mutationChartCharacter b (v := v) t ∈ dualSemigroup Φ.lattice τ.val) :
    torusToChart Φ b σ side hs c ≫ Φ.mutationComplementChartι b σ side hs c h =
      torusToChart Φ b τ t ht c ≫ Φ.mutationComplementChartι b τ t ht c h := by
  rw [← cancel_mono (U).ι]
  have he := (torusToChart_comp_complementChartToFan Φ b σ side hs c).trans
    (torusToChart_comp_complementChartToFan Φ b τ t ht c).symm
  simpa only [Category.assoc, mutationComplementChartι_comp_ι, complementChartToFan] using he

/-- The localized torus included into the complement of the pivot fiber. -/
def mutationComplementTorusι (h₀ : Nonempty Φ.cones) : 𝕋 ⟶ (U).toScheme :=
  let σ : Φ.cones := ⟨⊥, Φ.bot_mem h₀.some.property⟩
  let hs : mutationChartCharacter b (v := v) false ∈ dualSemigroup Φ.lattice σ.val := by
    simp [σ]
  torusToChart Φ b σ false hs c ≫ Φ.mutationComplementChartι b σ false hs c h

/-- Every localized cone chart gives the same inclusion of the localized torus. -/
private theorem torusToChart_comp_mutationComplementChartι_eq (h₀ : Nonempty Φ.cones) :
    torusToChart Φ b σ side hs c ≫ Φ.mutationComplementChartι b σ side hs c h =
      Φ.mutationComplementTorusι b c h h₀ :=
  torusToChart_comp_mutationComplementChartι Φ b σ side hs c h _ _ _

/-- Composing the localized torus inclusion with the open immersion into the fan
recovers the ambient localized torus inclusion. -/
@[reassoc (attr := simp)]
theorem mutationComplementTorusι_comp_ι (h₀ : Nonempty Φ.cones) :
    Φ.mutationComplementTorusι b c h h₀ ≫ (U).ι = Φ.mutationTorusι b c h₀ := by
  simp only [mutationComplementTorusι, Category.assoc, mutationComplementChartι_comp_ι]
  exact torusToChart_comp_complementChartToFan Φ b _ false _ c

/-- The localized torus is dense in the complement of the pivot fiber. -/
theorem isDominant_mutationComplementTorusι [IsDomain K] (hv : v ≠ 0) (h₀ : Nonempty Φ.cones) :
    IsDominant (Φ.mutationComplementTorusι b c h h₀) := by
  have : IsDominant (Φ.mutationComplementTorusι b c h h₀ ≫ (U).ι) := by
    rw [mutationComplementTorusι_comp_ι]
    exact isDominant_mutationTorusι Φ b c hv h₀
  exact IsDominant.of_comp_of_isOpenImmersion _ (U).ι

private theorem isDominant_torusToChart_comp_mutationComplementChartι [IsDomain K] (hv : v ≠ 0) :
    IsDominant (torusToChart Φ b σ side hs c ≫ Φ.mutationComplementChartι b σ side hs c h) := by
  have : IsDominant ((torusToChart Φ b σ side hs c ≫
      Φ.mutationComplementChartι b σ side hs c h) ≫ (U).ι) := by
    rw [Category.assoc, mutationComplementChartι_comp_ι, ← complementChartToFan,
      torusToChart_comp_complementChartToFan]
    exact isDominant_mutationTorusι Φ b c hv ⟨σ⟩
  exact IsDominant.of_comp_of_isOpenImmersion _ (U).ι

private theorem mutationComplementChartι_comp_toBase :
    Φ.mutationComplementChartι b σ side hs c h ≫ (U).ι ≫
        Φ.finiteFanSchemeToSpec K =
      Spec.algebraMap K L := by
  rw [mutationComplementChartι_comp_ι_assoc]
  simp only [affineChartι_finiteFanSchemeToSpec, Spec.algebraMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]

variable (hv : v ≠ 0) (hpos : PointedCone.hull ℝ {i v} ∈ Φ.cones)
  (hneg : PointedCone.hull ℝ {i (-v)} ∈ Φ.cones)

local notation "Ψ" => (mutationFan Φ b hv hpos hneg)
local notation "τ(" σ ")" => (mutationFanConeEquiv Φ b hv hpos hneg σ)
local notation "hs'" => (mutationChartCharacter_mem_dualSemigroup_target Φ b hv hpos hneg σ side hs)

private def torusTwist : 𝕋 ≅ 𝕋 :=
  Scheme.Spec.mapIso
    (mutationTorusChartAlgEquiv b (v := v) c).toRingEquiv.toCommRingCatIso.op

private theorem torusTwist_hom :
    (torusTwist b (v := v) c).hom =
      Spec.map (CommRingCat.ofHom
        (mutationTorusChartAlgEquiv b (v := v) c).toAlgHom.toRingHom) :=
  (rfl)

local notation "L'" => Localization.Away (mutationChartBinomial Φ side c
  (Subtype.mk (mutationChartCharacter b (v := v) side) hs'))

private def localizedChartIso : LS ≅ Spec (.of L') :=
  Scheme.Spec.mapIso
    (Φ.mutationChartAlgEquiv b hv hpos hneg σ side hs c).toRingEquiv.toCommRingCatIso.op

private theorem localizedChartIso_hom :
    (localizedChartIso Φ b σ side hs c hv hpos hneg).hom =
      Spec.map (CommRingCat.ofHom
        (Φ.mutationChartAlgEquiv b hv hpos hneg σ side hs c).toAlgHom.toRingHom) :=
  (rfl)

private theorem mutationChartToTorus_eq_mutated :
    let q' : dualSemigroup Φ.lattice (τ(σ)).val := ⟨_, hs'⟩
    mutationChartToTorus Ψ b side c q' rfl = mutationChartToTorus Φ b side c q' rfl := by
  dsimp only
  apply Localization.algHom_ext
  apply (AddMonoidAlgebra.lift K T (dualSemigroup Φ.lattice (τ(σ)).val)).symm.injective
  apply MonoidHom.ext
  intro a
  -- The two chart maps, viewed on unlocalized monomials, use the same exponent inclusion.
  change mutationChartToTorus Ψ b side c ⟨_, hs'⟩ rfl (algebraMap _ _ (single a.toAdd 1)) =
    mutationChartToTorus Φ b side c ⟨_, hs'⟩ rfl (algebraMap _ _ (single a.toAdd 1))
  rw [mutationChartToTorus_single, mutationChartToTorus_single]

private theorem torusToChart_comp_localizedChartIso :
    torusToChart Φ b σ side hs c ≫ (localizedChartIso Φ b σ side hs c hv hpos hneg).hom =
      (torusTwist b (v := v) c).hom ≫ torusToChart Ψ b τ(σ) side hs' c := by
  simp only [torusToChart, localizedChartIso_hom, torusTwist_hom,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  rw [CommRingCat.hom_ofHom, CommRingCat.hom_ofHom,
    mutationChartToTorus_eq_mutated Φ b σ side hs c hv hpos hneg]
  exact congrArg AlgHom.toRingHom
    (mutationChartToTorus_comp_mutationChartAlgEquiv Φ b hv hpos hneg σ side hs c)

private theorem localizedChartIso_hom_comp_toBase :
    (localizedChartIso Φ b σ side hs c hv hpos hneg).hom ≫ Spec.algebraMap K L' =
      Spec.algebraMap K L := by
  simp only [localizedChartIso_hom, Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun (f : K →+* L) ↦ Spec.map (CommRingCat.ofHom f))
    (Φ.mutationChartAlgEquiv b hv hpos hneg σ side hs c).toAlgHom.comp_algebraMap

private abbrev complementCover {J : Type} (e : J → Φ.cones) (he : Function.Surjective e)
    (side : J → Bool)
    (hs : ∀ j, mutationChartCharacter b (v := v) (side j) ∈ dualSemigroup Φ.lattice (e j).val) :
    (U).toScheme.OpenCover where
  I₀ := J
  X j := Spec (.of (Localization.Away
    (Φ.mutationChartBinomial (side j) c ⟨_, hs j⟩)))
  f j := Φ.mutationComplementChartι b (e j) (side j) (hs j) c h
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨σ, y, hy⟩ := Φ.exists_affineChartι_apply_eq K ((U).ι x)
    obtain ⟨j, rfl⟩ := he σ
    have hx : (U).ι x ∈ Set.range (complementChartToFan Φ b (e j) (side j) (hs j) c) := by
      rw [range_complementChartToFan Φ b _ _ _ c h]
      exact ⟨⟨y, hy⟩, x.property⟩
    obtain ⟨w, hw⟩ := hx
    refine ⟨j, w, (U).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, mutationComplementChartι_comp_ι]
    exact hw

include hv hpos hneg in
/-- The ruling character of the pivot is weakly of one sign on each cone of the mutated fan. -/
theorem mutationDetCharacter_nonneg_or_nonpos (θ : (Ψ).cones) :
    (∀ x ∈ θ.val, 0 ≤ (lattice Ψ).realCharacter m x) ∨
    ∀ x ∈ θ.val, (lattice Ψ).realCharacter m x ≤ 0 := by
  obtain ⟨σ, rfl⟩ := (mutationFanConeEquiv Φ b hv hpos hneg).surjective θ
  obtain ⟨side, hs⟩ := Φ.exists_mutationChartCharacter_mem_dualSemigroup b σ
    (Φ.detCharacter_nonneg_or_nonpos b hv hpos hneg σ)
  have ht := (mem_dualSemigroup (lattice Ψ) _).mp
    (Φ.mutationChartCharacter_mem_dualSemigroup_target b hv hpos hneg σ side hs)
  cases side
  · exact Or.inl (by simpa only [mutationChartCharacter_false] using ht)
  · exact Or.inr (by simpa [mutationChartCharacter_true] using ht)

local notation "hp₀" => (detCharacter_nonneg_or_nonpos Φ b hv hpos hneg)
local notation "hp₁" => (mutationDetCharacter_nonneg_or_nonpos Φ b hv hpos hneg)
local notation "U₀" => (mutationComplement Φ b (v := v) hp₀ c)
local notation "U₁" => (mutationComplement Ψ b (v := v) hp₁ c)

private abbrev SignedCone :=
  Σ σ : Φ.cones, {side : Bool //
    mutationChartCharacter b (v := v) side ∈ dualSemigroup Φ.lattice σ.val}

local notation "J" => (SignedCone Φ b (v := v))

include hv hpos hneg in
private theorem signedCone_surjective : Function.Surjective (Sigma.fst : J → Φ.cones) := by
  intro σ
  obtain ⟨s, hs⟩ := Φ.exists_mutationChartCharacter_mem_dualSemigroup b σ (hp₀ σ)
  exact ⟨⟨σ, s, hs⟩, rfl⟩

private def zeroChart : J :=
  ⟨⟨⊥, Φ.bot_mem hpos⟩, false, by simp⟩

local notation "jp" => (zeroChart Φ b hpos)
local notation "ht(" j ")" =>
  (mutationChartCharacter_mem_dualSemigroup_target Φ b hv hpos hneg (Sigma.fst j)
    (Subtype.val (Sigma.snd j)) (Subtype.property (Sigma.snd j)))

private abbrev sourceCover : (U₀).toScheme.OpenCover :=
  complementCover Φ b c hp₀ (Sigma.fst : J → Φ.cones)
    (signedCone_surjective Φ b hv hpos hneg) (fun j ↦ j.snd.val) fun j ↦ j.snd.property

private abbrev targetCover : (U₁).toScheme.OpenCover :=
  complementCover Ψ b c hp₁ (fun j : J ↦ τ(j.fst))
    ((mutationFanConeEquiv Φ b hv hpos hneg).surjective.comp
      (signedCone_surjective Φ b hv hpos hneg)) (fun j ↦ j.snd.val) fun j ↦ ht(j)

local notation "C₀" => (sourceCover Φ b c hv hpos hneg)
local notation "C₁" => (targetCover Φ b c hv hpos hneg)
local notation "E(" j ")" =>
  (localizedChartIso Φ b (Sigma.fst j) (Subtype.val (Sigma.snd j))
    (Subtype.property (Sigma.snd j)) c hv hpos hneg)
local notation "j₀(" j ")" => (torusToChart Φ b (Sigma.fst j) (Subtype.val (Sigma.snd j))
  (Subtype.property (Sigma.snd j)) c)
local notation "j₁(" j ")" =>
  (torusToChart Ψ b τ(Sigma.fst j) (Subtype.val (Sigma.snd j)) ht(j) c)
local notation "t" => (torusTwist b (v := v) c)

private instance isDominant_sourcePivot [IsDomain K] :
    IsDominant (j₀(jp) ≫ (C₀).f jp) :=
  isDominant_torusToChart_comp_mutationComplementChartι Φ b
    (jp).fst (jp).snd.val (jp).snd.property c hp₀ hv

private instance isDominant_targetPivot [IsDomain K] :
    IsDominant (j₁(jp) ≫ (C₁).f jp) :=
  isDominant_torusToChart_comp_mutationComplementChartι Ψ b τ((jp).fst) (jp).snd.val ht(jp) c hp₁ hv

private theorem sourceTorus_agree (j : J) :
    j₀(j) ≫ (C₀).f j = j₀(jp) ≫ (C₀).f jp :=
  torusToChart_comp_mutationComplementChartι Φ b j.fst j.snd.val j.snd.property c hp₀
    (jp).fst (jp).snd.val (jp).snd.property

private theorem targetTorus_agree (j : J) :
    j₁(j) ≫ (C₁).f j = j₁(jp) ≫ (C₁).f jp :=
  torusToChart_comp_mutationComplementChartι Ψ b τ(j.fst) j.snd.val ht(j) c hp₁
    τ((jp).fst) (jp).snd.val ht(jp)

private theorem sourceChart_toBase (j : J) :
    (C₀).f j ≫ (U₀).ι ≫ Φ.finiteFanSchemeToSpec K =
      Spec.algebraMap K
        (Localization.Away (Φ.mutationChartBinomial j.snd.val c ⟨_, j.snd.property⟩)) :=
  mutationComplementChartι_comp_toBase Φ b j.fst j.snd.val j.snd.property c hp₀

private theorem targetChart_toBase (j : J) :
    (C₁).f j ≫ (U₁).ι ≫ (Ψ).finiteFanSchemeToSpec K =
      Spec.algebraMap K (Localization.Away ((Ψ).mutationChartBinomial j.snd.val c ⟨_, ht(j)⟩)) :=
  mutationComplementChartι_comp_toBase Ψ b τ(j.fst) j.snd.val ht(j) c hp₁

variable [IsDomain K]

private instance (h : ∀ σ : Φ.cones,
    (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0) :
    IsReduced (Φ.mutationComplement b h c).toScheme :=
  isReduced_of_isOpenImmersion (Φ.mutationComplement b h c).ι

private def mutationComplementHom : (U₀).toScheme ⟶ (U₁).toScheme := by
  refine (C₀).glueMorphismsOfDominant (j₀(jp) ≫ (C₀).f jp) (fun j ↦ j₀(j))
    (sourceTorus_agree Φ b c hv hpos hneg)
    (fun j ↦ E(j).hom ≫ (C₁).f j) ((t).hom ≫ j₁(jp) ≫ (C₁).f jp) (fun j ↦ ?_)
    ((U₁).ι ≫ (Ψ).finiteFanSchemeToSpec K)
    ((U₀).ι ≫ Φ.finiteFanSchemeToSpec K) (fun j ↦ ?_)
  · let a : J := j
    -- Expand the cover member's scheme via the chosen signed cone.
    change j₀(a) ≫ E(a).hom ≫ (C₁).f a = _
    rw [← Category.assoc j₀(a),
      torusToChart_comp_localizedChartIso Φ b a.fst a.snd.val a.snd.property c hv hpos hneg,
      Category.assoc, targetTorus_agree Φ b c hv hpos hneg a]
  · let a : J := j
    -- Use the localized chart scheme to read both structure maps.
    change (E(a).hom ≫ (C₁).f a) ≫ _ = (C₀).f a ≫ _
    rw [Category.assoc, targetChart_toBase Φ b c hv hpos hneg a,
      sourceChart_toBase Φ b c hv hpos hneg a]
    exact localizedChartIso_hom_comp_toBase Φ b a.fst a.snd.val a.snd.property c hv hpos hneg

private theorem sourceCover_f_mutationComplementHom (j : J) :
    (C₀).f j ≫ mutationComplementHom Φ b c hv hpos hneg = E(j).hom ≫ (C₁).f j := by
  unfold mutationComplementHom
  apply Scheme.Cover.ι_glueMorphismsOfDominant

private def mutationComplementInv : (U₁).toScheme ⟶ (U₀).toScheme := by
  refine (C₁).glueMorphismsOfDominant (j₁(jp) ≫ (C₁).f jp) (fun j ↦ j₁(j))
    (targetTorus_agree Φ b c hv hpos hneg)
    (fun j ↦ E(j).inv ≫ (C₀).f j) ((t).inv ≫ j₀(jp) ≫ (C₀).f jp) (fun j ↦ ?_)
    ((U₀).ι ≫ Φ.finiteFanSchemeToSpec K)
    ((U₁).ι ≫ (Ψ).finiteFanSchemeToSpec K) (fun j ↦ ?_)
  · let a : J := j
    have ht : j₁(a) ≫ E(a).inv = (t).inv ≫ j₀(a) := by
      rw [Iso.comp_inv_eq, Category.assoc, torusToChart_comp_localizedChartIso,
        Iso.inv_hom_id_assoc]
    -- Expand the cover member's scheme via the chosen signed cone.
    change j₁(a) ≫ E(a).inv ≫ (C₀).f a = _
    rw [← Category.assoc j₁(a), ht, Category.assoc, sourceTorus_agree Φ b c hv hpos hneg a]
  · let a : J := j
    -- Use the localized chart scheme to read both structure maps.
    change (E(a).inv ≫ (C₀).f a) ≫ _ = (C₁).f a ≫ _
    rw [Category.assoc, sourceChart_toBase Φ b c hv hpos hneg a,
      targetChart_toBase Φ b c hv hpos hneg a, Iso.inv_comp_eq]
    exact (localizedChartIso_hom_comp_toBase Φ b a.fst a.snd.val a.snd.property c hv hpos hneg).symm

private theorem targetCover_f_mutationComplementInv (j : J) :
    (C₁).f j ≫ mutationComplementInv Φ b c hv hpos hneg = E(j).inv ≫ (C₀).f j := by
  unfold mutationComplementInv
  apply Scheme.Cover.ι_glueMorphismsOfDominant

/-- Toric mutation is an isomorphism on the two complements of the pivot fiber. -/
def mutationComplementIso : (U₀).toScheme ≅ (U₁).toScheme where
  hom := mutationComplementHom Φ b c hv hpos hneg
  inv := mutationComplementInv Φ b c hv hpos hneg
  hom_inv_id := by
    apply (C₀).hom_ext
    intro j
    let a : J := j
    -- Use the common cone index to compare the two local inverses.
    change (C₀).f a ≫ _ ≫ _ = (C₀).f a ≫ 𝟙 _
    rw [← Category.assoc, sourceCover_f_mutationComplementHom Φ b c hv hpos hneg a,
      Category.assoc, targetCover_f_mutationComplementInv Φ b c hv hpos hneg a,
      Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    apply (C₁).hom_ext
    intro j
    let a : J := j
    -- Use the common cone index to compare the two local inverses.
    change (C₁).f a ≫ _ ≫ _ = (C₁).f a ≫ 𝟙 _
    rw [← Category.assoc, targetCover_f_mutationComplementInv Φ b c hv hpos hneg a,
      Category.assoc, sourceCover_f_mutationComplementHom Φ b c hv hpos hneg a,
      Iso.inv_hom_id_assoc, Category.comp_id]

/-- In every localized cone chart, the global isomorphism is induced by the chart's
mutation algebra equivalence. This includes both signs when both are regular. -/
@[reassoc]
theorem mutationComplementChartι_comp_mutationComplementIso_hom :
    Φ.mutationComplementChartι b σ side hs c hp₀ ≫
        (Φ.mutationComplementIso b c hv hpos hneg).hom =
      Spec.map (CommRingCat.ofHom
        (Φ.mutationChartAlgEquiv b hv hpos hneg σ side hs c).toAlgHom.toRingHom) ≫
        (Ψ).mutationComplementChartι b τ(σ) side hs' c hp₁ := by
  simpa only [mutationComplementIso, localizedChartIso_hom] using
    sourceCover_f_mutationComplementHom Φ b c hv hpos hneg (⟨σ, side, hs⟩ : J)

/-- On the dense torus with the pivot binomial inverted, the complement
isomorphism is induced by the mutation binomial twist. -/
@[reassoc]
theorem mutationComplementTorusι_comp_mutationComplementIso_hom
    (hs₀ : Nonempty Φ.cones) (hs₁ : Nonempty (Ψ).cones) :
    Φ.mutationComplementTorusι b c hp₀ hs₀ ≫ (Φ.mutationComplementIso b c hv hpos hneg).hom =
      Spec.map (CommRingCat.ofHom
        (mutationTorusChartAlgEquiv b (v := v) c).toAlgHom.toRingHom) ≫
        (Ψ).mutationComplementTorusι b c hp₁ hs₁ := by
  rw [← torusTwist_hom]
  rw [← torusToChart_comp_mutationComplementChartι_eq Φ b (jp).fst (jp).snd.val
    (jp).snd.property c hp₀ hs₀, Category.assoc,
    mutationComplementChartι_comp_mutationComplementIso_hom, ← localizedChartIso_hom,
    ← Category.assoc, torusToChart_comp_localizedChartIso, Category.assoc,
    torusToChart_comp_mutationComplementChartι_eq]

/-- The toric mutation isomorphism on the fiber complements is over the coefficient domain. -/
@[reassoc]
theorem mutationComplementIso_hom_comp_toBase :
    (Φ.mutationComplementIso b c hv hpos hneg).hom ≫ (U₁).ι ≫
        (Ψ).finiteFanSchemeToSpec K =
      (U₀).ι ≫ Φ.finiteFanSchemeToSpec K := by
  apply (C₀).hom_ext
  intro j
  let a : J := j
  -- Use the localized chart schemes to compare the two structure maps.
  change (C₀).f a ≫ _ ≫ _ = (C₀).f a ≫ _
  rw [← Category.assoc ((C₀).f a), mutationComplementIso,
    sourceCover_f_mutationComplementHom Φ b c hv hpos hneg a, Category.assoc,
    targetChart_toBase Φ b c hv hpos hneg a, sourceChart_toBase Φ b c hv hpos hneg a]
  exact localizedChartIso_hom_comp_toBase Φ b a.fst a.snd.val a.snd.property c hv hpos hneg

omit [IsDomain K] in
include h in
private theorem range_mutationComplementChartι :
    Set.range (Φ.mutationComplementChartι b σ side hs c h) =
      (U).ι ⁻¹' Set.range (Φ.affineChartι K σ) := by
  have hι : Function.Injective ((U).ι) := (U).ι.isOpenEmbedding.injective
  apply hι.image_injective
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
    mutationComplementChartι_comp_ι,
    ← complementChartToFan, range_complementChartToFan,
    Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]

/-- The mutation isomorphism on the fiber complement identifies its intersections with
the dense tori of the two fans. -/
theorem mutationComplementIso_preimage_range_denseTorusι
    (hΦ : Nonempty Φ.cones) (hΨ : Nonempty (Ψ).cones) :
    ((Φ.mutationComplementIso b c hv hpos hneg).hom ≫ (U₁).ι) ⁻¹'
        Set.range (zeroι[Ψ, hΨ]) =
      (U₀).ι ⁻¹' Set.range (zeroι[Φ, hΦ]) := by
  let j := zeroChart Φ b hpos
  have hzero : (τ(j.fst)).val = ⊥ := by
    apply SetLike.coe_injective
    rw [coe_mutationFanConeEquiv]
    dsimp only [j, zeroChart]
    -- The zero cone is the singleton at the origin in the ambient space.
    change Φ.lattice.mutationRayEquiv b v '' ({0} : Set V) = {0}
    rw [Set.image_singleton]
    simp [IsIntegralLattice.mutationRayEquiv_apply]
  have h₀ : Set.range (Φ.affineChartι K j.fst) = Set.range (zeroι[Φ, hΦ]) := by
    rfl
  have h₁ : Set.range ((Ψ).affineChartι K τ(j.fst)) =
      Set.range (zeroι[Ψ, hΨ]) := by
    have hb : (⊥ : PointedCone ℝ V) ∈ (Ψ).cones := hzero ▸ (τ(j.fst)).property
    have hj : τ(j.fst) = ⟨⊥, hb⟩ := Subtype.ext hzero
    rw [hj]
  let e := Φ.mutationComplementIso b c hv hpos hneg
  let f := Φ.mutationComplementChartι b j.fst j.snd.val j.snd.property c hp₀
  let g := (Ψ).mutationComplementChartι b τ(j.fst) j.snd.val ht(j) c hp₁
  have hr₀ : Set.range f = (U₀).ι ⁻¹' Set.range (zeroι[Φ, hΦ]) :=
    (range_mutationComplementChartι Φ b j.fst j.snd.val j.snd.property c hp₀).trans
      (congrArg (Set.preimage (U₀).ι) h₀)
  have hr₁ : Set.range g = (U₁).ι ⁻¹' Set.range (zeroι[Ψ, hΨ]) :=
    (range_mutationComplementChartι Ψ b τ(j.fst) j.snd.val ht(j) c hp₁).trans
      (congrArg (Set.preimage (U₁).ι) h₁)
  have he : Set.range (f ≫ e.hom) = Set.range g := by
    rw [mutationComplementChartι_comp_mutationComplementIso_hom, ← localizedChartIso_hom]
    simp only [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp_of_isIso, g]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, ← hr₀, ← hr₁, ← he,
    Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.preimage_image_eq _ e.hom.isOpenEmbedding.injective]

end Torus

variable {Φ} [IsDomain K] in
/-- On the complement of the pivot fiber, mutation identifies the reduced boundary ideals. -/
theorem comap_boundaryIdeal_mutationComplementIso
    {v : N} (hv : v ≠ 0) (hpos : PointedCone.hull ℝ {i v} ∈ Φ.cones)
    (hneg : PointedCone.hull ℝ {i (-v)} ∈ Φ.cones) (c : Kˣ) (hΦ : Nonempty Φ.cones)
    (hΨ : Nonempty (Φ.mutationFan b hv hpos hneg).cones) :
    ((Φ.mutationFan b hv hpos hneg).toricBoundaryIdeal K hΨ).comap
      ((Φ.mutationComplementIso b (c : K) hv hpos hneg).hom ≫
        (mutationComplement (Φ.mutationFan b hv hpos hneg) b
          (Φ.mutationDetCharacter_nonneg_or_nonpos b hv hpos hneg) (c : K)).ι) =
      (Φ.toricBoundaryIdeal K hΦ).comap
        (Φ.mutationComplement b (Φ.detCharacter_nonneg_or_nonpos b hv hpos hneg) (c : K)).ι := by
  rw [toricBoundaryIdeal_def K, toricBoundaryIdeal_def K,
    Scheme.IdealSheafData.comap_vanishingIdeal_of_isOpenImmersion,
    Scheme.IdealSheafData.comap_vanishingIdeal_of_isOpenImmersion]
  congr 1
  apply TopologicalSpace.Closeds.ext
  exact congrArg Set.compl
    (Φ.mutationComplementIso_preimage_range_denseTorusι b (c : K) hv hpos hneg hΦ hΨ)

end TauCeti.Toric.Fan

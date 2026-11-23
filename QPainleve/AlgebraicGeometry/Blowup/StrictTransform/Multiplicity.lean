/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic
public import QPainleve.AlgebraicGeometry.IdealSheaf.RegularPair
public import TauCeti.AlgebraicGeometry.Blowup.AffineCharts
public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
public import TauCeti.AlgebraicGeometry.CartierDivisor.IdealSheaf
public import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.RingTheory.Ideal.AssociatedGraded
import Mathlib.AlgebraicGeometry.FunctionField
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Multiplicity
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.RingTheory.Ideal.AffineBlowup.StrictTransform
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.RingTheory.Ideal.Order
import TauCeti.RingTheory.Regular.AssociatedGraded

/-!
# Total and strict transforms of divisors

On an order-one affine chart the total-transform ideal of a hypersurface is its
strict-transform ideal times the exceptional ideal to the order of the local equation.
The comparison uses Tau Ceti's schematic closure theorem for the strict-transform morphism
([The Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)).
For the blowup of a regular closed point of local dimension two, the chart formulas
give a global equality with exceptional exponent equal to the stalk order.
-/

public section

open CategoryTheory Limits TopologicalSpace
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

open RingTheory.Sequence in
/-- A weakly regular pair around the whole center gives the total-transform formula on the
blowup. The remainder of the blowup lies in the exceptional complement. -/
theorem totalTransform_eq_strictTransform_mul_pow_of_affine {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (U : X.affineOpens) (hU : (I.support : Set X) ⊆ U.val)
    {a b f : Γ(X, U)} (hI : Ideal.span {a, b} = I.ideal U) [(I.ideal U).IsPrime]
    (hab : IsWeaklyRegular Γ(X, U) [a, b]) (hba : IsWeaklyRegular Γ(X, U) [b, a])
    (hJ : J.ideal U = Ideal.span {f}) {n : ℕ}
    (hf : f ∈ I.ideal U ^ n) (hf' : f ∉ I.ideal U ^ (n + 1)) :
    J.comap I.blowupToBase =
      (I.blowupMap J.subschemeι).ker * (I.comap I.blowupToBase) ^ n := by
  let P := I.ideal U
  have hList : Ideal.ofList [a, b] = P := by simpa [Ideal.span_insert] using hI
  let e := hab.associatedGradedEquiv hList
  have : IsDomain P.AssociatedGraded := e.toMulEquiv.isDomain_iff.mp inferInstance
  have hOrder (i : Fin ([a, b] : List Γ(X, U)).length) :
      ([a, b] : List Γ(X, U))[i.val] ∉ P ^ 2 := by
    intro h
    apply MvPolynomial.X_ne_zero (R := Γ(X, U) ⧸ P) i
    apply e.injective
    rw [map_zero, hab.associatedGradedEquiv_X hList]
    exact (Ideal.AssociatedGraded.mk_eq_zero_iff _).mpr h
  let s (i : Bool) := cond i a b
  have hs : Ideal.span (Set.range s) = P := by
    simpa [s, Bool.range_eq, Set.pair_comm] using hI
  have hsOrder (i : Bool) : s i ∉ P ^ 2 := by
    cases i
    · exact hOrder 1
    · exact hOrder 0
  have hsReg (i : Bool) : s i ∈ nonZeroDivisors Γ(X, U) := by
    cases i
    · exact (isLeftRegular_iff_isRegular.mp
        ((isWeaklyRegular_cons_iff _ _ _).mp hba).1.isLeftRegular).mem_nonZeroDivisors
    · exact (isLeftRegular_iff_isRegular.mp
        ((isWeaklyRegular_cons_iff _ _ _).mp hab).1.isLeftRegular).mem_nonZeroDivisors
  let E := I.comap I.blowupToBase
  let W : I.blowup.Opens := E.support.compl
  let hAff : IsAffineOpen U.val := U.property
  let C : I.blowup.OpenCover := Scheme.Cover.mkOfCovers Bool
    (fun i ↦ cond i (Proj (reesAlgebra.grade P)) W.toScheme)
    (fun i ↦ match i with
    | false => W.ι
    | true => I.blowupChart hAff)
    (by
      intro y
      by_cases hy : y ∈ W
      · exact ⟨false, ⟨y, hy⟩, rfl⟩
      · refine ⟨true, ?_⟩
        change y ∈ Set.range (I.blowupChart hAff)
        rw [← Scheme.Hom.coe_opensRange, I.opensRange_blowupChart]
        apply hU
        have hyE : y ∈ (E.support : Set I.blowup) := by
          by_contra h
          exact hy h
        rwa [support_comap, Closeds.coe_preimage] at hyE)
    (by
      rintro (_ | _)
      · exact inferInstanceAs (IsOpenImmersion W.ι)
      · exact inferInstanceAs (IsOpenImmersion (I.blowupChart hAff)))
  refine ext_of_comap_openCover C fun i ↦ ?_
  rw [comap_mul, comap_pow]
  cases i with
  | false =>
    have hW : E.comap W.ι = ⊤ :=
      (comap_eq_top_iff _ _).mpr (Scheme.Opens.ι_preimage_self W)
    change (J.comap I.blowupToBase).comap W.ι =
      (I.blowupMap J.subschemeι).ker.comap W.ι * (E.comap W.ι) ^ n
    rw [hW, ← one_eq_top, one_pow, mul_one, comap_ker_blowupMap_subschemeι_exceptionalCompl]
  | true =>
    change (J.comap I.blowupToBase).comap (I.blowupChart hAff) =
      (I.blowupMap J.subschemeι).ker.comap (I.blowupChart hAff) *
        (E.comap (I.blowupChart hAff)) ^ n
    rw [mul_comm, ← comap_comp, ← comap_comp]
    exact I.comap_eq_pow_mul_ker_blowupMap_on_blowupChart J hAff s hs hsOrder hsReg hJ hf hf'

open RingTheory.Sequence in
/-- The total transform of an effective Cartier divisor under a blowup of a regular
closed point of local dimension two is its strict transform plus its multiplicity at
the point times the exceptional divisor. The equality is on the actual ideal sheaves. -/
theorem IsEffectiveCartier.totalTransform_eq_strictTransform_mul_pow_closedPoint
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X] {p : X}
    [IsRegularLocalRing (X.presheaf.stalk p)] {J : X.IdealSheafData}
    (hJ : J.IsEffectiveCartier) (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) :
    let I := vanishingIdeal (Closeds.mk (closure {p}) isClosed_closure)
    J.comap I.blowupToBase =
      (I.blowupMap J.subschemeι).ker * (I.comap I.blowupToBase) ^ (J.stalkOrder p).toNat := by
  let I := vanishingIdeal (Closeds.mk (closure {p}) isClosed_closure)
  obtain ⟨V, -, hpV, f₀, hreg₀, hf₀⟩ := hJ.exists_eq_span_singleton_le ⊤ (Opens.mem_top p)
  obtain ⟨U, hpU, hUV, a, b, hab, hreg, hswap⟩ :=
    exists_mem_le_span_pair_vanishingIdeal_closure_singleton hdim hpV
  let f : Γ(X, U) := X.presheaf.map (homOfLE hUV).op f₀
  have hf : J.ideal U = Ideal.span {f} := J.ideal_eq_span_singleton_of_le hUV hf₀
  have hsupport : (I.support : Set X) ⊆ U.val := by
    rw [coe_support_vanishingIdeal, Closeds.coe_mk, hp.closure_eq]
    exact Set.singleton_subset_iff.mpr hpU
  let P := (U.property.primeIdealOf ⟨p, hpU⟩).asIdeal
  have hIP : I.ideal U = P := vanishingIdeal_closure_singleton_ideal p U hpU
  let : P.IsMaximal := U.property.primeIdealOf_isMaximal_of_isClosed ⟨p, hpU⟩ hp
  have hPrime : (I.ideal U).IsPrime := hIP.symm ▸ (inferInstance : P.IsPrime)
  have hord : J.stalkOrder p ≠ ⊤ := by
    let : Nonempty V.val := ⟨⟨p, hpV⟩⟩
    have hf₀_ne : f₀ ≠ 0 := fun he ↦
      one_ne_zero (hreg₀ (by simp [he]) : (1 : Γ(X, V)) = 0)
    have hgerm : X.presheaf.germ V.val p hpV f₀ ≠ 0 := fun he ↦
      hf₀_ne (germ_injective_of_isIntegral X p hpV (he.trans (map_zero _).symm))
    rw [J.stalkOrder_def, ne_eq, Ideal.localOrder_eq_top_iff_eq_bot,
      J.stalkIdeal_eq_map V p hpV, hf₀, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_eq_bot]
    exact hgerm
  let n := (J.stalkOrder p).toNat
  have hn : (n : ℕ∞) = J.stalkOrder p := ENat.natCast_toNat hord
  have hpow (m : ℕ) : f ∈ I.ideal U ^ m ↔ (m : ℕ∞) ≤ J.stalkOrder p := by
    have he : (IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ m).comap
        (algebraMap Γ(X, U) (Localization.AtPrime P)) = P ^ m :=
      IsLocalization.AtPrime.under_maximalIdeal_pow P (Localization.AtPrime P) m
    rw [J.stalkOrder_eq_orderAt U p hpU, Ideal.natCast_le_orderAt_iff, hIP,
      Ideal.map_le_iff_le_comap, he, hf, Ideal.span_singleton_le_iff_mem]
  refine totalTransform_eq_strictTransform_mul_pow_of_affine I J U hsupport hab hreg hswap hf
    ((hpow n).mpr hn.le) (fun hm ↦ ?_)
  have hle := (hpow (n + 1)).mp hm
  rw [← hn] at hle
  exact (Nat.not_succ_le_self n) (by exact_mod_cast hle)

variable {X : Scheme.{u}} {p : X} [IsIntegral X] [IsLocallyNoetherian X]
  [IsRegularLocalRing (X.presheaf.stalk p)] {D : X.IdealSheafData}

local notation "Iₚ" => vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
local notation "B" => blowup Iₚ
local notation "π" => blowupToBase Iₚ
local notation "E" => Scheme.IdealSheafData.comap Iₚ π
local notation "hE" => isEffectiveCartier_comap_blowupToBase Iₚ
local notation "S" => Scheme.Hom.ker (blowupMap Iₚ D.subschemeι)
local notation "m" => ENat.toNat (D.stalkOrder p)

/-- Removing the exceptional power of the exact multiplicity from the total transform
gives the ideal of the scheme-theoretic strict transform. -/
theorem IsEffectiveCartier.comap_blowupToBase_colon_eq_strictTransform
    (hD : D.IsEffectiveCartier) (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) :
    (D.comap π).colon (E ^ m) = S := by
  have hsplit : D.comap π = S * E ^ m :=
    hD.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hdim
  rw [hsplit, (TauCeti.isEffectiveCartier_pow hE m).mul_colon_cancel_right]

/-- The total transform of an effective Cartier divisor under the blowup of a regular
closed point of local dimension two is the strict transform plus the stalk order
times the exceptional divisor. The strict transform is effective Cartier and its
support omits every codimension-one point of the exceptional divisor. -/
theorem IsEffectiveCartier.exists_strictTransform_cartierDivisor [IsIntegral B]
    (hD : D.IsEffectiveCartier) (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (hT : (D.comap π).IsEffectiveCartier) :
    ∃ hS : (S).IsEffectiveCartier,
      hT.toCartierDivisor = hS.toCartierDivisor + m • (hE).toCartierDivisor ∧
        ∀ x : CodimensionOnePoint B, (x : B) ∈ (E).support → (x : B) ∉ (S).support := by
  let hF := TauCeti.isEffectiveCartier_pow hE m
  have hsplit : D.comap π = S * E ^ m :=
    hD.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hdim
  have hle : D.comap π ≤ E ^ m := by
    rw [hsplit]
    exact fun U ↦ by
      simpa only [ideal_mul, Pi.mul_apply] using Ideal.mul_le_right
  have hres := hD.comap_blowupToBase_colon_eq_strictTransform hp hdim
  let hS : (S).IsEffectiveCartier :=
    Eq.mp (congrArg Scheme.IdealSheafData.IsEffectiveCartier hres)
      (hT.colon hF.locallyPrincipal hle)
  refine ⟨hS, ?_, ?_⟩
  · calc
      _ = (TauCeti.isEffectiveCartier_mul hS hF).toCartierDivisor :=
        (hT.toCartierDivisor_eq_iff _).mpr hsplit
      _ = _ := by rw [toCartierDivisor_mul hS hF, toCartierDivisor_pow]
  · have hm : (m : ℕ∞) = D.stalkOrder p := by
      refine ENat.natCast_toNat ?_
      rw [D.stalkOrder_def, ne_eq, Ideal.localOrder_eq_top_iff_eq_bot]
      exact hD.stalkIdeal_ne_bot p
    have hP : Iₚ = (X.fromSpecResidueField p).ker :=
      (X.ker_fromSpecResidueField_eq_vanishingIdeal p).symm
    rw [← hres, hP]
    exact fun x hx ↦ notMem_support_colon_exceptional_of_mem_exceptional p hp hdim D m hm.symm x hx

end AlgebraicGeometry.Scheme.IdealSheafData

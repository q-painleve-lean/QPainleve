/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.LineBundle.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import QPainleve.AlgebraicGeometry.Blowup.PointCohomology
import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.Cohomology.ProjectiveSpace.EulerCharacteristic
import QPainleve.AlgebraicGeometry.Cohomology.Support
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.NegativeTwist
import TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.LineBundle.LocalRing
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Euler characteristics of exceptional twists at a point blowup

The restriction of `π*L(mE)` to the exceptional line is a twist of degree `-m`.
The actual Cartier ideal sequence gives the Euler characteristic recurrence in both
directions from the untwisted cohomology comparison. This is the local contribution
of a blowup to Riemann–Roch on a surface.

The argument uses the Cartier sequence
`Scheme.IdealSheafData.shortExact_tensor_toPushforwardSubscheme` and its projection
formula `tensorPushforwardSubschemeIso` from Tau Ceti. The restriction and connecting maps
are those of this tensor Cartier sequence.
-/

public section

open CategoryTheory Limits TopologicalSpace MonoidalCategory
open TauCeti.AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} (p : X)

local notation "Iₚ" => Scheme.Hom.ker (Scheme.fromSpecResidueField X p)
local notation "Y" => blowup Iₚ
local notation "π" => blowupToBase Iₚ
local notation "E" => comap Iₚ π
local notation "ι" => subschemeι E
local notation "𝒥" =>
  IsEffectiveCartier.toInvertibleSheaf (isEffectiveCartier_comap_blowupToBase Iₚ)
local notation:max "twist[" a ", " m "]" =>
  (LineBundleClass.pullback π a * (LineBundleClass.mk 𝒥) ^ (-m : ℤ))

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

private noncomputable local instance : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩

local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k)
local notation "𝒪" => Proj.twistingSheaf 𝒜

/-- On the exceptional divisor over a rational regular point of local dimension two, the
restriction of the pullback of a line bundle twisted by `mE` is isomorphic to `𝒪(-m)` under the
exceptional projective-line identification. The same projective-line isomorphism works for all
line bundles and all integers `m`. -/
theorem exists_iso_projectiveLine_pullback_pointBlowup_exceptional_twist
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hrat : IsIso (X.fromSpecResidueField p ≫ (X ↘ Spec (.of k)))) :
    ∃ e : projectiveLine k ≅ (E).subscheme,
      e.hom ≫ ι ≫ π ≫ (X ↘ Spec (.of k)) = (projectiveLine k ↘ Spec (.of k)) ∧
      ∀ (a : LineBundleClass X) (m : ℤ) (M : InvertibleSheaf Y),
        LineBundleClass.mk M = twist[a, m] →
        Nonempty (((InvertibleSheaf.pullback (e.hom ≫ ι)).obj M).obj ≅ 𝒪 (-m)) := by
  let κ := X.residueField p
  let c := X.fromSpecResidueField p ≫ (X ↘ Spec (.of k))
  let : Algebra k κ := (Spec.preimage c).hom.toAlgebra
  have hc : Spec.map (CommRingCat.ofHom (algebraMap k κ)) = c := Spec.map_preimage c
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k κ))) := hc.symm ▸ hrat
  let b := projectiveLine.baseChangeProjection k κ
  have hb := projectiveLine.isPullback_baseChangeProjection k κ
  have : IsIso b := hb.isIso_fst_of_isIso
  obtain ⟨eκ, heκ, hconormal, -⟩ :=
    exists_iso_projectiveLine_pullback_exceptionalIdeal_of_closedPoint p hp hdim
  let e := (asIso b).symm ≪≫ eκ
  have he : b ≫ e.hom = eκ.hom := by simp [e]
  have hκ : eκ.hom ≫ ι ≫ π ≫ (X ↘ Spec (.of k)) =
      b ≫ (projectiveLine k ↘ Spec (.of k)) := by
    rw [hb.w, hc]
    simpa only [Category.assoc, c] using
      congrArg (· ≫ (X ↘ Spec (.of k))) heκ.w
  refine ⟨e, (cancel_epi b).mp (by simpa only [← Category.assoc, he] using hκ), ?_⟩
  intro a m M hM
  let d := LineBundleClass.pullback (e.hom ≫ ι) (LineBundleClass.mk 𝒥)
  have hd : LineBundleClass.eulerDegree k d = 1 := by
    rw [← LineBundleClass.eulerDegree_pullback hb d, LineBundleClass.pullback_comp,
      ← Category.assoc, he, LineBundleClass.pullback_mk, LineBundleClass.eulerDegree_mk]
    exact (projectiveLine.nonempty_iso_twistingSheaf_iff κ _ 1).mp hconormal
  have ha : LineBundleClass.pullback (e.hom ≫ ι) (LineBundleClass.pullback π a) = 1 := by
    have hef : (e.hom ≫ ι) ≫ π =
        ((asIso b).inv ≫ (projectiveLine κ ↘ Spec (.of κ))) ≫ X.fromSpecResidueField p := by
      dsimp only [e, Iso.trans_hom, Iso.symm_hom]
      simpa only [Category.assoc] using congrArg ((asIso b).inv ≫ ·) heκ.w
    rw [LineBundleClass.pullback_comp, hef, ← LineBundleClass.pullback_comp]
    have ht : LineBundleClass.pullback (X.fromSpecResidueField p) a = 1 :=
      Subsingleton.elim _ _
    rw [ht, LineBundleClass.pullback_one]
  let : Fact (∀ x : projectiveLine k, Order.coheight x ≤ 1) :=
    ⟨Scheme.IsCurveOver.coheight_le_one (k := k)⟩
  apply (projectiveLine.nonempty_iso_twistingSheaf_iff k _ (-m)).mpr
  rw [← LineBundleClass.eulerDegree_mk, ← LineBundleClass.pullback_mk, hM,
    LineBundleClass.pullback_mul, ha, one_mul, LineBundleClass.pullback_zpow,
    LineBundleClass.eulerDegree_zpow, hd, mul_one]

/-- The Cartier quotient of the exceptional twist has the cohomology of `𝒪(-m)` on the
exceptional projective line, as vector spaces over the base field. -/
theorem nonempty_cohomologyLinearEquiv_pointBlowup_exceptional_quotient
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hrat : IsIso (X.fromSpecResidueField p ≫ (X ↘ Spec (.of k))))
    (a : LineBundleClass X) (m : ℤ) (M : InvertibleSheaf Y)
    (hM : LineBundleClass.mk M = twist[a, m]) (q : ℕ) :
    let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    Nonempty (Cohomology (M.obj ⊗ (E).pushforwardSubscheme) q ≃ₗ[k]
      Cohomology (𝒪 (-m)) q) := by
  obtain ⟨e, he, htwist⟩ :=
    exists_iso_projectiveLine_pullback_pointBlowup_exceptional_twist p k hp hdim hrat
  let : e.hom.IsOver (Spec (.of k)) := ⟨he⟩
  obtain ⟨t⟩ := htwist a m M hM
  let F := (InvertibleSheaf.toFiniteLocallyFree Y).obj M
  let N := (Scheme.Modules.pullback ι).obj M.obj
  have hF : F.obj = M.obj := ObjectProperty.ιOfLE_obj_obj _ _
  have hN : ((FiniteLocallyFreeSheaf.pullback ι).obj F).obj = N := by
    rw [FiniteLocallyFreeSheaf.pullback_obj_obj, hF]
  let qIso : M.obj ⊗ (E).pushforwardSubscheme ≅ (Scheme.Modules.pushforward ι).obj N :=
    eqToIso (congrArg (· ⊗ (E).pushforwardSubscheme) hF.symm) ≪≫
      (E).tensorPushforwardSubschemeIso F ≪≫ (Scheme.Modules.pushforward ι).mapIso (eqToIso hN)
  exact ⟨(cohomologyBaseLinearEquivOfIso k qIso q).trans <|
    (Scheme.Hom.cohomologyPushforwardBaseLinearEquiv ι k N q).trans <|
    (e.hom.cohomologyPullbackBaseLinearEquivOfIsIso k N q).symm.trans <|
    (cohomologyBaseLinearEquivOfIso k ((Scheme.Modules.pullbackComp e.hom ι).app M.obj) q)
      |>.trans (cohomologyBaseLinearEquivOfIso k t q)⟩

/-- Tensoring the `mE` twist by the exceptional ideal gives the preceding twist.
This identifies the first term of the actual tensor Cartier sequence. -/
theorem exists_iso_tensor_exceptional_ideal_pointBlowup_twist
    (a : LineBundleClass X) (m : ℤ) {L M : InvertibleSheaf Y}
    (hL : LineBundleClass.mk L = twist[a, m - 1])
    (hM : LineBundleClass.mk M = twist[a, m]) :
    Nonempty (L.obj ≅ M.obj ⊗ (E).sheaf) := by
  have h : LineBundleClass.mk L = LineBundleClass.mk (M.tensorProduct 𝒥) := by
    rw [LineBundleClass.mk_tensorProduct, hL, hM, mul_assoc, ← zpow_add_one]
    congr 2
    omega
  obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.mp h
  exact ⟨e ≪≫ InvertibleSheaf.tensorProductObjIso _ _ ≪≫
    (tensorLeft M.obj).mapIso
      (eqToIso (isEffectiveCartier_comap_blowupToBase Iₚ).toInvertibleSheaf_obj)⟩

private theorem pointBlowup_exceptional_twist_cohomology_step
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hrat : IsIso (X.fromSpecResidueField p ≫ (X ↘ Spec (.of k))))
    (a : LineBundleClass X) (m : ℤ) {L M : InvertibleSheaf Y}
    (hL : LineBundleClass.mk L = twist[a, m - 1])
    (hM : LineBundleClass.mk M = twist[a, m]) :
    (∀ q, FiniteDimensional k (Cohomology L.obj q) ∧
      (2 < q → Subsingleton (Cohomology L.obj q))) ↔
    (∀ q, FiniteDimensional k (Cohomology M.obj q) ∧
      (2 < q → Subsingleton (Cohomology M.obj q))) := by
  let S := (ShortComplex.mk _ _ (E).sheafι_toPushforwardSubscheme).map (tensorLeft M.obj)
  have hS : S.ShortExact := (E).shortExact_tensor_toPushforwardSubscheme M.obj
  obtain ⟨e₁⟩ := exists_iso_tensor_exceptional_ideal_pointBlowup_twist p a m hL hM
  let e₂ := ρ_ M.obj
  let c₁ (q : ℕ) : Cohomology L.obj q ≃ₗ[k] Cohomology S.X₁ q :=
    cohomologyBaseLinearEquivOfIso k e₁ q
  let c₂ (q : ℕ) : Cohomology S.X₂ q ≃ₗ[k] Cohomology M.obj q :=
    cohomologyBaseLinearEquivOfIso k e₂ q
  have h₃ q : FiniteDimensional k (Cohomology S.X₃ q) ∧
      (1 < q → Subsingleton (Cohomology S.X₃ q)) := by
    obtain ⟨e⟩ :=
      nonempty_cohomologyLinearEquiv_pointBlowup_exceptional_quotient p k hp hdim hrat a m M hM q
    have := (Pi.basisFun k (Fin 2)).finite_cohomology_twistingSheaf (-m) q
    refine ⟨Module.Finite.equiv e.symm, fun hq ↦ ?_⟩
    have := (Pi.basisFun k (Fin 2)).subsingleton_cohomology_proj_of_card_le
      (𝒪 (-m)) q (by simp only [Fintype.card_fin]; omega)
    exact e.injective.subsingleton
  constructor
  · intro h q
    have := (h₃ q).1
    have := Module.Finite.equiv_iff (c₁ q) |>.mp (h q).1
    refine ⟨Module.Finite.equiv_iff (c₂ q) |>.mp (finiteDimensional_cohomology_X₂ k Y hS q),
      fun hq ↦ ?_⟩
    have := (h q).2 hq
    have := subsingleton_cohomology_X₂ hS q (c₁ q).surjective.subsingleton ((h₃ q).2 (by omega))
    exact (c₂ q).surjective.subsingleton
  · intro h q
    have := Module.Finite.equiv_iff (c₂ q) |>.mpr (h q).1
    cases q with
    | zero =>
        have := hS.mono_f
        exact ⟨Module.Finite.equiv_iff (c₁ 0) |>.mpr
          (finiteDimensional_cohomology_zero_of_mono k Y S.f), by omega⟩
    | succ q =>
        have := (h₃ q).1
        refine ⟨Module.Finite.equiv_iff (c₁ (q + 1)) |>.mpr
          (finiteDimensional_cohomology_X₁ k Y hS q (q + 1) rfl), fun hq ↦ ?_⟩
        have := (h (q + 1)).2 hq
        have := subsingleton_cohomology_X₁ hS q (q + 1) rfl
          ((h₃ q).2 (by omega)) (c₂ (q + 1)).injective.subsingleton
        exact (c₁ (q + 1)).injective.subsingleton

variable [IsLocallyNoetherian X] in
private theorem nonempty_cohomologyLinearEquiv_pointBlowup_pullback
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (L : InvertibleSheaf X) (q : ℕ) :
    let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    Nonempty (Cohomology L.obj q ≃ₗ[k]
      Cohomology ((InvertibleSheaf.pullback π).obj L).obj q) := by
  have hs : (Iₚ).support = Closeds.mk (closure ({p} : Set X)) isClosed_closure := by
    ext x
    simp only [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField]
    rfl
  -- The cohomology comparison uses the reduced ideal on the closure of the point.
  have hI : Iₚ = vanishingIdeal (Iₚ).support := by
    refine le_antisymm (by rw [vanishingIdeal_support]; exact le_radical _) ?_
    exact vanishingIdeal_le_ker_of_range_subset _
      (X.fromSpecResidueField p).range_subset_ker_support
  rw [hI.trans (congrArg vanishingIdeal hs)]
  exact ⟨pointBlowupCohomologyLinearEquiv k hp hdim
    ((InvertibleSheaf.toFiniteLocallyFree X).obj L) q⟩

/-- The Euler characteristic of a pulled-back line bundle is unchanged by blowing up a
regular closed point of local dimension two, for every truncation degree. -/
theorem eulerCharBelow_pointBlowup_pullback [IsLocallyNoetherian X]
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (a : LineBundleClass X) (q : ℕ) :
    let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    LineBundleClass.eulerCharBelow k (LineBundleClass.pullback π a) q =
      LineBundleClass.eulerCharBelow k a q := by
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
  simp only [LineBundleClass.pullback_mk, LineBundleClass.eulerCharBelow_mk]
  induction q with
  | zero => simp
  | succ q ih =>
      obtain ⟨e⟩ := nonempty_cohomologyLinearEquiv_pointBlowup_pullback p k hp hdim L q
      simp only [eulerCharBelow_succ, ih, ← e.finrank_eq]

private theorem eulerCharBelow_pointBlowup_exceptional_quotient
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hrat : IsIso (X.fromSpecResidueField p ≫ (X ↘ Spec (.of k))))
    (a : LineBundleClass X) (m : ℤ) (M : InvertibleSheaf Y)
    (hM : LineBundleClass.mk M = twist[a, m]) :
    eulerCharBelow k Y (M.obj ⊗ (E).pushforwardSubscheme) 3 = 1 - m := by
  have h q := nonempty_cohomologyLinearEquiv_pointBlowup_exceptional_quotient
    p k hp hdim hrat a m M hM q
  have hdim' q := (h q).elim fun e ↦ LinearEquiv.finrank_eq e
  have hχ := (Pi.basisFun k (Fin 2)).eulerCharBelow_twistingSheaf (-m) (n := 0) (by decide)
  have hvan := (Pi.basisFun k (Fin 2)).subsingleton_cohomology_proj_of_card_le (𝒪 (-m)) 2
    (by decide)
  rw [eulerCharBelow_succ, eulerCharBelow_two, hdim', hdim', hdim',
    Module.finrank_zero_of_subsingleton (M := Cohomology (𝒪 (-m)) 2)]
  rw [eulerCharBelow_two, Ring.choose_one_right] at hχ
  simp only [Nat.cast_zero, mul_zero, add_zero]
  omega

/-- The first cohomology of the exceptional Cartier quotient vanishes for twists
`mE` with `m ≤ 1`. -/
theorem subsingleton_cohomology_one_pointBlowup_exceptional_quotient
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hrat : IsIso (X.fromSpecResidueField p ≫ (X ↘ Spec (.of k))))
    (a : LineBundleClass X) {m : ℤ} (hm : m ≤ 1) (M : InvertibleSheaf Y)
    (hM : LineBundleClass.mk M = twist[a, m]) :
    Subsingleton (Cohomology (M.obj ⊗ (E).pushforwardSubscheme) 1) := by
  obtain ⟨e⟩ := nonempty_cohomologyLinearEquiv_pointBlowup_exceptional_quotient
    p k hp hdim hrat a m M hM 1
  have := (Pi.basisFun k (Fin 2)).subsingleton_cohomology_twistingSheaf_of_neg_card_lt
    (m := -m) (by simp only [Fintype.card_fin]; omega) (q := 1) (by decide)
  exact e.injective.subsingleton

/-- The first cohomology of the exceptional Cartier quotient has dimension
`max (m - 1) 0`. In particular, the source of the connecting map into surface
second cohomology vanishes for `m ≤ 1`. -/
theorem finrank_cohomology_one_pointBlowup_exceptional_quotient
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hrat : IsIso (X.fromSpecResidueField p ≫ (X ↘ Spec (.of k))))
    (a : LineBundleClass X) (m : ℤ) (M : InvertibleSheaf Y)
    (hM : LineBundleClass.mk M = twist[a, m]) :
    let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    Module.finrank k (Cohomology (M.obj ⊗ (E).pushforwardSubscheme) 1) = (m - 1).toNat := by
  dsimp only
  by_cases hm : m ≤ 1
  · have := subsingleton_cohomology_one_pointBlowup_exceptional_quotient
      p k hp hdim hrat a hm M hM
    rw [Module.finrank_zero_of_subsingleton]
    omega
  · obtain ⟨e⟩ := nonempty_cohomologyLinearEquiv_pointBlowup_exceptional_quotient
      p k hp hdim hrat a m M hM 1
    have hfin := projectiveLine.finrank_cohomology_one_twistingSheaf k (n := -m) (by omega)
    rw [e.finrank_eq]
    omega

variable [Infinite k] [X.IsProjectiveOver k]

/-- All cohomology of an exceptional twist of a pulled-back line bundle on the blowup of
a projective surface at a rational regular point is finite-dimensional, and degrees above
two vanish. This applies to both positive and negative twists. -/
theorem pointBlowup_exceptional_twist_cohomology
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hrat : IsIso (X.fromSpecResidueField p ≫ (X ↘ Spec (.of k))))
    (hX : topologicalKrullDim X ≤ 2) (a : LineBundleClass X) (m : ℤ)
    (M : InvertibleSheaf Y) (hM : LineBundleClass.mk M = twist[a, m]) (q : ℕ) :
    let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    FiniteDimensional k (Cohomology M.obj q) ∧ (2 < q → Subsingleton (Cohomology M.obj q)) := by
  suffices ∀ (B : InvertibleSheaf Y), LineBundleClass.mk B = twist[a, m] →
      ∀ q, FiniteDimensional k (Cohomology B.obj q) ∧
        (2 < q → Subsingleton (Cohomology B.obj q)) from this M hM q
  clear M hM q
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  induction m using Int.induction_on with
  | zero =>
      intro B hB q
      obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
      have hclass : LineBundleClass.mk B =
          LineBundleClass.mk ((InvertibleSheaf.pullback π).obj L) := by
        simpa only [neg_zero, zpow_zero, mul_one, LineBundleClass.pullback_mk] using hB
      obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.mp hclass
      obtain ⟨c⟩ := nonempty_cohomologyLinearEquiv_pointBlowup_pullback p k hp hdim L q
      let d := c.trans (cohomologyBaseLinearEquivOfIso k e.symm q)
      have := moduleFinite_cohomology_of_isProjectiveOver k L.obj q
      refine ⟨Module.Finite.equiv d, fun hq ↦ ?_⟩
      have := subsingleton_cohomology_of_projective_dim_lt (k := k) L.obj
        (hX.trans_lt (by exact_mod_cast hq))
      exact d.surjective.subsingleton
  | succ m ih =>
      intro B hB
      obtain ⟨A, hA⟩ := LineBundleClass.mk_surjective (twist[a, (m : ℤ) + 1 - 1])
      exact (pointBlowup_exceptional_twist_cohomology_step p k hp hdim hrat a _ hA hB).mp
        (ih A (by simpa only [add_sub_cancel_right] using hA))
  | pred m ih =>
      intro A hA
      obtain ⟨B, hB⟩ := LineBundleClass.mk_surjective (twist[a, -(m : ℤ)])
      exact (pointBlowup_exceptional_twist_cohomology_step p k hp hdim hrat a _ hA hB).mpr (ih B hB)

/-- The Euler characteristic changes by `1 - m` between the `(m - 1)E` and `mE` twists.
The map between the twists is the one induced by the ideal of the actual exceptional divisor. -/
theorem eulerCharBelow_pointBlowup_exceptional_twist_sub_one
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hrat : IsIso (X.fromSpecResidueField p ≫ (X ↘ Spec (.of k))))
    (hX : topologicalKrullDim X ≤ 2) (a : LineBundleClass X) (m : ℤ) :
    let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    LineBundleClass.eulerCharBelow k (twist[a, m]) 3 =
      LineBundleClass.eulerCharBelow k (twist[a, m - 1]) 3 + (1 - m) := by
  obtain ⟨L, hL⟩ := LineBundleClass.mk_surjective (twist[a, m - 1])
  obtain ⟨M, hM⟩ := LineBundleClass.mk_surjective (twist[a, m])
  obtain ⟨e₁⟩ := exists_iso_tensor_exceptional_ideal_pointBlowup_twist p a m hL hM
  let e₂ := ρ_ M.obj
  have h₁ q := pointBlowup_exceptional_twist_cohomology p k hp hdim hrat hX a (m - 1) L hL q
  have h₂ q := pointBlowup_exceptional_twist_cohomology p k hp hdim hrat hX a m M hM q
  have := (h₁ 3).2 (by decide)
  have h := eulerCharBelow_eq_add k ((E).shortExact_tensor_toPushforwardSubscheme M.obj) 3
    (fun q _ _ ↦ (finiteDimensional_cohomology_congr k e₁ q).mp (h₁ q).1)
    (fun q _ ↦ (finiteDimensional_cohomology_congr k e₂ q).mpr (h₂ q).1)
    (cohomologyBaseLinearEquivOfIso k e₁ 3).surjective.subsingleton
  dsimp only
  rw [← hL, ← hM, LineBundleClass.eulerCharBelow_mk, LineBundleClass.eulerCharBelow_mk]
  -- The mapped Cartier complex has the three tensor products compared above.
  change eulerCharBelow k Y (M.obj ⊗ 𝟙_ (Y).Modules) 3 =
    eulerCharBelow k Y (M.obj ⊗ (E).sheaf) 3 +
      eulerCharBelow k Y (M.obj ⊗ (E).pushforwardSubscheme) 3 at h
  rw [eulerCharBelow_congr k e₂, ← eulerCharBelow_congr k e₁,
    eulerCharBelow_pointBlowup_exceptional_quotient p k hp hdim hrat a m M hM] at h
  exact h

/-- On the blowup of a projective surface at a rational regular point, the Euler characteristic
of `π*L(mE)` is `χ(L) + m(1-m)/2`, for every integer `m`. -/
theorem eulerCharBelow_pointBlowup_exceptional_twist
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hrat : IsIso (X.fromSpecResidueField p ≫ (X ↘ Spec (.of k))))
    (hX : topologicalKrullDim X ≤ 2) (a : LineBundleClass X) (m : ℤ) :
    let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    LineBundleClass.eulerCharBelow k (twist[a, m]) 3 =
      LineBundleClass.eulerCharBelow k a 3 + m * (1 - m) / 2 := by
  let χ (t : ℤ) := LineBundleClass.eulerCharBelow k (twist[a, t]) 3
  let χ₀ := LineBundleClass.eulerCharBelow k a 3
  suffices h : 2 * (χ m - χ₀) = m * (1 - m) by
    have heq : χ m = χ₀ + m * (1 - m) / 2 := by omega
    exact heq
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have hstep t : χ t = χ (t - 1) + (1 - t) :=
    eulerCharBelow_pointBlowup_exceptional_twist_sub_one p k hp hdim hrat hX a t
  have hpoly (t : ℤ) : t * (1 - t) = (t - 1) * (1 - (t - 1)) + 2 * (1 - t) := by ring
  induction m using Int.induction_on with
  | zero =>
      have h : χ 0 = χ₀ := by
        simpa only [χ, χ₀, neg_zero, zpow_zero, mul_one] using
          eulerCharBelow_pointBlowup_pullback p k hp hdim a 3
      simp [h]
  | succ m ih =>
      have h := hstep ((m : ℤ) + 1)
      have h' := hpoly ((m : ℤ) + 1)
      rw [add_sub_cancel_right] at h h'
      omega
  | pred m ih =>
      have h := hstep (-(m : ℤ))
      have h' := hpoly (-(m : ℤ))
      omega

omit [Infinite k] in
/-- The exceptional twist formula for the blowup of any closed point on a smooth projective
surface over an algebraically closed field. -/
theorem eulerCharBelow_pointBlowup_exceptional_twist_of_smoothSurface
    [IsAlgClosed k] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    (hp : IsClosed ({p} : Set X)) (a : LineBundleClass X) (m : ℤ) :
    let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    LineBundleClass.eulerCharBelow k (twist[a, m]) 3 =
      LineBundleClass.eulerCharBelow k a 3 + m * (1 - m) / 2 := by
  let f := X ↘ Spec (.of k)
  have : Nonempty X := ⟨p⟩
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsRegular X := IsRegular.of_smooth f
  have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 p hp
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have hr : IsIso (X.fromSpecResidueField p ≫ f) := by
    rw [← SpecMap_residueFieldIsoBase_inv f p hp]
    infer_instance
  exact eulerCharBelow_pointBlowup_exceptional_twist p k hp hd hr hX.le a m

end AlgebraicGeometry.Scheme.IdealSheafData

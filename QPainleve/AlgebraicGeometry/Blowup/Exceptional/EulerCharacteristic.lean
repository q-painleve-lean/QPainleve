/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Restriction
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.LineBundle.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import QPainleve.AlgebraicGeometry.Blowup.Point.Cohomology
import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.Cohomology.ProjectiveSpace.EulerCharacteristic
import QPainleve.AlgebraicGeometry.Cohomology.Support
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Cohomology
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.NegativeTwist
import TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic
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
  have hdegree : LineBundleClass.intersectionNumber k (e.hom ≫ ι) (LineBundleClass.mk M) = -m := by
    rw [LineBundleClass.intersectionNumber_mk]
    exact (projectiveLine.nonempty_iso_twistingSheaf_iff k _ (-m)).mp (htwist a m M hM)
  exact ⟨((E).cohomologyTensorPushforwardSubschemeEquivTwistingSheaf e M q).trans
    (LinearEquiv.cast (M := fun d : ℤ ↦ Cohomology (𝒪 d) q) hdegree)⟩

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

/-- Finiteness and vanishing above degree two for a line bundle pass to every exceptional
twist of its pullback under the blowup of a rational regular point of local dimension two. -/
theorem pointBlowup_exceptional_twist_cohomology_of_cohomology [IsLocallyNoetherian X]
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hrat : IsIso (X.fromSpecResidueField p ≫ (X ↘ Spec (.of k))))
    (L : InvertibleSheaf X)
    (hL : ∀ q, FiniteDimensional k (Cohomology L.obj q) ∧
      (2 < q → Subsingleton (Cohomology L.obj q)))
    (m : ℤ) (M : InvertibleSheaf Y) (hM : LineBundleClass.mk M = twist[LineBundleClass.mk L, m])
    (q : ℕ) :
    let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    FiniteDimensional k (Cohomology M.obj q) ∧ (2 < q → Subsingleton (Cohomology M.obj q)) := by
  let a := LineBundleClass.mk L
  suffices ∀ (B : InvertibleSheaf Y), LineBundleClass.mk B = twist[a, m] →
      ∀ q, FiniteDimensional k (Cohomology B.obj q) ∧
        (2 < q → Subsingleton (Cohomology B.obj q)) from this M hM q
  clear M hM q
  induction m using Int.induction_on with
  | zero =>
      intro B hB q
      have hclass : LineBundleClass.mk B =
          LineBundleClass.mk ((InvertibleSheaf.pullback π).obj L) := by
        simpa only [a, neg_zero, zpow_zero, mul_one, LineBundleClass.pullback_mk] using hB
      obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.mp hclass
      obtain ⟨c⟩ := nonempty_cohomologyLinearEquiv_pointBlowup_pullback p k hp hdim L q
      let d := c.trans (cohomologyBaseLinearEquivOfIso k e.symm q)
      have := (hL q).1
      refine ⟨Module.Finite.equiv d, fun hq ↦ ?_⟩
      have := (hL q).2 hq
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

private theorem eulerCharBelow_pointBlowup_exceptional_twist_sub_one_of_cohomology
    [IsLocallyNoetherian X]
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hrat : IsIso (X.fromSpecResidueField p ≫ (X ↘ Spec (.of k))))
    (A : InvertibleSheaf X)
    (hA : ∀ q, FiniteDimensional k (Cohomology A.obj q) ∧
      (2 < q → Subsingleton (Cohomology A.obj q))) (m : ℤ) :
    let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    LineBundleClass.eulerCharBelow k (twist[LineBundleClass.mk A, m]) 3 =
      LineBundleClass.eulerCharBelow k (twist[LineBundleClass.mk A, m - 1]) 3 + (1 - m) := by
  let a := LineBundleClass.mk A
  obtain ⟨L, hL⟩ := LineBundleClass.mk_surjective (twist[a, m - 1])
  obtain ⟨M, hM⟩ := LineBundleClass.mk_surjective (twist[a, m])
  obtain ⟨e₁⟩ := exists_iso_tensor_exceptional_ideal_pointBlowup_twist p a m hL hM
  let e₂ := ρ_ M.obj
  have h₁ q := pointBlowup_exceptional_twist_cohomology_of_cohomology
    p k hp hdim hrat A hA (m - 1) L hL q
  have h₂ q := pointBlowup_exceptional_twist_cohomology_of_cohomology
    p k hp hdim hrat A hA m M hM q
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

/-- On a blowup at a rational regular point of local dimension two, twice the change
in Euler characteristic for the exceptional twist by `mE` is `m(1-m)`.
The base line bundle must have finite cohomology vanishing above degree two. -/
theorem two_mul_eulerCharBelow_sub_pointBlowup_exceptional_twist [IsLocallyNoetherian X]
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hrat : IsIso (X.fromSpecResidueField p ≫ (X ↘ Spec (.of k))))
    (L : InvertibleSheaf X)
    (hL : ∀ q, FiniteDimensional k (Cohomology L.obj q) ∧
      (2 < q → Subsingleton (Cohomology L.obj q))) (m : ℤ) :
    let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    2 * (LineBundleClass.eulerCharBelow k (twist[LineBundleClass.mk L, m]) 3 -
      LineBundleClass.eulerCharBelow k (LineBundleClass.mk L) 3) = m * (1 - m) := by
  let a := LineBundleClass.mk L
  let χ (t : ℤ) := LineBundleClass.eulerCharBelow k (twist[a, t]) 3
  let χ₀ := LineBundleClass.eulerCharBelow k a 3
  suffices h : 2 * (χ m - χ₀) = m * (1 - m) from h
  have hstep t : χ t = χ (t - 1) + (1 - t) :=
    eulerCharBelow_pointBlowup_exceptional_twist_sub_one_of_cohomology p k hp hdim hrat L hL t
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

variable [Infinite k] [X.IsProjectiveOver k]

private theorem lineBundle_cohomology_of_projective_surface (hX : topologicalKrullDim X ≤ 2)
    (L : InvertibleSheaf X) (q : ℕ) :
    FiniteDimensional k (Cohomology L.obj q) ∧ (2 < q → Subsingleton (Cohomology L.obj q)) :=
  ⟨moduleFinite_cohomology_of_isProjectiveOver k L.obj q, fun hq ↦
    subsingleton_cohomology_of_projective_dim_lt (k := k) L.obj
      (hX.trans_lt (by exact_mod_cast hq))⟩

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
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
  have h := two_mul_eulerCharBelow_sub_pointBlowup_exceptional_twist
    p k hp hdim hrat L (lineBundle_cohomology_of_projective_surface k hX L) m
  dsimp only at h ⊢
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

local notation "Jₚ" =>
  vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)

omit [Infinite k] in
/-- The exceptional twist formula for the center given by the vanishing ideal of the
closed point, in terms of the Picard class of its exceptional divisor. -/
theorem eulerCharBelow_pointBlowup_exceptional_twist_vanishingIdeal
    [IsAlgClosed k] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    (hp : IsClosed ({p} : Set X)) (a : LineBundleClass X) (m : ℤ) :
    letI : Scheme.Over (Jₚ).blowup (Spec (.of k)) := ⟨(Jₚ).blowupToBase ≫ X ↘ Spec (.of k)⟩
    LineBundleClass.eulerCharBelow k
      (LineBundleClass.pullback (Jₚ).blowupToBase a * (Jₚ).blowupExceptionalClass ^ m) 3 =
      LineBundleClass.eulerCharBelow k a 3 + m * (1 - m) / 2 := by
  -- Transport the scheme, structure map and exceptional class along the center equality.
  let P (J : X.IdealSheafData) : Prop :=
    let : J.blowup.Over (Spec (.of k)) := ⟨J.blowupToBase ≫ X ↘ Spec (.of k)⟩
    LineBundleClass.eulerCharBelow k
      (LineBundleClass.pullback J.blowupToBase a * J.blowupExceptionalClass ^ m) 3 =
      LineBundleClass.eulerCharBelow k a 3 + m * (1 - m) / 2
  have h : P Iₚ := by
    simpa only [P, blowupExceptionalClass_def, inv_zpow, zpow_neg] using
      eulerCharBelow_pointBlowup_exceptional_twist_of_smoothSurface p k hp a m
  exact (X.ker_fromSpecResidueField_eq_vanishingIdeal p) ▸ h

end AlgebraicGeometry.Scheme.IdealSheafData

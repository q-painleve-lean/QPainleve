/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
import TauCeti.AlgebraicGeometry.LineBundle.LocalRing
import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine

/-!
# Restriction to the exceptional projective line

The pullback of a line bundle from the base restricts trivially to the exceptional fibre.
The exceptional twist by `mE` has degree `-m` there. These comparisons identify the
Cartier quotient used to compute cohomology under a point blowup. Tensoring by the
exceptional ideal identifies the first term of the same sequence with the preceding twist.
-/

public section

open CategoryTheory Limits MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

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

/-- On the exceptional projective line over the residue field, restriction of a pulled-back
line bundle twisted by `mE` has degree `-m`. The same identification works for every line
bundle and every integer twist. -/
theorem exists_iso_projectiveLine_residueField_exceptional_twist
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) :
    let κ : Type u := X.residueField p
    let 𝒜κ := TauCeti.SymmetricAlgebra.homogeneousSubmodule κ (Fin 2 → κ)
    ∃ e : projectiveLine κ ≅ (E).subscheme,
      IsPullback (e.hom ≫ ι) (projectiveLine κ ↘ Spec (.of κ)) π (X.fromSpecResidueField p) ∧
      ∀ (a : LineBundleClass X) (m : ℤ) (M : InvertibleSheaf Y),
        LineBundleClass.mk M = twist[a, m] →
        Nonempty (((InvertibleSheaf.pullback (e.hom ≫ ι)).obj M).obj ≅
          Proj.twistingSheaf 𝒜κ (-m)) := by
  let κ := X.residueField p
  obtain ⟨e, he, hconormal, -⟩ :=
    exists_iso_projectiveLine_pullback_exceptionalIdeal_of_closedPoint p hp hdim
  refine ⟨e, he, fun a m M hM ↦ ?_⟩
  have ha : LineBundleClass.pullback (e.hom ≫ ι) (LineBundleClass.pullback π a) = 1 := by
    rw [LineBundleClass.pullback_comp, he.w, ← LineBundleClass.pullback_comp]
    have h : LineBundleClass.pullback (X.fromSpecResidueField p) a = 1 := Subsingleton.elim _ _
    rw [h, LineBundleClass.pullback_one]
  let : Fact (∀ x : projectiveLine κ, Order.coheight x ≤ 1) :=
    ⟨Scheme.IsCurveOver.coheight_le_one (k := κ)⟩
  have hd : LineBundleClass.eulerDegree κ
      (LineBundleClass.pullback (e.hom ≫ ι) (LineBundleClass.mk 𝒥)) = 1 := by
    rw [LineBundleClass.pullback_mk, LineBundleClass.eulerDegree_mk]
    exact (projectiveLine.nonempty_iso_twistingSheaf_iff κ _ 1).mp hconormal
  apply (projectiveLine.nonempty_iso_twistingSheaf_iff κ _ (-m)).mpr
  rw [← LineBundleClass.eulerDegree_mk, ← LineBundleClass.pullback_mk, hM,
    LineBundleClass.pullback_mul, ha, one_mul, LineBundleClass.pullback_zpow,
    LineBundleClass.eulerDegree_zpow, hd, mul_one]

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

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

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
  obtain ⟨eκ, heκ, htwist⟩ :=
    exists_iso_projectiveLine_residueField_exceptional_twist p hp hdim
  let e := (asIso b).symm ≪≫ eκ
  have he : b ≫ e.hom = eκ.hom := by simp [e]
  have hκ : eκ.hom ≫ ι ≫ π ≫ (X ↘ Spec (.of k)) =
      b ≫ (projectiveLine k ↘ Spec (.of k)) := by
    rw [hb.w, hc]
    simpa only [Category.assoc, c] using
      congrArg (· ≫ (X ↘ Spec (.of k))) heκ.w
  refine ⟨e, (cancel_epi b).mp (by simpa only [← Category.assoc, he] using hκ), ?_⟩
  intro a m M hM
  let N := (InvertibleSheaf.pullback (e.hom ≫ ι)).obj M
  have hN : LineBundleClass.mk N =
      LineBundleClass.pullback (e.hom ≫ ι) (LineBundleClass.mk M) :=
    (LineBundleClass.pullback_mk _ _).symm
  let : Fact (∀ x : projectiveLine k, Order.coheight x ≤ 1) :=
    ⟨Scheme.IsCurveOver.coheight_le_one (k := k)⟩
  apply (projectiveLine.nonempty_iso_twistingSheaf_iff k N (-m)).mpr
  rw [← LineBundleClass.eulerDegree_mk, ← LineBundleClass.eulerDegree_pullback hb, hN,
    LineBundleClass.pullback_comp, ← Category.assoc, he, LineBundleClass.pullback_mk,
    LineBundleClass.eulerDegree_mk]
  exact (projectiveLine.nonempty_iso_twistingSheaf_iff κ _ (-m)).mp (htwist a m M hM)

end AlgebraicGeometry.Scheme.IdealSheafData

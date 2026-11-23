/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Mutation.Center

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Pullback
import TauCeti.AlgebraicGeometry.Restrict

/-!
# Ordered internal blowups away from the mutation fiber

The mutation isomorphism on the complements of the pivot fiber identifies the
reduced toric boundaries there. It therefore identifies the models obtained by
blowing up any ordered list of the transported centers, compatibly with their
strict boundaries. Repeated centers are blown up on the successive strict
transforms, including the infinitely near centers.

This is the lifting through the remaining centers in the elementary transformation
of Gross, Hacking and Keel, [*Birational geometry of cluster algebras*, §3.1][GHK].

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.Scheme.IdealSheafData
open QPainleve.BlowupTower

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (b : Module.Basis (Fin 2) ℤ N) {v : N} (hv : v ≠ 0)
  (hpos : PointedCone.hull ℝ {i v} ∈ Φ.cones) (hneg : PointedCone.hull ℝ {i (-v)} ∈ Φ.cones)
  (c : ℂˣ)

local notation "Ψ" => Φ.mutationFan b hv hpos hneg
local notation "U₀" =>
  Φ.mutationComplement b (Φ.detCharacter_nonneg_or_nonpos b hv hpos hneg) (Units.val c)
local notation "U₁" =>
  mutationComplement (Ψ) b (Φ.mutationDetCharacter_nonneg_or_nonpos b hv hpos hneg) (Units.val c)
local notation "e" => Φ.mutationComplementIso b (Units.val c) hv hpos hneg
local notation "f₀" => Scheme.Opens.ι (U₀)
local notation "f₁" => Iso.hom (e) ≫ Scheme.Opens.ι (U₁)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "χ(" ρ ")" => LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator ρ))
local notation "hχ(" ρ ")" => Eq.trans
  (congrFun (LinearMap.toAddMonoidHom_coe (b.detDualEquiv (Ray.primitiveGenerator ρ)))
    (Ray.primitiveGenerator ρ)) (Module.Basis.detDualEquiv_self b (Ray.primitiveGenerator ρ))

local notation "center(" ρ ", " a ")" =>
  Ray.binomialCenterOnBoundary ρ rankTwo (m := χ(ρ)) hχ(ρ) (Ray.surjective_detCharacter ρ b) a

variable [hΦ : Nonempty Φ.cones]
local notation "hΨ" =>
  Nonempty.intro (Φ.mutationFanConeEquiv b hv hpos hneg (Subtype.mk _ hpos))

local notation "J₀" => Φ.boundaryIdeal hΦ
local notation "J₁" => boundaryIdeal (Ψ) hΨ
local notation "J" => comap (J₀) (f₀)
local notation "boundaryToTarget" => subschemeMap (J) (J₁) (f₁) (le_map_iff_comap_le.mpr
  (Eq.le (comap_boundaryIdeal_mutationComplementIso b hv hpos hneg c hΦ hΨ)))

private theorem isPullback_boundary_to_mutationTarget :
    IsPullback (J).subschemeι (boundaryToTarget) (f₁) (J₁).subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _ (subschemeMap_subschemeι _ _ _ _).symm
    (by simpa only [ker_subschemeι] using
      comap_boundaryIdeal_mutationComplementIso b hv hpos hneg c hΦ hΨ)

variable {n : ℕ} (s : Fin n → Φ.Ray) (d : Fin n → ℂˣ)

local notation "r" => Φ.mutationFanRayEquiv b hv hpos hneg
local notation "d₁" =>
  fun j ↦ d j * c ^ max (Module.Basis.det b ![Ray.primitiveGenerator (s j), v]) 0

local notation "s₀" => fun j ↦ center(s j, d j)
local notation "s₁" => fun j ↦ center((r) (s j), (d₁) j)

private theorem exists_common_boundaryCenter
    {j₀ : (J).subscheme ⟶ (J₀).subscheme} {j₁ : (J).subscheme ⟶ (J₁).subscheme}
    (h₀ : IsPullback (J).subschemeι j₀ (f₀) (J₀).subschemeι)
    (h₁ : IsPullback (J).subschemeι j₁ (f₁) (J₁).subschemeι)
    (hprim : IsPrimitive v) (j : Fin n)
    (hsame : (s j).primitiveGenerator = v → d j ≠ c)
    (hopp : (s j).primitiveGenerator = -v → d j * c ≠ 1) :
    ∃ t : S ⟶ (J).subscheme, t ≫ j₀ = (s₀) j ∧ t ≫ j₁ = (s₁) j := by
  obtain ⟨p, hp₀, hp₁⟩ :=
    exists_binomialCenter_mutationComplementIso b (s j) hv hpos hneg c (d j) hprim hsame hopp
  have hp : p ≫ f₀ = (s₀) j ≫ (J₀).subschemeι := by
    simpa only [Ray.binomialCenterOnBoundary_comp_subschemeι] using hp₀
  refine ⟨h₀.lift p ((s₀) j) hp, h₀.lift_snd _ _ _, (cancel_mono (J₁).subschemeι).mp ?_⟩
  rw [Category.assoc, ← h₁.w, ← Category.assoc, h₀.lift_fst]
  simpa only [Ray.binomialCenterOnBoundary_comp_subschemeι] using hp₁

/-- The restrictions of the two ordered toric blowup models to the mutation fiber
complements have a common model over the complement isomorphism. Both comparison
squares are cartesian, and the same closed boundary embeds as the restriction of
each strict boundary. Only centers on the pivot fiber are excluded. -/
theorem exists_common_internalBlowupTower_mutationComplement (hprim : IsPrimitive v)
    (hsame : ∀ j, (s j).primitiveGenerator = v → d j ≠ c)
    (hopp : ∀ j, (s j).primitiveGenerator = -v → d j * c ≠ 1) :
    let A := internalBlowupTower b s d
    let B := internalBlowupTower (Φ := Ψ) (h₀ := hΨ) b ((r) ∘ s) (d₁)
    ∃ (Z : Scheme) (q : Z ⟶ (U₀).toScheme) (g₀ : Z ⟶ A.1) (g₁ : Z ⟶ B.1)
        (j : (J).subscheme ⟶ Z),
      IsPullback g₀ q A.2.toTower.toBase (f₀) ∧
      IsPullback g₁ q B.2.toTower.toBase (f₁) ∧
      IsPullback j (subschemeMap _ _ (f₀) ((J₀).le_map_comap (f₀))) g₀ A.2.boundaryι ∧
      IsPullback j (boundaryToTarget) g₁ B.2.boundaryι := by
  classical
  let j₀ := subschemeMap _ _ (f₀) ((J₀).le_map_comap (f₀))
  have h₀ : IsPullback (J).subschemeι j₀ (f₀) (J₀).subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _
      (subschemeMap_subschemeι _ _ _ _).symm (by simp)
  have h₁ := isPullback_boundary_to_mutationTarget b hv hpos hneg c
  choose s' hs₀ hs₁ using fun k ↦
    exists_common_boundaryCenter b hv hpos hneg c s d h₀ h₁ hprim k (hsame k) (hopp k)
  have hC₀ (k : Fin n) : ((s₀) k).ker.IsEffectiveCartier :=
    (s k).isEffectiveCartier_ker_binomialCenterOnBoundary rankTwo hχ(s k)
      ((s k).surjective_detCharacter b) (d k)
  have hC₁ (k : Fin n) : ((s₁) k).ker.IsEffectiveCartier :=
    ((r) (s k)).isEffectiveCartier_ker_binomialCenterOnBoundary rankTwo hχ((r) (s k))
      (((r) (s k)).surjective_detCharacter b) ((d₁) k)
  have hclosed₀ (k : Fin n) : IsClosedImmersion ((s₀) k) :=
    (s k).isClosedImmersion_binomialCenterOnBoundary rankTwo (m := χ(s k))
      (b.detDualEquiv_self _) ((s k).surjective_detCharacter b) (d k)
  have hclosed₁ (k : Fin n) : IsClosedImmersion ((s₁) k) :=
    ((r) (s k)).isClosedImmersion_binomialCenterOnBoundary rankTwo
      (m := χ((r) (s k))) (b.detDualEquiv_self _) (((r) (s k)).surjective_detCharacter b) ((d₁) k)
  have hs' (k : Fin n) : (s' k).ker.IsEffectiveCartier := by
    have hd : IsOpenImmersion j₀ := MorphismProperty.of_isPullback h₀ inferInstance
    have hsquare : IsPullback (s' k) (𝟙 _) j₀ ((s₀) k) :=
      IsPullback.of_vert_isIso_mono ⟨by simpa only [Category.id_comp] using hs₀ k⟩
    exact ker_eq_comap_of_isPullback _ hsquare ▸ (hC₀ k).comap j₀
  have himage₀ (k : Fin n) : Set.range ((s₀) k ≫ (J₀).subschemeι) ⊆ (f₀).isoLocus := by
    rw [← hs₀ k, Category.assoc, ← h₀.w, ← Category.assoc]
    exact (Set.range_comp_subset_range _ (f₀)).trans
      ((f₀).le_isoLocus_iff.mpr ((f₀).isIso_morphismRestrict_of_le_opensRange le_rfl))
  have himage₁ (k : Fin n) : Set.range ((s₁) k ≫ (J₁).subschemeι) ⊆ (f₁).isoLocus := by
    rw [← hs₁ k, Category.assoc, ← h₁.w, ← Category.assoc]
    exact (Set.range_comp_subset_range _ (f₁)).trans
      ((f₁).le_isoLocus_iff.mpr ((f₁).isIso_morphismRestrict_of_le_opensRange le_rfl))
  obtain ⟨g₀, hg₀, hb₀⟩ := exists_isPullback_alongBoundary h₀.w (s₀) s' hs₀ hC₀ hs' himage₀
  obtain ⟨g₁, hg₁, hb₁⟩ := exists_isPullback_alongBoundary h₁.w (s₁) s' hs₁ hC₁ hs' himage₁
  dsimp only at hg₀ hb₀ hg₁ hb₁ ⊢
  rw [internalBlowupTower_eq_alongBoundary b s d,
    internalBlowupTower_eq_alongBoundary (h₀ := hΨ) b ((r) ∘ s) (d₁)]
  have hinput₀ : (fun j ↦ ⟨((s₀) j).ker, hC₀ j⟩) = fun j ↦ (s j).internalCenter b (d j) :=
    funext fun j ↦ Subtype.ext ((s j).internalCenter_val b (d j)).symm
  have hinput₁ : (fun j ↦ ⟨((s₁) j).ker, hC₁ j⟩) =
      fun j ↦ (((r) ∘ s) j).internalCenter (h₀ := hΨ) b ((d₁) j) :=
    funext fun j ↦ Subtype.ext (((r) (s j)).internalCenter_val (h₀ := hΨ) b ((d₁) j)).symm
  rw [← hinput₀, ← hinput₁]
  exact ⟨_, _, g₀, g₁, _, hg₀, hg₁,
    WithBoundary.isPullback_boundaryι h₀ hg₀ hb₀,
    WithBoundary.isPullback_boundaryι h₁ hg₁ hb₁⟩

end TauCeti.Toric.Fan

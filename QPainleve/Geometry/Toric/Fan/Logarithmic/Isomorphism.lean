/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Equiv
public import QPainleve.Geometry.Toric.Fan.Logarithmic.StarFactorization
public import QPainleve.Geometry.Toric.Fan.Subdivision
public import QPainleve.Geometry.Toric.Fan.Subdivision.Equiv
public import QPainleve.Geometry.Toric.Fan.TorusAction.InternalBlowup

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.Boundary.Transport
import QPainleve.Geometry.Toric.Fan.Picard.Translation
import QPainleve.Geometry.Toric.Fan.TorusAction.Subdivision

/-!
# Ordered models for a resolved toric isomorphism

A fan equivalence followed by a torus translation carries a specified ordered
internal model to an ordered model of the target projection. The isomorphism
lifts along the given subdivision and transports each center in place, including
infinitely near centers. This handles the toric identifications at the ends of
the specified factorization in [Lutz, Theorem 8.4][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative Module
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

namespace TauCeti.Toric.Fan.LogarithmicProjection

universe u

variable {k : Type u} [Field k] [PerfectField k] {N V : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "π[" H "]" => FanHom.finiteFanSchemeHom k (IsSubdivision.toFanHom H)
local notation "base[" U "]" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd U))

variable {Z : Scheme} [Z.Over (Spec (.of k))] [IsIntegral Z]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
  {D : Z.IdealSheafData} {A B : LogarithmicProjection k i D}

/-- Transport a specified ordered model along a resolved toric isomorphism.
The carried basis and translated parameters give the target model over the
transported subdivision. Its projection recovers the specified regular
representative, and its strict boundary recovers the same pole ideal.
The lift preserves the order and the total exceptional coordinates. On toric
classes its pullback is that of the lattice equivalence. -/
theorem exists_ordered_toric_iso_model
    (f : FanEquiv A.fan B.fan) (χ : Multiplicative (N →+ ℤ) →* kˣ)
    (hf : A.hom.toRationalMap.comp
      (f.toFanHom.finiteFanSchemeHom k ≫ (B.fan.torusTranslationIso k χ).hom).toRationalMap =
        B.hom.toRationalMap)
    (b : Basis (Fin 2) ℤ N) {Δ : Fan i} (hΔ : Δ.IsRegular) (H : Δ.IsSubdivision A.fan)
    {n : ℕ} (r : Fin n → Δ.Ray) (c : Fin n → kˣ) :
    letI : Nonempty Δ.cones := H.nonempty_cones_of_nonempty A.isComplete.nonempty_cones
    let Δ' := Δ.mapEquiv B.fan.lattice f.latticeEquiv
    let F := Δ.mapEquivIso B.fan.lattice f.latticeEquiv
    let K := f.isSubdivision_mapEquiv H
    letI : Nonempty Δ'.cones := K.nonempty_cones_of_nonempty B.isComplete.nonempty_cones
    let b' := b.map F.latticeEquiv.toIntLinearEquiv
    let r' := F.rayEquiv ∘ r
    let c' := fun j ↦ c j / χ (ofAdd (b'.detDualEquiv (r' j).primitiveGenerator).toAddMonoidHom)
    let U := Δ.internalBlowupTower k b r c
    let W := Δ'.internalBlowupTower k b' r' c'
    ∀ (a : U.1 ≅ Z), a.hom ≫ A.hom = base[U] ≫ π[H] →
      D.comap a.hom = U.2.boundaryι.ker →
      ∃ g : U.1 ≅ W.1,
        IsLift (F.finiteFanSchemeIso k ≪≫ Δ'.torusTranslationIso k χ)
          U.2.toTower W.2.toTower g ∧
        (g.inv ≫ a.hom) ≫ B.hom = base[W] ≫ π[K] ∧
        D.comap (g.inv ≫ a.hom) = W.2.boundaryι.ker ∧
        U.2.boundaryι ≫ g.hom =
          (F.boundaryIso k inferInstance inferInstance ≪≫ Δ'.boundaryTranslation k χ).hom ≫
            W.2.boundaryι ∧
        ∀ (d : Additive (LineBundleClass (Δ'.finiteFanScheme k))) (x : Fin n → ℤ),
          pullback g.hom (W.2.toTower.picardHom (d, x)).toMul =
            (U.2.toTower.picardHom
              (Additive.ofMul (pullback (F.toFanHom.finiteFanSchemeHom k) d.toMul), x)).toMul := by
  intro Δ' F K b' r' c' U W a ha hD
  let h₀ : Nonempty Δ.cones := H.nonempty_cones_of_nonempty A.isComplete.nonempty_cones
  let h₁ : Nonempty Δ'.cones := K.nonempty_cones_of_nonempty B.isComplete.nonempty_cones
  have hΔ' : Δ'.IsRegular := F.isRegular_iff.mpr hΔ
  obtain ⟨u, ⟨hu, huB⟩, -⟩ := F.existsUnique_isLift_internalBlowupTower k b b'
    (b.detDualEquiv_map F.latticeEquiv.toIntLinearEquiv) r c hΔ
  obtain ⟨v, ⟨hv, hvB, -⟩, -⟩ :=
    exists_unique_internal_blowup_torus_translation k b' r' hΔ' χ c c' (fun _ ↦ rfl)
  let g : U.1 ≅ W.1 := u ≪≫ v
  have hg := hu.trans hv
  have hB : U.2.boundaryι ≫ g.hom =
      (F.boundaryIso k h₀ h₁ ≪≫ Δ'.boundaryTranslation k χ).hom ≫ W.2.boundaryι := by
    dsimp only [g, U, W, r'] at huB hvB ⊢
    rw [Iso.trans_hom, Iso.trans_hom, reassoc_of% huB, hvB, Category.assoc]
  have hproj : A.hom ≫ f.toFanHom.finiteFanSchemeHom k ≫
      (B.fan.torusTranslationIso k χ).hom = B.hom := by
    let : (B.fan.finiteFanScheme k).IsSeparated := inferInstance
    apply Scheme.Hom.toRationalMap_injective
    simpa only [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom] using hf
  have hsub : F.toFanHom.finiteFanSchemeHom k ≫ π[K] =
      π[H] ≫ f.toFanHom.finiteFanSchemeHom k := by
    rw [← FanHom.finiteFanSchemeHom_comp, ← FanHom.finiteFanSchemeHom_comp,
      f.toFanHom_comp_subdivision H]
  have htarget : g.hom ≫ base[W] ≫ π[K] = a.hom ≫ B.hom := by
    rw [hg.hom_toBase_assoc]
    simp only [Iso.trans_hom, FanEquiv.finiteFanSchemeIso_hom, Category.assoc]
    rw [K.torusTranslationIso_hom_comp_finiteFanSchemeHom k, reassoc_of% hsub,
      ← reassoc_of% ha, hproj]
  refine ⟨g, hg, ?_, ?_, hB, ?_⟩
  · rw [Category.assoc, ← htarget, Iso.inv_hom_id_assoc]
  · have hBinv : U.2.boundaryι =
        ((F.boundaryIso k h₀ h₁ ≪≫ Δ'.boundaryTranslation k χ).hom ≫ W.2.boundaryι) ≫ g.inv := by
      rw [← hB, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [comap_comp, hD, hBinv, Scheme.Hom.comap_ker_comp_of_isClosedImmersion,
      Scheme.Hom.ker_comp_of_isIso]
  · intro d x
    rw [hg.pullback_picardHom, Iso.trans_hom, FanEquiv.finiteFanSchemeIso_hom, ← pullback_comp,
      Δ'.pullback_torusTranslation_hom k hΔ']

end TauCeti.Toric.Fan.LogarithmicProjection

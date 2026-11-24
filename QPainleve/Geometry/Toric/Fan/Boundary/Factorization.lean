/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Automorphism
public import QPainleve.Geometry.Toric.Fan.Boundary.Equiv

import QPainleve.Geometry.Toric.Fan.Equiv
import QPainleve.Geometry.Toric.Fan.Picard.Rank
import QPainleve.Geometry.Toric.Fan.TwoDimensional
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Factorization of isomorphisms of toric pairs

An isomorphism of complete regular toric surfaces preserving the reduced boundary
is a fan isomorphism followed by a torus translation. The boundary prime divisors
determine the map on rays, and the toric Picard presentation recovers the lattice
map from its action on principal divisors using
`Fan.exact_characterToRayDivisor_rayDivisorToPicard`. The residual isomorphism
fixes each ray divisor, so the boundary-fixing translation theorem applies.

This gives the terminal isomorphism of a factorization into the admissible links
of [Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry (CodimensionOnePoint LineBundleClass)
open AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N N' : Type} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

local notation "X[" A "]" => Fan.algebraicRealization A
local notation "D[" A "," h "]" => Fan.boundaryIdeal A h
local notation "p[" A "," h "," r "]" => Fan.rayBoundaryPoint A h r
local notation "I[" A "," h "," r "]" => Fan.rayBoundaryIdeal A h r

section BoundaryRays

variable [Nonempty Φ.cones] [Nonempty Ψ.cones]
  (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (e : X[Φ] ≅ X[Ψ])
  (he : (D[Ψ,inferInstance]).comap e.hom = D[Φ,inferInstance])

include he in
private theorem exists_rayBoundaryPoint_image (ρ : Φ.Ray) :
    ∃ τ : Ψ.Ray, e.hom (p[Φ,hΦ,ρ]).val = (p[Ψ,hΨ,τ]).val := by
  have h := Φ.rayBoundaryPoint_notMem_range_denseTorusι hΦ ρ
  have hmem : (p[Φ,hΦ,ρ]).val ∈
      (((D[Ψ,inferInstance]).comap e.hom).support : Set X[Φ]) := by
    rwa [he, Fan.support_boundaryIdeal]
  rw [support_comap, TopologicalSpace.Closeds.coe_preimage] at hmem
  let q := CodimensionOnePoint.mapOfIsOpenImmersion e.hom p[Φ,hΦ,ρ]
  have hq : q ∈ Set.range (Ψ.rayBoundaryPoint hΨ) := by
    rw [Ψ.range_rayBoundaryPoint hΨ inferInstance]
    simpa only [q, Set.mem_ofPred_eq, CodimensionOnePoint.coe_mapOfIsOpenImmersion,
      ← Set.mem_compl_iff, ← Fan.support_boundaryIdeal, Set.mem_preimage] using hmem
  obtain ⟨τ, hτ⟩ := hq
  exact ⟨τ, by simpa only [q, CodimensionOnePoint.coe_mapOfIsOpenImmersion] using
    (congrArg Subtype.val hτ).symm⟩

include he in
private theorem exists_boundary_ray_equiv :
    ∃ r : Φ.Ray ≃ Ψ.Ray, ∀ ρ, e.hom (p[Φ,hΦ,ρ]).val = (p[Ψ,hΨ,r ρ]).val := by
  classical
  choose r hr using exists_rayBoundaryPoint_image hΦ hΨ e he
  have hinv : (D[Φ,inferInstance]).comap e.inv = D[Ψ,inferInstance] := by
    rw [← he, ← comap_comp, Iso.inv_hom_id, comap_id]
  refine ⟨Equiv.ofBijective r ⟨?_, ?_⟩, hr⟩
  · intro ρ τ h
    apply Φ.rayBoundaryPoint_injective hΦ
    exact Subtype.ext (e.hom.isOpenEmbedding.injective (by rw [hr, hr, h]))
  · intro τ
    obtain ⟨ρ, hρ⟩ := exists_rayBoundaryPoint_image hΨ hΦ e.symm hinv τ
    refine ⟨ρ, Ψ.rayBoundaryPoint_injective hΨ (Subtype.ext ?_)⟩
    rw [← hr, ← hρ, ← Scheme.Hom.comp_apply, Iso.symm_hom, Iso.inv_hom_id]
    simp

end BoundaryRays

section PicardRelations

variable [Nonempty Φ.cones] [Nonempty Ψ.cones]
  (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (e : X[Φ] ≅ X[Ψ])
  (r : Φ.Ray ≃ Ψ.Ray)
  (hr : ∀ ρ, e.hom (p[Φ,hΦ,ρ]).val = (p[Ψ,hΨ,r ρ]).val)

local notation "C[" F "]" => AddMonoidHom.toIntLinearMap (Fan.characterToRayDivisor F)
local notation "P[" F "," h "]" => AddMonoidHom.toIntLinearMap (Fan.rayDivisorToPicard F h)
local notation "pull" => LinearEquiv.funCongrLeft ℤ ℤ r

include hr in
private theorem pullback_rayDivisorToPicard (x : Ψ.Ray → ℤ) :
    Additive.ofMul (LineBundleClass.pullback e.hom (P[Ψ,hΨ] x).toMul) =
      P[Φ,hΦ] (pull x) := by
  let := Fintype.ofFinite Φ.Ray
  let := Fintype.ofFinite Ψ.Ray
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  let := Ψ.uniqueFactorizationMonoid_stalk_algebraicRealization hΨ
  have hprime (ρ : Φ.Ray) :
      CodimensionOnePoint.mapOfIsOpenImmersion e.hom p[Φ,hΦ,ρ] = p[Ψ,hΨ,r ρ] :=
    Subtype.ext (by simpa only [CodimensionOnePoint.coe_mapOfIsOpenImmersion] using hr ρ)
  have hclass (ρ : Φ.Ray) :
      LineBundleClass.pullback e.hom (LineBundleClass.primeDivisorClass p[Ψ,hΨ,r ρ]) =
        LineBundleClass.primeDivisorClass p[Φ,hΦ,ρ] := by
    rw [← hprime, LineBundleClass.pullback_primeDivisorClass_mapOfIsOpenImmersion]
  have hsum := r.sum_comp
    (fun τ ↦ x τ • Additive.ofMul (LineBundleClass.primeDivisorClass p[Ψ,hΨ,τ]))
  rw [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_toIntLinearMap,
    Fan.rayDivisorToPicard_apply, Fan.rayDivisorToPicard_apply, ← hsum]
  rw [← LineBundleClass.pullbackHom_apply, ← MonoidHom.toAdditive_apply_apply, map_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [map_zsmul]
  simp only [MonoidHom.toAdditive_apply_apply, LineBundleClass.pullbackHom_apply, toMul_ofMul,
    hclass, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

include hr in
private theorem exists_latticeEquiv_of_boundary_image (hc : Φ.IsComplete) (hc' : Ψ.IsComplete) :
    ∃ f : N ≃+ N', ∀ ρ, f ρ.primitiveGenerator = (r ρ).primitiveGenerator := by
  let := Φ.lattice.free
  let := Ψ.lattice.free
  let := Φ.lattice.finite
  let := Ψ.lattice.finite
  have exactΦ : Function.Exact C[Φ] P[Φ,hΦ] :=
    Φ.exact_characterToRayDivisor_rayDivisorToPicard hΦ
  have exactΨ : Function.Exact C[Ψ] P[Ψ,hΨ] :=
    Ψ.exact_characterToRayDivisor_rayDivisorToPicard hΨ
  have hker : (P[Ψ,hΨ]).ker.map (pull).toLinearMap = (P[Φ,hΦ]).ker := by
    ext x
    rw [Submodule.mem_map_equiv]
    have hx := pullback_rayDivisorToPicard hΦ hΨ e r hr ((pull).symm x)
    simp only [LinearEquiv.apply_symm_apply] at hx
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← hx]
    let pb := (LineBundleClass.pullbackEquiv e).toAdditive
    have hp (w : Additive (LineBundleClass X[Ψ])) :
        pb w = Additive.ofMul (LineBundleClass.pullback e.hom w.toMul) := by
      rw [← LineBundleClass.pullbackEquiv_apply]
      rfl
    rw [← hp]
    exact (pb.injective.eq_iff' (map_zero pb)).symm
  let a := LinearEquiv.ofInjective C[Φ] (Φ.characterToRayDivisor_injective hc)
  let b := LinearEquiv.ofInjective C[Ψ] (Ψ.characterToRayDivisor_injective hc')
  have hm : (LinearMap.range C[Ψ]).map (pull).toLinearMap = LinearMap.range C[Φ] := by
    simpa only [exactΦ.linearMap_ker_eq, exactΨ.linearMap_ker_eq] using hker
  let d := b.trans (((pull).ofSubmodules _ _ hm).trans a.symm)
  have hd (m : N' →+ ℤ) (ρ : Φ.Ray) :
      d m ρ.primitiveGenerator = m (r ρ).primitiveGenerator := by
    let y := (pull).ofSubmodules _ _ hm (b m)
    have hh : C[Φ] (d m) = pull (C[Ψ] m) := calc
      _ = (a (a.symm y) : Φ.Ray → ℤ) := rfl
      _ = (y : Φ.Ray → ℤ) := congrArg Subtype.val (a.apply_symm_apply y)
      _ = _ := rfl
    simpa only [AddMonoidHom.coe_toIntLinearMap, characterToRayDivisor_apply,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply] using congrFun hh ρ
  let l := (addMonoidHomLequivInt ℤ).symm.trans (d.trans (addMonoidHomLequivInt ℤ))
  let f := (Module.evalEquiv ℤ N).trans (l.dualMap.trans (Module.evalEquiv ℤ N').symm)
  refine ⟨f.toAddEquiv, fun ρ ↦ (Module.evalEquiv ℤ N').injective ?_⟩
  ext m
  simpa [f, l, LinearEquiv.dualMap_apply] using hd m.toAddMonoidHom ρ

end PicardRelations

private theorem exists_fanEquiv_of_boundary_image [Nonempty Φ.cones] [Nonempty Ψ.cones]
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete) (hc' : Ψ.IsComplete)
    (hN' : Module.finrank ℤ N' = 2)
    (e : X[Φ] ≅ X[Ψ]) (r : Φ.Ray ≃ Ψ.Ray)
    (hr : ∀ ρ, e.hom (p[Φ,hΦ,ρ]).val = (p[Ψ,hΨ,r ρ]).val) :
    ∃ f : FanEquiv Φ Ψ, f.rayEquiv = r := by
  obtain ⟨l, hl⟩ := exists_latticeEquiv_of_boundary_image hΦ hΨ e r hr hc hc'
  let Ω := Φ.mapEquiv Ψ.lattice l
  let g : FanEquiv Φ Ω := Φ.mapEquivIso Ψ.lattice l
  have hgl : g.latticeEquiv = l := Φ.mapEquivIso_latticeEquiv Ψ.lattice l
  have := Ψ.lattice.free
  have := Ψ.lattice.finite
  let b : Module.Basis (Fin 2) ℤ N' := hN' ▸ Module.finBasis ℤ N'
  have hg (ρ : Φ.Ray) :
      (g.rayEquiv ρ).primitiveGenerator = (r ρ).primitiveGenerator := by
    simpa only [FanEquiv.primitiveGenerator_rayEquiv, hgl] using hl ρ
  have hΩ : Ω = Ψ := by
    apply eq_of_range_primitiveGenerator_eq b (g.isRegular_iff.mpr hΦ) hΨ
      (g.isComplete_iff.mpr hc) hc'
    have h := congrArg Set.range (show Ray.primitiveGenerator ∘ g.rayEquiv =
      Ray.primitiveGenerator ∘ r from funext hg)
    simpa only [EquivLike.range_comp] using h
  let f : FanEquiv Φ Ψ := { g with map_mem := fun σ ↦ hΩ ▸ g.map_mem σ }
  have hfl : f.latticeEquiv = l := hgl
  refine ⟨f, Equiv.ext fun ρ ↦ Ray.primitiveGenerator_injective ?_⟩
  simpa only [FanEquiv.primitiveGenerator_rayEquiv, hfl] using hl ρ

/-- An isomorphism of complete regular toric surfaces over `ℂ` preserving the
reduced boundaries is the composite of a unique fan isomorphism followed by a
unique torus translation on the target. -/
theorem existsUnique_toric_factorization_of_boundary_iso
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete) (hc' : Ψ.IsComplete)
    (_hN : Module.finrank ℤ N = 2) (hN' : Module.finrank ℤ N' = 2)
    (e : X[Φ] ≅ X[Ψ]) [e.hom.IsOver (Spec (.of ℂ))]
    (he : (D[Ψ,hc'.nonempty_cones]).comap e.hom = D[Φ,hc.nonempty_cones]) :
    letI := hc'.nonempty_cones
    ∃! q : FanEquiv Φ Ψ × (Multiplicative (N' →+ ℤ) →* ℂˣ),
      q.1.toFanHom.algebraicMap ≫ (Ψ.torusTranslation q.2).hom = e.hom := by
  let := hc.nonempty_cones
  let := hc'.nonempty_cones
  obtain ⟨r, hr⟩ := exists_boundary_ray_equiv hΦ hΨ e he
  obtain ⟨f, hfr⟩ := exists_fanEquiv_of_boundary_image hΦ hΨ hc hc' hN' e r hr
  let a := asIso f.toFanHom.algebraicMap
  let t := a.symm ≪≫ e
  have : a.hom.IsOver (Spec (.of ℂ)) :=
    inferInstanceAs (f.toFanHom.algebraicMap.IsOver (Spec (.of ℂ)))
  have : t.hom.IsOver (Spec (.of ℂ)) :=
    inferInstanceAs ((a.inv ≫ e.hom).IsOver (Spec (.of ℂ)))
  have hfix (ρ : Ψ.Ray) : (I[Ψ,hΨ,ρ]).comap t.hom = I[Ψ,hΨ,ρ] := by
    apply (Ψ.comap_rayBoundaryIdeal_eq_iff hΨ t ρ).mpr
    obtain ⟨τ, rfl⟩ := f.rayEquiv.surjective ρ
    have hτ : a.hom (p[Φ,hΦ,τ]).val = (p[Ψ,hΨ,f.rayEquiv τ]).val :=
      f.algebraicMap_rayBoundaryPoint hΦ hΨ τ
    dsimp only [t]
    rw [Iso.trans_hom, Iso.symm_hom, Scheme.Hom.comp_apply, ← hτ,
      ← Scheme.Hom.comp_apply a.hom a.inv, a.hom_inv_id]
    rw [hτ, hfr]
    simpa using hr τ
  obtain ⟨χ, hχ, huniq⟩ :=
    Ψ.existsUnique_torusTranslation_of_comap_rayBoundaryIdeal_eq hΨ hc' t hfix
  refine ⟨⟨f, χ⟩, ?_, ?_⟩
  · dsimp only
    rw [hχ, Iso.trans_hom, Iso.symm_hom]
    exact a.hom_inv_id_assoc e.hom
  · rintro ⟨g, ψ⟩ hψ
    have hg : g.rayEquiv = r := by
      apply Equiv.ext
      intro ρ
      apply Ψ.rayBoundaryPoint_injective hΨ
      apply Subtype.ext
      have hp := congrArg (fun (m : X[Φ] ⟶ X[Ψ]) ↦ m (p[Φ,hΦ,ρ]).val) hψ
      rw [Scheme.Hom.comp_apply, g.algebraicMap_rayBoundaryPoint hΦ hΨ, hr] at hp
      rw [← hp]
      exact ((Ψ.comap_rayBoundaryIdeal_eq_iff hΨ (Ψ.torusTranslation ψ) (g.rayEquiv ρ)).mp
        (Ψ.comap_rayBoundaryIdeal_torusTranslation_hom hΨ ψ (g.rayEquiv ρ))).symm
    have hgf := FanEquiv.eq_of_rayEquiv_eq hc (hg.trans hfr.symm)
    subst g
    congr 1
    apply huniq ψ
    apply Iso.ext
    exact (cancel_epi a.hom).mp (hψ.trans (a.hom_inv_id_assoc e.hom).symm)

end TauCeti.Toric.Fan

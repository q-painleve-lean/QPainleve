/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.Geometry.Toric.Fan.Boundary.Prime

import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Contraction

/-!
# Descent of isomorphisms of ordered toric models

The boundary primes retained by a nodal contraction determine which isomorphisms
of ordered toric blowup models descend to the original surfaces. The criterion
allows different labeled fans and identifies the reduced boundary downstairs.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

universe u

variable (K : Type u) [Field K] [PerfectField K]

variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  [Nonempty Φ.cones] [Nonempty Ψ.cones] (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
  {n n' : ℕ} (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
  (s : Fin n → Φ.Ray) (s' : Fin n' → Ψ.Ray) (c : Fin n → Kˣ) (d : Fin n' → Kˣ)

local notation "S" => Spec (CommRingCat.of K)
local notation "M" => internalBlowupTower K b s c
local notation "M'" => internalBlowupTower K b' s' d
local notation "B" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd M))
local notation "B'" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd M'))
local notation "R" => internalBlowupBoundaryPrimeEquiv K hΦ b s c
local notation "R'" => internalBlowupBoundaryPrimeEquiv K hΨ b' s' d

variable {X X' Y Y' : Scheme.{u}} [IsIntegral X] [IsIntegral X']
  {f : X ⟶ Spec (.of K)} {g : X' ⟶ Spec (.of K)}
  [SmoothOfRelativeDimension 2 f] [SmoothOfRelativeDimension 2 g]
  [QuasiCompact f] [QuasiCompact g]
  {D : X.IdealSheafData} {D' : X'.IdealSheafData} [IsReduced D.subscheme] [IsReduced D'.subscheme]
  {m m' : ℕ} {T : BlowupTower X m Y} {U : BlowupTower X' m' Y'}
  {p : (internalBlowupTower K b s c).1 ⟶ X}
  {q : (internalBlowupTower K b' s' d).1 ⟶ X'}

/-- An isomorphism of ordered toric models carrying the strict primes according to a
ray equivalence descends if and only if that equivalence matches the surviving rays.
The descent is unique, is over the base field, and identifies the reduced boundaries.
The nodal towers specify the contractions. -/
theorem existsUnique_iso_iff_eq_contractedBoundaryRays
    (hT : IsNodalBoundaryTower D f (𝟙 X) T) (hU : IsNodalBoundaryTower D' g (𝟙 X') U)
    (e : Y ≅ M.1) (e' : Y' ≅ M'.1)
    (hp : e.hom ≫ p = T.toBase) (hq : e'.hom ≫ q = U.toBase)
    (t : M.1 ≅ M'.1) (hover : p ≫ f = t.hom ≫ q ≫ g)
    (hD : (D.comap p).support = (B).support) (hD' : (D'.comap q).support = (B').support)
    (τ : Φ.Ray ≃ Ψ.Ray) (hτ : ∀ ρ, t.hom (R ρ).val = (R' (τ ρ)).val) :
    (∃! a : X ≅ X', p ≫ a.hom = t.hom ≫ q ∧ a.hom ≫ g = f ∧ D'.comap a.hom = D) ↔
      ∀ ρ : Φ.Ray, p (R ρ).val ∈ D.boundaryPrimes ↔ q (R' (τ ρ)).val ∈ D'.boundaryPrimes := by
  symm
  constructor
  · intro hkeep
    let u := e ≪≫ t ≪≫ e'.symm
    have hproj : u.hom ≫ U.toBase = e.hom ≫ t.hom ≫ q := by
      simp only [u, Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hq, Iso.inv_hom_id_assoc]
    have huOver : T.toBase ≫ f = u.hom ≫ U.toBase ≫ g := by
      rw [← hp, Category.assoc, hover, ← (reassoc_of% hproj) g]
    have hB : (D.comap T.toBase).support = ((B).comap e.hom).support := by
      rw [← hp, comap_comp, support_comap, hD, ← support_comap]
    have htB : (B).support = ((B').comap t.hom).support := by
      apply SetLike.coe_injective
      apply (Set.image_injective.mpr t.hom.injective)
      rw [support_comap, Closeds.coe_preimage, Set.image_preimage_eq _ t.hom.surjective,
        coe_support_ker_boundaryι_eq_iUnion_closure K hΦ b s c,
        coe_support_ker_boundaryι_eq_iUnion_closure K hΨ b' s' d,
        Set.image_iUnion]
      simpa only [← t.hom.isClosedEmbedding.closure_image_eq, Set.image_singleton, hτ] using
        τ.surjective.iUnion_comp (fun ρ ↦ closure {(R' ρ).val})
    have hsupp : (D.comap T.toBase).support = ((D'.comap U.toBase).comap u.hom).support := by
      rw [hB, ← comap_comp, hproj, comap_comp, comap_comp, support_comap B,
        support_comap ((D'.comap q).comap t.hom), support_comap (D'.comap q), hD',
        ← support_comap B', ← htB]
    have hprimes (x : Y) (hx : x ∈ (D.comap T.toBase).boundaryPrimes) :
        T.toBase x ∈ D.boundaryPrimes ↔ U.toBase (u.hom x) ∈ D'.boundaryPrimes := by
      have hx' : e.hom x ∈ (B).boundaryPrimes := by
        rw [mem_boundaryPrimes, coheight_eq_of_isOpenImmersion e.hom]
        rw [mem_boundaryPrimes, hB, support_comap] at hx
        exact hx
      obtain ⟨ρ, hρ⟩ := (R).surjective ⟨e.hom x, hx'⟩
      have heρ : (R ρ).val = e.hom x := congrArg Subtype.val hρ
      have h := hkeep ρ
      rw [heρ, ← hτ, heρ, ← Scheme.Hom.comp_apply e.hom p, hp] at h
      simpa only [← Scheme.Hom.comp_apply, Category.assoc, hproj] using h
    obtain ⟨a, ⟨ha, haOver, haD⟩, hu⟩ :=
      hT.existsUnique_iso_of_eq_surviving_boundaryPrimes hU u huOver hsupp hprimes
    refine ⟨a, ⟨(cancel_epi e.hom).mp ?_, haOver, haD⟩, fun a' h ↦
      hu a' ⟨?_, h.2⟩⟩
    · rw [← Category.assoc, hp, ha, hproj]
    · rw [hproj, ← h.1, ← Category.assoc, hp]
  · rintro ⟨a, ⟨ha, -, haD⟩, -⟩ ρ
    have h := congrArg (fun k : M.1 ⟶ X' ↦ k (R ρ).val) ha
    simp only [Scheme.Hom.comp_apply, hτ] at h
    rw [← h, ← haD, mem_boundaryPrimes, mem_boundaryPrimes,
      coheight_eq_of_isOpenImmersion a.hom, support_comap]
    rfl

end TauCeti.Toric.Fan

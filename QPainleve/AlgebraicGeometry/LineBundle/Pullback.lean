/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import QPainleve.AlgebraicGeometry.LineBundle.Ratio
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import QPainleve.AlgebraicGeometry.LineBundle.Frame
import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Nonvanishing under pullback of line bundles

An affine open framed by a section of a line bundle pulls back to an open framed by
the pulled-back section. The preservation of the frame uses
`Scheme.Hom.isBaseChange_pullbackSectionsLE` on affine opens in the inverse image.
Ratios with respect to these frames commute with pullback.
-/

public section

open CategoryTheory Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

private theorem preimage_le_nonvanishingLocus_pullbackSections_of_isAffineOpen
    (M : Y.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]
    (g : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U) (s : Γ(M, U))
    (hs : U ≤ M.nonvanishingLocus s) :
    g ⁻¹ᵁ U ≤ ((pullback g).obj M).nonvanishingLocus (g.pullbackSections M U s) := by
  let L := (pullback g).obj M
  intro x hx
  refine (L.mem_nonvanishingLocus_iff_of_mem hx).mpr ?_
  refine (Submodule.span_singleton_eq_top_iff _ _).mpr fun m ↦ ?_
  obtain ⟨W, hxW, z, rfl⟩ := L.presheaf.exists_germ_eq m
  obtain ⟨V, hV, hxV, hle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (U := W ⊓ g ⁻¹ᵁ U) (x := x) ⟨hxW, hx⟩
  let hVU : V ≤ g ⁻¹ᵁ U := hle.trans inf_le_right
  let j : V ⟶ W := homOfLE (hle.trans inf_le_left)
  let : Algebra Γ(Y, U) Γ(X, V) := (g.appLE U V hVU).hom.toAlgebra
  let : Module Γ(Y, U) Γ(L, V) := Module.compHom _ (algebraMap Γ(Y, U) Γ(X, V))
  let : IsScalarTower Γ(Y, U) Γ(X, V) Γ(L, V) := IsScalarTower.of_compHom _ _ _
  let φ : Γ(M, U) →ₗ[Γ(Y, U)] Γ(L, V) :=
    { toFun := g.pullbackSectionsLE M U V hVU
      map_add' := map_add _
      map_smul' := fun r z ↦ (g.pullbackSectionsLE M U V hVU).map_smulₛₗ r z }
  have hφ := g.isBaseChange_pullbackSectionsLE M hU hV hVU (fun _ ↦ rfl) φ (fun _ ↦ rfl)
  let b := (Module.Basis.singleton PUnit.{1} Γ(Y, U)).map (M.sectionFrame s hs)
  have hb := (hφ.basis b).span_eq
  rw [Set.range_unique, IsBaseChange.basis_apply] at hb
  have hb' : Submodule.span Γ(X, V) {g.pullbackSectionsLE M U V hVU s} = ⊤ := by
    simpa only [b, Module.Basis.map_apply, Module.Basis.singleton_apply, sectionFrame_apply,
      one_smul, φ, LinearMap.coe_mk, AddHom.coe_mk] using hb
  obtain ⟨a, ha⟩ := (Submodule.span_singleton_eq_top_iff _ _).mp hb' (L.presheaf.map j.op z)
  refine ⟨X.presheaf.germ V x hxV a, ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply L.presheaf (homOfLE hVU) _ hxV,
    ← L.germ_smul, ← g.pullbackSectionsLE_apply, ha, TopCat.Presheaf.germ_res_apply]

private theorem preimage_nonvanishingLocus_le_pullbackSections
    (M : Y.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]
    (g : X ⟶ Y) {U : Y.Opens} (s : Γ(M, U)) :
    g ⁻¹ᵁ M.nonvanishingLocus s ≤
      ((pullback g).obj M).nonvanishingLocus (g.pullbackSections M U s) := by
  intro x hx
  obtain ⟨V, hV, hxV, hle⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (U := M.nonvanishingLocus s) (x := g x) hx
  let j : V ⟶ U := homOfLE (hle.trans (M.nonvanishingLocus_le s))
  have hs : V ≤ M.nonvanishingLocus (M.presheaf.map j.op s) := by
    rw [M.nonvanishingLocus_map]
    exact le_inf le_rfl hle
  have hv := preimage_le_nonvanishingLocus_pullbackSections_of_isAffineOpen M g hV _ hs
  rw [← g.pullbackSections_restrict M U j, nonvanishingLocus_map] at hv
  exact (hv.trans inf_le_right) hxV

/-- Pullback of a section of a line bundle pulls back its nonvanishing locus. -/
@[simp]
theorem nonvanishingLocus_pullbackSections
    (M : Y.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]
    (g : X ⟶ Y) {U : Y.Opens} (s : Γ(M, U)) :
    ((pullback g).obj M).nonvanishingLocus (g.pullbackSections M U s) =
      g ⁻¹ᵁ M.nonvanishingLocus s := by
  let L := (pullback g).obj M
  refine le_antisymm ?_ (preimage_nonvanishingLocus_le_pullbackSections M g s)
  intro x hx
  have hxU : g x ∈ U := (L.nonvanishingLocus_le _) hx
  obtain ⟨V, e, hxV⟩ := M.exists_mem_trivialization (g x)
  let W := U ⊓ V
  let i : W ⟶ U := homOfLE inf_le_left
  let j : W ⟶ V := homOfLE inf_le_right
  let t := M.presheaf.map j.op (M.trivializationGenerator e)
  have ht : M.nonvanishingLocus t = W := by
    dsimp only [t]
    rw [M.nonvanishingLocus_map, M.nonvanishingLocus_trivializationGenerator,
      inf_eq_left.mpr j.le]
  obtain ⟨r, hr⟩ := M.surjective_smul_of_le_nonvanishingLocus ht.ge (M.presheaf.map i.op s)
  have ht' : L.nonvanishingLocus (g.pullbackSections M W t) = g ⁻¹ᵁ W := by
    refine le_antisymm (L.nonvanishingLocus_le _) ?_
    conv_lhs => rw [← ht]
    exact preimage_nonvanishingLocus_le_pullbackSections M g t
  have hs := congrArg (g.pullbackSections M W) hr
  rw [map_smulₛₗ, ← g.pullbackSections_restrict M U i] at hs
  have hEq := congrArg L.nonvanishingLocus hs
  rw [L.nonvanishingLocus_smul, ht', L.nonvanishingLocus_map,
    inf_eq_left.mpr (X.basicOpen_le _), ← Scheme.preimage_basicOpen] at hEq
  have hxBasic : x ∈ g ⁻¹ᵁ Y.basicOpen r := hEq.symm ▸
    (⟨⟨hxU, hxV⟩, hx⟩ : x ∈ g ⁻¹ᵁ W ⊓ L.nonvanishingLocus (g.pullbackSections M U s))
  have hy : g x ∈ Y.basicOpen r := hxBasic
  rw [M.basicOpen_eq_inf_nonvanishingLocus i s ht.ge hr] at hy
  exact hy.2

/-- The nonvanishing locus of a pulled-back section restricted to a smaller
open is the intersection of that open with the preimage of its original locus. -/
@[simp]
theorem nonvanishingLocus_pullbackSectionsLE
    (M : Y.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]
    (g : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (hV : V ≤ g ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((pullback g).obj M).nonvanishingLocus (g.pullbackSectionsLE M U V hV s) =
      V ⊓ g ⁻¹ᵁ M.nonvanishingLocus s := by
  rw [g.pullbackSectionsLE_apply, nonvanishingLocus_map, nonvanishingLocus_pullbackSections]

/-- Pulling back a section ratio to an open in the inverse image gives the ratio
of the two pulled-back sections on that open. -/
theorem appLE_sectionRatio
    (M : Y.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]
    (g : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (hV : V ≤ g ⁻¹ᵁ U)
    (t s : Γ(M, U)) (hs : U ≤ M.nonvanishingLocus s) :
    g.appLE U V hV (M.sectionRatio t s hs) =
      ((pullback g).obj M).sectionRatio
        (g.pullbackSectionsLE M U V hV t) (g.pullbackSectionsLE M U V hV s)
        (by
          rw [nonvanishingLocus_pullbackSectionsLE]
          exact le_inf le_rfl (hV.trans (g.preimage_mono hs))) := by
  symm
  apply (sectionRatio_eq_iff _ _).mpr
  rw [← map_smulₛₗ (g.pullbackSectionsLE M U V hV), sectionRatio_smul]

/-- A global section with dense nonvanishing locus pulls back to a section with
dense nonvanishing locus along a dominant morphism from a preirreducible scheme. -/
theorem dense_nonvanishingLocus_pullbackSectionsLE_top
    (M : Y.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]
    [PreirreducibleSpace X] [Nonempty Y] (g : X ⟶ Y) [IsDominant g]
    {s : Γ(M, ⊤)} (hs : Dense (M.nonvanishingLocus s : Set Y)) :
    Dense (((pullback g).obj M).nonvanishingLocus
      (g.pullbackSectionsLE M ⊤ ⊤ g.preimage_top.ge s) : Set X) := by
  rw [nonvanishingLocus_pullbackSectionsLE, top_inf_eq]
  refine (g ⁻¹ᵁ M.nonvanishingLocus s).isOpen.dense ?_
  simpa [← Set.nonempty_preimage_iff] using
    g.denseRange.inter_open_nonempty _ (M.nonvanishingLocus s).isOpen hs.nonempty

end AlgebraicGeometry.Scheme.Modules

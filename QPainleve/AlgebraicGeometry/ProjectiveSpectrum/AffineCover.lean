/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import Mathlib.Algebra.Module.Submodule.Union
import TauCeti.Topology.KrullDimension.ClosedCover

/-!
# Affine covers of projective schemes over infinite fields

A projective scheme of dimension at most `d` over an infinite field has an affine cover
with `d + 1` members. Hyperplane complements provide the opens. At each step one hyperplane
avoids the generic points of all components of the closed subset still to cover. Its
intersection with that subset has strictly smaller dimension by Tau Ceti's
`IsOpen.topologicalKrullDim_compl_lt`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.SymmetricAlgebra (homogeneousSubmodule)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k M : Type u} [Field k] [Infinite k] [AddCommGroup M] [Module k M]
  {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule k M))

/-- A finite set of points of a scheme mapping to projective space lies in the inverse image of
one degree-one standard open. Over an infinite field, the linear forms vanishing at any one
point are a proper subspace, and finitely many such subspaces cannot cover the space of forms. -/
theorem exists_subset_preimage_basicOpen_ι {s : Set X} (hs : s.Finite) :
    ∃ m : M, s ⊆ f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule k M) (SymmetricAlgebra.ι k M m) := by
  classical
  let : Finite s := hs.to_subtype
  let V (x : s) : Submodule k M :=
    ((f x).asHomogeneousIdeal.toIdeal.restrictScalars k).comap (SymmetricAlgebra.ι k M)
  have hV (x : s) : V x ≠ ⊤ := by
    have hcover := TauCeti.SymmetricAlgebra.iSup_basicOpen_ι_eq_top k M id (by simp)
    have hx : f x ∈ ⨆ m : M,
        Proj.basicOpen (homogeneousSubmodule k M) (SymmetricAlgebra.ι k M (id m)) :=
      hcover.symm ▸ Set.mem_univ (f x)
    obtain ⟨m, hm⟩ := Opens.mem_iSup.mp hx
    intro h
    have hmV : m ∈ V x := h ▸ Submodule.mem_top
    exact (Proj.mem_basicOpen _ _ _).mp hm hmV
  obtain ⟨m, hm⟩ := Submodule.exists_forall_notMem_of_forall_ne_top V hV
  exact ⟨m, fun x hx ↦ (Proj.mem_basicOpen _ _ _).mpr (hm ⟨x, hx⟩)⟩

/-- A Noetherian scheme of dimension below `n` mapping to projective space over an infinite
field is covered by the inverse images of `n` degree-one standard opens. -/
theorem exists_basicOpen_ι_cover_of_dim_lt [NoetherianSpace X] {n : ℕ}
    (hdim : topologicalKrullDim X < n) :
    ∃ v : Fin n → M, (⨆ j, f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule k M)
      (SymmetricAlgebra.ι k M (v j))) = ⊤ := by
  classical
  induction n generalizing X with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    have : IsEmpty X := by
      refine ⟨fun x ↦ ?_⟩
      have : Nonempty (IrreducibleCloseds X) :=
        ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
      have hnonneg : 0 ≤ topologicalKrullDim X := Order.krullDim_nonneg
      exact (not_le_of_gt hdim) (by simpa using hnonneg)
    ext x
    exact isEmptyElim x
  | succ n ih =>
    by_cases hX : Nonempty X
    · obtain ⟨m, hm⟩ := f.exists_subset_preimage_basicOpen_ι
        (genericPoints.finite NoetherianSpace.finite_irreducibleComponents)
      let U := f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule k M) (SymmetricAlgebra.ι k M m)
      have hdense : Dense (U : Set X) := (dense_iff_closure_eq.mpr genericPoints.closure).mono hm
      let I := IdealSheafData.vanishingIdeal (X := X) ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
      let i := I.subschemeι
      have : NoetherianSpace I.subscheme := i.isClosedEmbedding.isInducing.noetherianSpace
      have hrange : Set.range i = (U : Set X)ᶜ := by
        rw [I.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
        rfl
      have hZ : topologicalKrullDim I.subscheme = topologicalKrullDim ↥((U : Set X)ᶜ) :=
        (i.isClosedEmbedding.isEmbedding.toHomeomorph.trans
          (Homeomorph.setCongr hrange)).isHomeomorph.topologicalKrullDim_eq _
      have hn : topologicalKrullDim I.subscheme < n := by
        rw [hZ]
        exact (U.isOpen.topologicalKrullDim_compl_lt hdense (ne_top_of_lt hdim)).trans_le
          (ENat.WithBot.lt_add_one_iff.mp (by simpa using hdim))
      -- The forms chosen on the complement are linear forms on the original projective space.
      obtain ⟨v, hv⟩ := ih (i ≫ f) hn
      refine ⟨Fin.cons m v, top_unique fun x _ ↦ ?_⟩
      by_cases hx : x ∈ U
      · exact Opens.mem_iSup.mpr ⟨0, by simpa only [Fin.cons_zero] using hx⟩
      · have hxrange : x ∈ Set.range i := hrange.symm ▸ hx
        obtain ⟨z, rfl⟩ := hxrange
        have hz : z ∈ ⨆ j, (i ≫ f) ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule k M)
            (SymmetricAlgebra.ι k M (v j)) := hv.symm ▸ Set.mem_univ z
        obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hz
        exact Opens.mem_iSup.mpr ⟨j.succ, by
          simpa only [Fin.cons_succ, Hom.mem_preimage, Hom.comp_apply] using hj⟩
    · have : IsEmpty X := not_nonempty_iff.mp hX
      exact ⟨fun _ ↦ 0, by ext x; exact isEmptyElim x⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

/-- A projective scheme over an infinite field of dimension strictly below `n` has a cover
by `n` affine opens. In particular a projective `d`-fold has a cover by `d + 1` affine opens. -/
theorem exists_affineCover_of_dim_lt {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k] {n : ℕ} (hdim : topologicalKrullDim X < n) :
    ∃ U : Fin n → X.Opens, (∀ j, IsAffineOpen (U j)) ∧ (⨆ j, U j) = ⊤ := by
  obtain ⟨M, _, _, _, f, hf, _⟩ :=
    IsProjectiveOver.exists_isClosedImmersion (R := k) (X := X)
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  have : NoetherianSpace X := f.isClosedEmbedding.isInducing.noetherianSpace
  obtain ⟨v, hv⟩ := f.exists_basicOpen_ι_cover_of_dim_lt hdim
  exact ⟨_, fun j ↦ (Proj.isAffineOpen_basicOpen _ _
    (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule k M (v j)) Nat.one_pos).preimage f, hv⟩

end AlgebraicGeometry.Scheme

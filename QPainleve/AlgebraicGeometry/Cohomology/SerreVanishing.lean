/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Cohomology.ProjectiveSpace.SerreVanishing
public import QPainleve.AlgebraicGeometry.LineBundle.Ample

import QPainleve.AlgebraicGeometry.LineBundle.GlobalGeneration
import QPainleve.AlgebraicGeometry.LineBundle.Power

/-!
# Serre vanishing for ample twists

On a proper scheme over a Noetherian ring, sufficiently high powers of an ample line
bundle kill positive cohomology of a coherent sheaf, with one bound for every degree.
This is the vanishing statement of the Stacks Project,
[Lemma 30.16.1(4)](https://stacks.math.columbia.edu/tag/0B5T). The proof applies the finite
projective comparison to a positive power of the ample bundle.
-/

public section

open AlgebraicGeometry Filter CategoryTheory MonoidalCategory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules
open LineBundleClass (mk_tensorPow mk_eq_mk_iff)

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **Serre vanishing.** On a proper scheme over a Noetherian ring, every sufficiently high
ample twist of a quasi-coherent sheaf of finite type has vanishing cohomology in all positive
degrees. -/
theorem eventually_subsingleton_cohomology_tensorPow_of_isAmple
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (L : InvertibleSheaf X) (hL : (LineBundleClass.mk L).IsAmple) :
    ∀ᶠ m : ℕ in atTop, ∀ q : ℕ, 0 < q →
      Subsingleton (Cohomology (F ⊗ (L.tensorPow m).obj) q) := by
  obtain ⟨d, hd, ι, _, g, _, _, e⟩ := hL.exists_finite_to_proj_tensorPow f
  exact g.eventually_subsingleton_cohomology_tensorPow_of_finite_to_proj
    (Finsupp.basisSingleOne (R := R) (ι := ι)) F L hd e

/-- Some positive power of an ample line bundle on a proper scheme over an affine
Noetherian base has vanishing first cohomology and a finite affine cover by
nonvanishing loci of global sections of that same power. -/
theorem exists_tensorPow_affine_cover_and_subsingleton_cohomology_one
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (H : InvertibleSheaf X) (ha : (LineBundleClass.mk H).IsAmple) :
    ∃ m : ℕ, 0 < m ∧
      let L := H.tensorPow m
      Subsingleton (Cohomology L.obj 1) ∧
      ∃ (ι : Type u) (_ : Finite ι) (t : ι → Γ(L.obj, ⊤)),
        (⨆ i, L.obj.nonvanishingLocus (t i)) = ⊤ ∧
        ∀ i, IsAffineOpen (L.obj.nonvanishingLocus (t i)) := by
  classical
  obtain ⟨d, hd, S, hS, hcover⟩ := ha.exists_finset_isAffineOpen_nonvanishingLocus_tensorPow
  choose hA v hv using fun i : S ↦ hcover i i.property
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (f.eventually_subsingleton_cohomology_tensorPow_of_isAmple (𝟙_ _) H ha)
  let l := N + 1
  let L := H.tensorPow (d * l)
  have hl : 0 < l := Nat.succ_pos N
  have hdl : N ≤ d * l := by
    exact (Nat.le_succ N).trans (Nat.le_mul_of_pos_left l hd)
  let φ := (cohomologyFunctor _ 1).mapIso (λ_ L.obj).symm
  have hvan : Subsingleton (Cohomology L.obj 1) :=
    @Function.Injective.subsingleton _ _ _ φ.addCommGroupIsoToAddEquiv.injective
      (hN _ hdl 1 Nat.one_pos)
  have hclass : LineBundleClass.mk ((H.tensorPow d).tensorPow l) = LineBundleClass.mk L := by
    simp only [L, mk_tensorPow, pow_mul]
  let α := ((H.tensorPow d).tensorPowObjIso l).symm ≪≫ (mk_eq_mk_iff.mp hclass).some
  let t (i : S) := α.hom.app ⊤ (tensorPowSection (v i) l)
  have ht (i : S) : L.obj.nonvanishingLocus (t i) = i.val := by
    have : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (H.tensorPow d).obj :=
      (H.tensorPow d).property
    have : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X
        (TauCeti.tensorPow (H.tensorPow d).obj l) :=
      TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_tensorPow _ _
    rw [nonvanishingLocus_hom_app, nonvanishingLocus_tensorPowSection _ hl, hv i]
  refine ⟨d * l, Nat.mul_pos hd hl, hvan, S, inferInstance, t, ?_, fun i ↦ ht i ▸ hA i⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨U, hU, hx⟩ := Opens.mem_sSup.mp (hS.symm ▸ Opens.mem_top x)
  have hx' : x ∈ L.obj.nonvanishingLocus (t ⟨U, hU⟩) :=
    (ht ⟨U, hU⟩).symm ▸ hx
  exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx'⟩

end AlgebraicGeometry.Scheme.Hom

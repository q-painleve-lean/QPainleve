/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.TensorProduct
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.LineBundle.Power
import TauCeti.AlgebraicGeometry.Modules.Localization
import TauCeti.Algebra.Group.Action.Pow

/-!
# Extending sections after twisting by a line bundle

On a quasi-compact quasi-separated scheme, a section of a quasi-coherent module over the
nonvanishing locus of a line bundle section extends to a global section after twisting.
On a finite affine cover trivializing the bundle this amounts to clearing denominators.
A further power kills the differences on overlaps, so the local extensions glue.
The two localization steps use Tau Ceti's `Scheme.Modules.exists_pow_smul_eq_map`
and `Scheme.Modules.exists_pow_smul_eq_zero_of_isCompact`.

## References

* [The Stacks Project, Lemma 28.18.2](https://stacks.math.columbia.edu/tag/01PW).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open TauCeti

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M L : X.Modules} {U V : X.Opens}

/-- An iterated twist by a line bundle is the tensor product with its existing tensor power. -/
def tensorTwistIsoTensorPow (M : X.Modules) (L : TauCeti.AlgebraicGeometry.InvertibleSheaf X)
    (n : ℕ) : M.tensorTwist L.obj n ≅ M ⊗ (L.tensorPow n).obj := by
  induction n with
  | zero =>
    rw [L.tensorPow_zero]
    exact (ρ_ M).symm ≪≫ (tensorLeft M).mapIso
      (TauCeti.AlgebraicGeometry.InvertibleSheaf.trivialObjIsoUnit X).symm
  | succ n ih =>
    rw [L.tensorPow_succ]
    exact (tensorRight L.obj).mapIso ih ≪≫ (α_ M (L.tensorPow n).obj L.obj) ≪≫
      (tensorLeft M).mapIso ((L.tensorPow n).tensorProductObjIso L).symm

section Extension

private lemma comp_leTop (i : V ⟶ U) : i ≫ U.leTop = V.leTop :=
  Subsingleton.elim _ _

variable [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L]

private lemma exists_affine_cover_frame [CompactSpace X] :
    ∃ (ι : Type u) (_ : Fintype ι) (W : ι → X.Opens),
      (⨆ i, W i) = ⊤ ∧ (∀ i, IsAffineOpen (W i)) ∧
      ∀ i, ∃ b : Γ(L, W i), W i ≤ L.nonvanishingLocus b := by
  classical
  have frame (x : X) : ∃ W : X.Opens, x ∈ W ∧ IsAffineOpen W ∧
      ∃ b : Γ(L, W), W ≤ L.nonvanishingLocus b := by
    obtain ⟨V, t, hxV⟩ := exists_mem_trivialization L x
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
    let b := L.presheaf.map (homOfLE hWV : W ⟶ V).op (trivializationGenerator L t)
    exact ⟨W, hxW, hW, b, by
      simp only [b, nonvanishingLocus_map, nonvanishingLocus_trivializationGenerator]
      exact le_inf le_rfl hWV⟩
  choose W hx ha hb using frame
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (W x : Set X)) (fun x ↦ (W x).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨t, inferInstance, fun i ↦ W i, top_unique fun x _ ↦ ?_,
    fun i ↦ ha i, fun i ↦ hb i⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
  obtain ⟨hit, hix⟩ := Set.mem_iUnion.mp hi
  exact Opens.mem_iSup.mpr ⟨⟨i, hit⟩, hix⟩

private lemma exists_coordinate_of_frame (s : Γ(L, ⊤)) (b : Γ(L, U))
    (hb : U ≤ L.nonvanishingLocus b) :
    ∃ f : Γ(X, U), L.presheaf.map U.leTop.op s = f • b ∧
      X.basicOpen f = U ⊓ L.nonvanishingLocus s := by
  obtain ⟨f, hf⟩ := surjective_smul_of_le_nonvanishingLocus hb (L.presheaf.map U.leTop.op s)
  refine ⟨f, hf.symm, ?_⟩
  have hb' : L.nonvanishingLocus b = U := le_antisymm (L.nonvanishingLocus_le b) hb
  have h := congrArg L.nonvanishingLocus hf
  rwa [nonvanishingLocus_smul, nonvanishingLocus_map, hb', inf_eq_left.mpr (X.basicOpen_le f)] at h

private lemma exists_local_extension [M.IsQuasicoherent] (s : Γ(L, ⊤))
    (x : Γ(M, L.nonvanishingLocus s)) (hU : IsAffineOpen U)
    (b : Γ(L, U)) (hb : U ≤ L.nonvanishingLocus b) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ y : Γ(M.tensorTwist L n, U),
      (M.tensorTwist L n).presheaf.map (homOfLE inf_le_left).op y =
        tensorSectionPow (L.presheaf.map (U ⊓ L.nonvanishingLocus s).leTop.op s) n
          (M.presheaf.map (homOfLE inf_le_right).op x) := by
  obtain ⟨f, hf, hfopen⟩ := exists_coordinate_of_frame s b hb
  let a : U ⊓ L.nonvanishingLocus s ⟶ U := homOfLE inf_le_left
  let x' : Γ(M, U ⊓ L.nonvanishingLocus s) := M.presheaf.map (homOfLE inf_le_right).op x
  obtain ⟨n₀, y₀, hy₀⟩ := M.exists_pow_smul_eq_map hU f hfopen inf_le_left x'
  refine ⟨n₀, fun n hn ↦ ?_⟩
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨tensorSectionPow b n₀ y₀, ?_⟩
    have hfa : L.presheaf.map (U ⊓ L.nonvanishingLocus s).leTop.op s =
        X.presheaf.map a.op f • L.presheaf.map a.op b := by
      have hres := (Functor.map_comp_apply L.presheaf U.leTop.op a.op s).symm
      rw [← op_comp, comp_leTop a] at hres
      exact hres.symm.trans ((congrArg (L.presheaf.map a.op) hf).trans (L.map_smul a f b))
    rw [map_tensorSectionPow, hfa, tensorSectionPow_smul_section, hy₀]
  | succ n hn ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨tensorSection y (L.presheaf.map U.leTop.op s), ?_⟩
    simp only [map_tensorSection, hy, ← Functor.map_comp_apply, ← op_comp, comp_leTop]
    exact (tensorSectionPow_succ _ _ _).symm

private lemma tensorSectionPow_eq_zero_on_overlap [M.IsQuasicoherent] (s : Γ(L, ⊤))
    (hU : IsCompact (U : Set X)) (b : Γ(L, U)) (hb : U ≤ L.nonvanishingLocus b)
    (x : Γ(M, U))
    (hx : M.presheaf.map (homOfLE (inf_le_left : U ⊓ L.nonvanishingLocus s ≤ U)).op x = 0) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, tensorSectionPow (L.presheaf.map U.leTop.op s) n x = 0 := by
  obtain ⟨f, hf, hfopen⟩ := exists_coordinate_of_frame s b hb
  have hrestrict (V : X.Opens) (hVU : V ≤ U) (hV : V = U ⊓ L.nonvanishingLocus s) :
      M.presheaf.map (homOfLE hVU).op x = 0 := by
    subst V
    exact hx
  have hx' : M.basicOpenRestrict f x = 0 :=
    (basicOpenRestrict_apply M f x).trans (hrestrict _ (X.basicOpen_le f) hfopen)
  obtain ⟨n₀, hn₀⟩ := M.exists_pow_smul_eq_zero_of_isCompact hU f x hx'
  refine ⟨n₀, fun n hn ↦ ?_⟩
  rw [hf, tensorSectionPow_smul_section, TauCeti.pow_smul_eq_zero_of_le hn hn₀, map_zero]

private lemma glue_local_extensions [QuasiSeparatedSpace X] [M.IsQuasicoherent]
    (s : Γ(L, ⊤)) {ι : Type u} [Finite ι]
    (W : ι → X.Opens) (hW : (⨆ i, W i) = ⊤) (ha : ∀ i, IsAffineOpen (W i))
    (b : ∀ i, Γ(L, W i)) (hb : ∀ i, W i ≤ L.nonvanishingLocus (b i))
    (y : ∀ i, Γ(M, W i))
    (hy : ∀ i j,
      M.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
        W i ⊓ W j ⊓ L.nonvanishingLocus s ≤ W i)).op (y i) =
      M.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
        W i ⊓ W j ⊓ L.nonvanishingLocus s ≤ W j)).op (y j)) :
    ∃ k : ℕ, ∃ t : Γ(M.tensorTwist L k, ⊤), ∀ i,
      (M.tensorTwist L k).presheaf.map (W i).leTop.op t =
        tensorSectionPow (L.presheaf.map (W i).leTop.op s) k (y i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hkill (p : ι × ι) : ∃ k₀ : ℕ, ∀ k ≥ k₀,
      tensorSectionPow (L.presheaf.map (W p.1 ⊓ W p.2).leTop.op s) k
        (M.presheaf.map (homOfLE inf_le_left).op (y p.1) -
          M.presheaf.map (homOfLE inf_le_right).op (y p.2)) = 0 := by
    let c : W p.1 ⊓ W p.2 ⟶ W p.1 := homOfLE inf_le_left
    let b' := L.presheaf.map c.op (b p.1)
    have hb' : W p.1 ⊓ W p.2 ≤ L.nonvanishingLocus b' := by
      simp only [b', nonvanishingLocus_map]
      exact le_inf le_rfl (c.le.trans (hb p.1))
    refine tensorSectionPow_eq_zero_on_overlap s
      ((ha p.1).isCompact.inter_of_isOpen (ha p.2).isCompact (W p.1).isOpen (W p.2).isOpen)
      b' hb' _ ?_
    simpa only [CategoryTheory.Functor.map_comp_apply, map_sub, sub_eq_zero,
      ← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using hy p.1 p.2
  choose k₀ hk₀ using hkill
  let k := Finset.univ.sup k₀
  let A := M.tensorTwist L k
  let z (i : ι) := tensorSectionPow (L.presheaf.map (W i).leTop.op s) k (y i)
  have hz : TopCat.Presheaf.IsCompatible A.presheaf W z := by
    intro i j
    have h := hk₀ (i, j) k (Finset.le_sup (Finset.mem_univ (i, j)))
    rw [map_sub, sub_eq_zero] at h
    -- The intersection maps in the sheaf compatibility condition are the two inclusions.
    change A.presheaf.map (homOfLE inf_le_left).op (z i) =
      A.presheaf.map (homOfLE inf_le_right).op (z j)
    simpa only [A, z, map_tensorSectionPow, ← Functor.map_comp_apply, ← op_comp, comp_leTop] using h
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨A.presheaf, A.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X) W ⊤
    (fun i ↦ (W i).leTop) hW.ge z hz
  exact ⟨k, t, ht⟩

private theorem exists_extension_tensorSectionPow [CompactSpace X] [QuasiSeparatedSpace X]
    [M.IsQuasicoherent] (s : Γ(L, ⊤)) (x : Γ(M, L.nonvanishingLocus s)) :
    ∃ (n : ℕ) (t : Γ(M.tensorTwist L n, ⊤)),
      (M.tensorTwist L n).presheaf.map (L.nonvanishingLocus s).leTop.op t =
        tensorSectionPow (L.presheaf.map (L.nonvanishingLocus s).leTop.op s) n x := by
  classical
  let D := L.nonvanishingLocus s
  obtain ⟨ι, _, W, hW, ha, hb⟩ := exists_affine_cover_frame (X := X) (L := L)
  choose b hb using hb
  choose n₀ hn₀ using fun i ↦ exists_local_extension s x (ha i) (b i) (hb i)
  let N := Finset.univ.sup n₀
  choose y hy using fun i ↦ hn₀ i N (Finset.le_sup (Finset.mem_univ i))
  let A := M.tensorTwist L N
  have : L.IsQuasicoherent :=
    TauCeti.AlgebraicGeometry.InvertibleSheaf.isQuasicoherent_obj ⟨L, inferInstance⟩
  have : A.IsQuasicoherent := isQuasicoherent_tensorTwist N
  have hy' (i j : ι) :
      A.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
        W i ⊓ W j ⊓ D ≤ W i)).op (y i) =
      A.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
        W i ⊓ W j ⊓ D ≤ W j)).op (y j) := by
    have h₁ := congrArg ((M.tensorTwist L N).presheaf.map (homOfLE
      (inf_le_inf_right D (inf_le_left : W i ⊓ W j ≤ W i))).op) (hy i)
    have h₂ := congrArg ((M.tensorTwist L N).presheaf.map (homOfLE
      (inf_le_inf_right D (inf_le_right : W i ⊓ W j ≤ W j))).op) (hy j)
    simp only [map_tensorSectionPow, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp,
      comp_leTop] at h₁ h₂
    exact h₁.trans h₂.symm
  obtain ⟨k, t, ht⟩ := glue_local_extensions s W hW ha b hb y hy'
  let B := A.tensorTwist L k
  have hD : B.presheaf.map D.leTop.op t =
      tensorSectionPow (L.presheaf.map D.leTop.op s) k
        (tensorSectionPow (L.presheaf.map D.leTop.op s) N x) := by
    refine TopCat.Sheaf.eq_of_locally_eq'
      (⟨B.presheaf, B.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
      (fun i ↦ W i ⊓ D) D (fun i ↦ homOfLE inf_le_right)
      (by rw [← iSup_inf_eq, hW, top_inf_eq]) _ _ fun i ↦ ?_
    have h := congrArg (((M.tensorTwist L N).tensorTwist L k).presheaf.map
      (homOfLE (inf_le_left : W i ⊓ D ≤ W i)).op) (ht i)
    -- Use the underlying presheaf to compare the two restrictions to the chart.
    change B.presheaf.map (homOfLE (inf_le_right : W i ⊓ D ≤ D)).op (B.presheaf.map D.leTop.op t) =
      B.presheaf.map (homOfLE (inf_le_right : W i ⊓ D ≤ D)).op _
    simpa only [B, A, map_tensorSectionPow, hy i, ← Functor.map_comp_apply, ← op_comp,
      comp_leTop] using h
  let e := eqToIso (tensorTwist_add M L N k)
  refine ⟨N + k, e.inv.app ⊤ t, ?_⟩
  have h := e.inv.mapPresheaf.naturality_apply D.leTop.op t
  exact h.symm.trans ((congrArg (e.inv.app D) hD).trans
    ((congrArg (e.inv.app D) (tensorSectionPow_add _ N k x).symm).trans
      (((SheafOfModules.evaluation _ (op D)).mapIso e).hom_inv_id_apply _)))

/-- A section of a quasi-coherent module over the nonvanishing locus of a line bundle
section `s` extends globally after tensoring by any sufficiently large power of `s`. -/
theorem eventually_exists_extension_tensorSectionPow [CompactSpace X] [QuasiSeparatedSpace X]
    [M.IsQuasicoherent] (s : Γ(L, ⊤)) (x : Γ(M, L.nonvanishingLocus s)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ t : Γ(M.tensorTwist L n, ⊤),
      (M.tensorTwist L n).presheaf.map (L.nonvanishingLocus s).leTop.op t =
        tensorSectionPow (L.presheaf.map (L.nonvanishingLocus s).leTop.op s) n x := by
  obtain ⟨n₀, t, ht⟩ := exists_extension_tensorSectionPow s x
  refine ⟨n₀, fun n hn ↦ ?_⟩
  induction n, hn using Nat.le_induction with
  | base => exact ⟨t, ht⟩
  | succ n hn ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨tensorSection t s, ?_⟩
    simp only [map_tensorSection, ht]
    exact (tensorSectionPow_succ _ _ _).symm

end Extension

end AlgebraicGeometry.Scheme.Modules

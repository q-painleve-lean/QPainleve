/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.RelativelyAmple
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.LineBundle.GlobalGeneration
import QPainleve.AlgebraicGeometry.LineBundle.Pullback
import QPainleve.AlgebraicGeometry.LineBundle.SectionExtension
import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Pullback

/-!
# Twisting a relatively ample line bundle by an ample line bundle on the base

A relatively ample line bundle becomes ample after twisting by the pullback of any sufficiently
large power of an ample line bundle on the base. Local sections over affine nonvanishing loci
extend after twisting. A finite subcover gives a uniform exponent, and the global generation
of high powers of the base line bundle gives every sufficiently large exponent.

The proof follows [Stacks Project, Lemma 29.38.7](https://stacks.math.columbia.edu/tag/0892).
-/

public section

open AlgebraicGeometry CategoryTheory Filter MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple

open _root_.AlgebraicGeometry Scheme.Modules

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {a : LineBundleClass X}

private theorem exists_affine_nonvanishing_over (ha : a.IsRelativelyAmple f)
    {V : Y.Opens} (hV : IsAffineOpen V) {x : X} (hx : x ∈ f ⁻¹ᵁ V) :
    ∃ (m : ℕ), 0 < m ∧ ∃ (K : InvertibleSheaf X), LineBundleClass.mk K = a ^ m ∧
      ∃ s : Γ(K.obj, f ⁻¹ᵁ V),
        x ∈ K.obj.nonvanishingLocus s ∧ IsAffineOpen (K.obj.nonvanishingLocus s) := by
  let U := f ⁻¹ᵁ V
  let j := U.ι
  obtain ⟨m, hm, H⟩ := (ha.isAmple_pullback V hV).exists_pos_forall_mk_eq ⟨x, hx⟩
  obtain ⟨K, hK⟩ := mk_surjective (a ^ m)
  let P := (InvertibleSheaf.pullback j).obj K
  have hP : LineBundleClass.mk P = (pullback j a) ^ m := by
    rw [← pullback_pow, ← hK, pullback_mk]
  obtain ⟨t, ht, htA⟩ := H P hP
  let e : P.obj ≅ (Scheme.Modules.pullback j).obj K.obj :=
    eqToIso (InvertibleSheaf.pullback_obj_obj j K)
  obtain ⟨s, hs⟩ := (bijective_pullbackSectionsLE_ι K.obj U ⊤ rfl).surjective (e.hom.app ⊤ t)
  have he : P.obj.nonvanishingLocus t = j ⁻¹ᵁ K.obj.nonvanishingLocus s := by
    rw [← nonvanishingLocus_hom_app e, ← hs, nonvanishingLocus_pullbackSectionsLE, top_inf_eq]
  refine ⟨m, hm, K, hK, s, ?_, ?_⟩
  · rwa [he] at ht
  · apply IsAffineOpen.image_of_isOpenImmersion (f := j) at htA
    rwa [he, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (K.obj.nonvanishingLocus_le s)] at htA

private theorem exists_affine_nonvanishing_over_section (ha : a.IsRelativelyAmple f)
    (B : InvertibleSheaf Y) (s : Γ(B.obj, ⊤)) {V : Y.Opens}
    (hs : B.obj.nonvanishingLocus s = V) (hV : IsAffineOpen V) {x : X} (hx : x ∈ f ⁻¹ᵁ V) :
    let L := (InvertibleSheaf.pullback f).obj B
    ∃ (m : ℕ), 0 < m ∧ ∃ (K : InvertibleSheaf X), LineBundleClass.mk K = a ^ m ∧
      ∃ (s' : Γ(L.obj, ⊤)) (t : Γ(K.obj, L.obj.nonvanishingLocus s')),
        x ∈ K.obj.nonvanishingLocus t ∧ IsAffineOpen (K.obj.nonvanishingLocus t) := by
  dsimp only
  let L := (InvertibleSheaf.pullback f).obj B
  let e : (Scheme.Modules.pullback f).obj B.obj ≅ L.obj :=
    eqToIso (InvertibleSheaf.pullback_obj_obj f B).symm
  have htop : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := by simp
  let s' : Γ(L.obj, ⊤) := e.hom.app ⊤ (f.pullbackSectionsLE B.obj ⊤ ⊤ htop s)
  have hs' : L.obj.nonvanishingLocus s' = f ⁻¹ᵁ V :=
    (nonvanishingLocus_hom_app e _).trans
      ((nonvanishingLocus_pullbackSectionsLE B.obj f htop s).trans (by rw [top_inf_eq, hs]))
  obtain ⟨m, hm, K, hK, t, hxt, htA⟩ := ha.exists_affine_nonvanishing_over hV hx
  refine ⟨m, hm, K, hK, s', ?_⟩
  rw [hs']
  exact ⟨t, hxt, htA⟩

private theorem exists_isAmple_mul_pullback_pow (ha : a.IsRelativelyAmple f)
    {A : InvertibleSheaf Y} (hA : (LineBundleClass.mk A).IsAmple) :
    ∃ n : ℕ, (a * pullback f (LineBundleClass.mk A) ^ n).IsAmple := by
  classical
  have := hA.compactSpace
  have := hA.quasiSeparatedSpace
  have := ha.quasiCompact
  have := ha.quasiSeparated
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨d, _, S, hS, hcover⟩ := hA.exists_finset_isAffineOpen_nonvanishingLocus_tensorPow
  let B := A.tensorPow d
  let L := (InvertibleSheaf.pullback f).obj B
  have hloc (x : X) : ∃ (m : ℕ), 0 < m ∧ ∃ (K : InvertibleSheaf X), LineBundleClass.mk K = a ^ m ∧
      ∃ (s : Γ(L.obj, ⊤)) (t : Γ(K.obj, L.obj.nonvanishingLocus s)),
        x ∈ K.obj.nonvanishingLocus t ∧ IsAffineOpen (K.obj.nonvanishingLocus t) := by
    obtain ⟨V, hVS, hxV⟩ := Opens.mem_sSup.mp (hS.symm ▸ Opens.mem_top (f x))
    obtain ⟨hV, s, hs⟩ := hcover V hVS
    exact ha.exists_affine_nonvanishing_over_section B s hs hV hxV
  choose m hm K hK s t hx hAffine using hloc
  let W (x : X) := (K x).obj.nonvanishingLocus (t x)
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (W x : Set X)) (fun x ↦ (W x).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  have hExtend (i : T) :
      ∀ᶠ q : ℕ in atTop, ∃ z : Γ((K i).obj ⊗ TauCeti.tensorPow L.obj (m i * q), ⊤),
        ((K i).obj ⊗ TauCeti.tensorPow L.obj (m i * q)).nonvanishingLocus z = W i := by
    have hmul : Tendsto (fun q : ℕ ↦ m i * q) atTop atTop :=
      tendsto_atTop_mono (fun q ↦ Nat.le_mul_of_pos_left q (hm i)) tendsto_id
    exact hmul.eventually (eventually_exists_nonvanishingLocus_tensorPow_eq (K i) L (s i) (t i))
  obtain ⟨q, hq⟩ := (Filter.eventually_all.mpr hExtend).exists
  refine ⟨d * q, inferInstance, fun x ↦ ?_⟩
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ x))
  obtain ⟨z, hz⟩ := hq ⟨i, hi⟩
  let C := (K i).tensorProduct (L.tensorPow (m i * q))
  let e := (K i).tensorProductObjIso (L.tensorPow (m i * q)) ≪≫
    whiskerLeftIso (K i).obj (L.tensorPowObjIso (m i * q))
  have he : C.obj.nonvanishingLocus (e.inv.app ⊤ z) = W i :=
    (nonvanishingLocus_hom_app e.symm _).trans hz
  refine ⟨m i, hm i, C, ?_, e.inv.app ⊤ z, he ▸ hxi, he ▸ hAffine i⟩
  simp [C, L, B, hK, ← pullback_mk, pullback_pow, mul_pow, ← pow_mul,
    Nat.mul_left_comm, Nat.mul_comm]

/-- Twisting a relatively ample class by the pullback of every sufficiently large power
of an ample line bundle on the base gives an ample class. -/
theorem eventually_isAmple_mul_pullback_pow (ha : a.IsRelativelyAmple f)
    {b : LineBundleClass Y} (hb : b.IsAmple) :
    ∀ᶠ n : ℕ in atTop, (a * pullback f b ^ n).IsAmple := by
  obtain ⟨B, rfl⟩ := mk_surjective b
  obtain ⟨q, hq⟩ := ha.exists_isAmple_mul_pullback_pow hb
  have hgen : ∀ᶠ n : ℕ in atTop, (B.tensorPow n).IsGloballyGenerated := by
    filter_upwards [eventually_exists_generatingSections_tensor_tensorPow_of_isAmple
      (𝟙_ Y.Modules) B hb] with n ⟨G, _⟩
    let e : (𝟙_ Y.Modules) ⊗ (B.tensorPow n).obj ≅ (B.tensorPow n).obj := λ_ _
    exact InvertibleSheaf.isGloballyGenerated_iff_nonempty_generatingSections.mpr ⟨G.equivOfIso e⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgen
  refine eventually_atTop.mpr ⟨q + N, fun n hn ↦ ?_⟩
  have h := hq.mul_mk_of_isGloballyGenerated ((hN (n - q) (by omega)).pullback f)
  rwa [← pullback_mk, mk_tensorPow, pullback_pow, mul_assoc, ← pow_add,
    Nat.add_sub_of_le (show q ≤ n by omega)] at h

end TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple

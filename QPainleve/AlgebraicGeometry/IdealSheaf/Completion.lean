/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.AdicCompletion.AlgHom
import TauCeti.RingTheory.AdicCompletion.Noetherian

/-!
# Detection of functions on infinitesimal neighborhoods

A global function on a locally Noetherian scheme is determined by its restrictions to the
thickenings cut out by powers of an ideal whose vanishing locus meets the closure of every point.
For a proper, scheme-theoretically dominant morphism to a Noetherian local spectrum, the completed
base ring injects into the inverse limit of the rings of functions on the infinitesimal fibers.
This part of the degree-zero [theorem on formal functions](https://stacks.math.columbia.edu/tag/02OC)
compares the completed base of an exceptional-curve contraction with the thickened fibers.

The stalk argument uses Krull intersection, as in the
[Stacks Project, Lemma 52.28.2](https://stacks.math.columbia.edu/tag/0EL2).
-/

public section

open CategoryTheory Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

namespace IdealSheafData

/-- Suppose every point specializes to a point of the closed locus of `I`.
A global function that restricts to zero on every positive thickening of this locus is zero. -/
theorem eq_zero_of_forall_subschemeι_appTop_pow_eq_zero
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (hI : ∀ x : X, ∃ y ∈ I.support, x ⤳ y) {s : Γ(X, ⊤)}
    (hs : ∀ n : ℕ, (I ^ (n + 1)).subschemeι.appTop s = 0) : s = 0 := by
  have germ_zero (y : X) (hy : y ∈ I.support) : X.presheaf.Γgerm y s = 0 := by
    have hproper := (I.mem_support_iff_stalkIdeal_ne_top y).mp hy
    rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ hproper, Ideal.mem_iInf]
    intro n
    cases n with
    | zero => simp
    | succ n =>
      have hy' : y ∈ ((I ^ (n + 1)).support : Set X) := by simpa using hy
      obtain ⟨z, rfl⟩ := (I ^ (n + 1)).range_subschemeι.symm ▸ hy'
      let i := (I ^ (n + 1)).subschemeι
      have hker : RingHom.ker (i.stalkMap z).hom = I.stalkIdeal (i z) ^ (n + 1) := by
        rw [Hom.ker_stalkMap_of_isClosedImmersion, ← stalkIdeal_pow]
        exact congrArg (fun J : X.IdealSheafData ↦ J.stalkIdeal (i z))
          (ker_subschemeι (I ^ (n + 1)))
      rw [← hker, RingHom.mem_ker]
      have hz : i z ∈ (⊤ : X.Opens) := TopologicalSpace.Opens.mem_top _
      have hg := i.germ_stalkMap_apply ⊤ z hz s
      have hres : i.app ⊤ s = 0 := hs n
      exact hg.trans (by rw [hres]; exact map_zero _)
  apply TopCat.Presheaf.section_ext X.sheaf ⊤ s 0
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hI x
  -- Transport the vanishing germ from the specialization back to `x`.
  change X.presheaf.germ ⊤ x hx s = X.presheaf.germ ⊤ x hx 0
  rw [← X.presheaf.germ_stalkSpecializes (TopologicalSpace.Opens.mem_top y) hxy,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ← TopCat.Presheaf.Γgerm,
    germ_zero y hy]
  simp

end IdealSheafData

namespace Hom

variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}

local notation "𝔪" => maximalIdeal R
local notation "R̂" => AdicCompletion 𝔪 R

/-- The map from the completed base ring to global functions on the infinitesimal fiber
of order `n + 1`, given by truncation followed by pullback. -/
noncomputable def completionToFiberThickening (f : X ⟶ Spec (.of R)) (n : ℕ) :
    R̂ →+* Γ(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1))))), ⊤) :=
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1))))
  ((Scheme.ΓSpecIso _).inv ≫ (pullback.snd f q).appTop).hom.comp
    (AdicCompletion.evalₐ 𝔪 (n + 1)).toRingHom

/-- The level comparison pulls back the corresponding truncation of the completed element. -/
@[simp]
theorem completionToFiberThickening_apply (f : X ⟶ Spec (.of R)) (n : ℕ) (a : R̂) :
    f.completionToFiberThickening n a =
      (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1)))))).appTop
        ((Scheme.ΓSpecIso _).inv (AdicCompletion.evalₐ 𝔪 (n + 1) a)) :=
  (rfl)

/-- For an element of the base ring, completion followed by restriction to an
infinitesimal fiber is ordinary pullback from the base to that fiber. -/
theorem completionToFiberThickening_algebraMap (f : X ⟶ Spec (.of R)) (n : ℕ) (r : R) :
    f.completionToFiberThickening n (algebraMap R R̂ r) =
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1)))))).appTop
        (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) := by
  let Q := CommRingCat.of (R ⧸ 𝔪 ^ (n + 1))
  let qr : CommRingCat.of R ⟶ Q := CommRingCat.ofHom (Ideal.Quotient.mk _)
  let q := Spec.map qr
  have h : (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ (pullback.fst f q).appTop =
      qr ≫ (Scheme.ΓSpecIso Q).inv ≫ (pullback.snd f q).appTop := by
    rw [← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc]
  rw [completionToFiberThickening_apply, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
  exact (ConcreteCategory.congr_hom h r).symm

private theorem pullback_appTop_pow_subschemeι_eq_zero [IsNoetherianRing R]
    (f : X ⟶ Spec (.of R)) (n : ℕ) (d : R̂)
    (ha : f.completionToFiberThickening n d = 0) :
    let j := Spec.map (CommRingCat.ofHom (algebraMap R R̂))
    let g := pullback.snd f j
    let I := (IdealSheafData.ofIdealTop
      ((maximalIdeal R̂).map (Scheme.ΓSpecIso (.of R̂)).inv.hom)).comap g
    (I ^ (n + 1)).subschemeι.appTop (g.appTop ((Scheme.ΓSpecIso (.of R̂)).inv d)) = 0 := by
  intro j g I
  let s := g.appTop ((Scheme.ΓSpecIso (.of R̂)).inv d)
  let e := Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ 𝔪 (n + 1)).toRingHom)
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1))))
  have he : e ≫ j = q := by
    rw [← Spec.map_comp]
    congr 1
  have hclosed : IsClosedImmersion e :=
    IsClosedImmersion.spec_of_surjective _ (AdicCompletion.surjective_evalₐ _ _)
  let i := pullback.fst g e
  have hEval : RingHom.ker (AdicCompletion.evalₐ 𝔪 (n + 1)).toRingHom =
      (𝔪 ^ (n + 1)).map (algebraMap R R̂) :=
    AdicCompletion.ker_evalₐ_eq_map_pow (Ideal.fg_of_isNoetherianRing 𝔪) (n + 1)
  have hi : i.ker = I ^ (n + 1) := by
    rw [IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.Hom.ker_Spec_map,
      CommRingCat.hom_ofHom, hEval, Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map,
      Ideal.map_pow, IdealSheafData.ofIdealTop_pow, IdealSheafData.comap_pow]
  let t : pullback g e ⟶ pullback f q :=
    pullback.lift (i ≫ pullback.fst f j) (pullback.snd g e) (calc
      (i ≫ pullback.fst f j) ≫ f = (i ≫ g) ≫ j := by
        simp only [g, Category.assoc, pullback.condition]
      _ = pullback.snd g e ≫ q := by rw [pullback.condition, Category.assoc, he])
  have ht : i ≫ g = t ≫ pullback.snd f q ≫ e := by
    rw [← Category.assoc, pullback.lift_snd, pullback.condition]
  have hΓ : (Scheme.ΓSpecIso (.of R̂)).inv ≫ g.appTop ≫ i.appTop =
      CommRingCat.ofHom (AdicCompletion.evalₐ 𝔪 (n + 1)).toRingHom ≫
        (Scheme.ΓSpecIso _).inv ≫ (pullback.snd f q).appTop ≫ t.appTop := by
    rw [← Scheme.Hom.comp_appTop, ht]
    simp only [Scheme.Hom.comp_appTop, Category.assoc, e]
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  have hz : i.appTop s = 0 := calc
    i.appTop s = t.appTop (f.completionToFiberThickening n d) := by
      have heq := congrArg (fun h : CommRingCat.of R̂ ⟶ Γ(pullback g e, ⊤) ↦ h.hom d) hΓ
      simpa only [s, q, completionToFiberThickening, CommRingCat.hom_comp,
        RingHom.comp_apply, CommRingCat.hom_ofHom] using heq
    _ = 0 := by simp [ha]
  rw [← IsClosedImmersion.lift_fac i (I ^ (n + 1)).subschemeι (by simp [hi]),
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hz, map_zero]

private theorem injective_completionToFiberThickening [IsNoetherianRing R]
    (f : X ⟶ Spec (.of R)) [IsProper f] [IsSchemeTheoreticallyDominant f] :
    Function.Injective fun a : R̂ ↦ fun n ↦ f.completionToFiberThickening n a := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap R R̂))
  let g := pullback.snd f j
  let Y := pullback f j
  have hflat : (algebraMap R R̂).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Flat j := Flat.SpecMap_iff.mpr hflat
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let I := (IdealSheafData.ofIdealTop
    ((maximalIdeal R̂).map (Scheme.ΓSpecIso (.of R̂)).inv.hom)).comap g
  have hI (x : Y) : ∃ y ∈ I.support, x ⤳ y := by
    obtain ⟨y, hxy, hy⟩ := g.isClosedMap.specializingMap (specializes_closedPoint (g x))
    refine ⟨y, ?_, hxy⟩
    rw [IdealSheafData.support_comap, ← SetLike.mem_coe, TopologicalSpace.Closeds.coe_preimage,
      Set.mem_preimage, hy, IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus,
      ← Ideal.coe_comap, Ideal.comap_map_of_bijective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R̂)).inv)]
    exact (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl
  refine (injective_iff_map_eq_zero (RingHom.pi f.completionToFiberThickening)).mpr ?_
  intro d hd
  let s := g.appTop ((Scheme.ΓSpecIso (.of R̂)).inv d)
  suffices s = 0 from
    map_eq_zero_iff (Scheme.ΓSpecIso (.of R̂)).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R̂)).inv).1 |>.mp
        ((map_eq_zero_iff g.appTop.hom (g.app_injective ⊤)).mp this)
  apply I.eq_zero_of_forall_subschemeι_appTop_pow_eq_zero hI
  exact fun n ↦ f.pullback_appTop_pow_subschemeι_eq_zero n d (congrFun hd n)

/-- The closed-fiber thickening of order `n + 1` maps to the thickening of order `n + 2`. -/
noncomputable def fiberThickeningι (f : X ⟶ Spec (.of R)) (n : ℕ) :
    pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 2))))) :=
  pullback.map _ _ _ _ (𝟙 X)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right
      (I := 𝔪) (Nat.le_succ (n + 1)))))) (𝟙 _) (by simp) (by
    rw [Category.comp_id, ← Spec.map_comp]
    congr 1)

/-- The inclusion of infinitesimal fibers commutes with the projection to the source scheme. -/
@[reassoc (attr := simp)]
theorem fiberThickeningι_fst (f : X ⟶ Spec (.of R)) (n : ℕ) :
    f.fiberThickeningι n ≫
      pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 2))))) =
    pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1))))) := by
  simp [fiberThickeningι]

/-- On the base schemes the inclusion of infinitesimal fibers lies over the quotient map. -/
@[reassoc (attr := simp)]
theorem fiberThickeningι_snd (f : X ⟶ Spec (.of R)) (n : ℕ) :
    f.fiberThickeningι n ≫
      pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 2))))) =
    pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1))))) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right
        (I := 𝔪) (Nat.le_succ (n + 1))))) :=
  pullback.lift_snd ..

/-- The inverse system of rings of global functions on the infinitesimal fibers, starting
at the closed fiber. -/
noncomputable abbrev fiberThickeningSections (f : X ⟶ Spec (.of R)) : ℕᵒᵖ ⥤ CommRingCat.{u} :=
  Functor.ofOpSequence (X := fun n ↦
    Γ(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1))))), ⊤))
      (fun n ↦ (fiberThickeningι f n).appTop)

/-- Restriction from one infinitesimal fiber to the preceding fiber commutes with
pullback from the completed base. -/
theorem completionToFiberThickening_naturality (f : X ⟶ Spec (.of R)) (n : ℕ) :
    CommRingCat.ofHom (f.completionToFiberThickening (n + 1)) ≫
        (fiberThickeningι f n).appTop =
      CommRingCat.ofHom (f.completionToFiberThickening n) := by
  let q (k : ℕ) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (k + 1))))
  let r := CommRingCat.ofHom
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := 𝔪) (Nat.le_succ (n + 1))))
  have hp : f.fiberThickeningι n ≫ pullback.snd f (q (n + 1)) =
      pullback.snd f (q n) ≫ Spec.map r :=
    f.fiberThickeningι_snd n
  have hr : CommRingCat.ofHom (AdicCompletion.evalₐ 𝔪 (n + 2)).toRingHom ≫ r =
      CommRingCat.ofHom (AdicCompletion.evalₐ 𝔪 (n + 1)).toRingHom := by
    ext x
    exact AdicCompletion.factor_evalₐ (Nat.le_succ (n + 1)) x
  -- Use the quotient transition before pulling back from the base.
  have hleft : CommRingCat.ofHom (f.completionToFiberThickening (n + 1)) ≫
      (fiberThickeningι f n).appTop =
      CommRingCat.ofHom (AdicCompletion.evalₐ 𝔪 (n + 2)).toRingHom ≫
        (Scheme.ΓSpecIso _).inv ≫ (pullback.snd f (q (n + 1))).appTop ≫
          (fiberThickeningι f n).appTop := by rfl
  rw [hleft, ← Scheme.Hom.comp_appTop, hp]
  simp only [Scheme.Hom.comp_appTop]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc, ← Category.assoc, hr]
  rfl

/-- The canonical map from the completed base ring to the inverse limit of the rings of
global functions on the infinitesimal fibers. -/
noncomputable def completionToFiberThickeningLimit (f : X ⟶ Spec (.of R)) :
    CommRingCat.of R̂ ⟶ limit f.fiberThickeningSections :=
  limit.lift _ {
    pt := CommRingCat.of R̂
    π := NatTrans.ofOpSequence
      (fun n ↦ CommRingCat.ofHom (f.completionToFiberThickening n)) (fun n ↦ by
        -- The source is the constant diagram on the completed base ring.
        change (𝟙 (CommRingCat.of R̂)) ≫ _ = _
        rw [Category.id_comp]
        have hm : f.fiberThickeningSections.map (homOfLE (Nat.le_succ n)).op =
            (f.fiberThickeningι n).appTop :=
          Functor.ofOpSequence_map_homOfLE_succ
            (X := fun k ↦ f.fiberThickeningSections.obj (op k))
            (fun k ↦ (f.fiberThickeningι k).appTop) n
        exact ((congrArg
          (fun k ↦ CommRingCat.ofHom (f.completionToFiberThickening (n + 1)) ≫ k) hm).trans
            (f.completionToFiberThickening_naturality n)).symm) }

/-- The limit comparison at level `n` is pullback along the fiber projection, applied to the
`(n + 1)`st truncation of the completed element. -/
@[reassoc (attr := simp)]
theorem completionToFiberThickeningLimit_π (f : X ⟶ Spec (.of R)) (n : ℕ) :
    f.completionToFiberThickeningLimit ≫ limit.π f.fiberThickeningSections (op n) =
      CommRingCat.ofHom (f.completionToFiberThickening n) :=
  limit.lift_π _ _

/-- The comparison from the completed local base ring to the limit of the infinitesimal fiber
functions is injective for a proper, scheme-theoretically dominant morphism. -/
theorem injective_completionToFiberThickeningLimit [IsNoetherianRing R]
    (f : X ⟶ Spec (.of R)) [IsProper f] [IsSchemeTheoreticallyDominant f] :
    Function.Injective f.completionToFiberThickeningLimit := by
  intro a b h
  apply f.injective_completionToFiberThickening
  funext n
  have ha := ConcreteCategory.congr_hom (f.completionToFiberThickeningLimit_π n) a
  have hb := ConcreteCategory.congr_hom (f.completionToFiberThickeningLimit_π n) b
  exact ha.symm.trans ((congrArg (limit.π f.fiberThickeningSections (op n)) h).trans hb)

end Hom

end AlgebraicGeometry.Scheme

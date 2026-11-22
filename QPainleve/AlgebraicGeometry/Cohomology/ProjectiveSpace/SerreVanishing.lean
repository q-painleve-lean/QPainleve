/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Instances
public import TauCeti.AlgebraicGeometry.Modules.FiniteType
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Finite
import TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
import TauCeti.AlgebraicGeometry.Cohomology.PushforwardAcyclic.Affine
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.GlobalGeneration
import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula

/-!
# Serre vanishing for projective twists

On projective space over a Noetherian ring, sufficiently positive twists of a coherent sheaf
have vanishing cohomology in every positive degree, with one bound for all degrees. The proof
uses descending induction via the kernel of a surjection from a finite sum of twists, following
the Stacks Project, Lemma 30.14.1 (tag 01YS). The surjection is provided by Tau Ceti's
`Proj.eventually_exists_epi_free_tensor_twistingSheaf`, and the vanishing for twists of the
structure sheaf by `Module.Basis.subsingleton_cohomology_twistingSheaf_of_neg_card_lt`.

The projection formula and the affine direct image comparison transfer vanishing along a finite
morphism to projective space, including a closed immersion. If a positive power of a line bundle
is the pullback of `𝒪(1)`, applying this comparison in each residue class of the exponent
gives vanishing for all sufficiently high powers of the line bundle. This follows the reduction
in the Stacks Project, Lemma 30.16.1 (tag 0B5T).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry.Scheme.Modules Filter TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme.Modules
open TauCeti.SymmetricAlgebra

universe u

namespace Module.Basis

variable {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

local notation "𝒜" => homogeneousSubmodule R M
local notation "P" => Proj 𝒜
local notation "𝒪(" m ")" => Proj.twistingSheaf 𝒜 m

private theorem subsingleton_cohomology_twist_free_tensor_twistingSheaf
    {κ : Type*} [Fintype κ] (b : Basis κ R M)
    (I : Type u) [Finite I] (p m : ℤ) (hm : -(Fintype.card κ : ℤ) < m + p)
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Cohomology (𝒪(m) ⊗ ((SheafOfModules.free I : (P).Modules) ⊗ 𝒪(p))) q) := by
  let G : (P).Modules := SheafOfModules.free I
  let U := 𝟙_ (P).Modules
  let L := 𝒪(m + p)
  let x : κ → SymmetricAlgebra R M := SymmetricAlgebra.ι R M ∘ b
  have hx (i : κ) : x i ∈ 𝒜 1 := ι_mem_homogeneousSubmodule R M (b i)
  have hcover : ⨆ i, Proj.basicOpen 𝒜 (x i) = ⊤ := iSup_basicOpen_ι_eq_top R M b b.span_eq
  have : HasFiniteBiproducts (P).Modules := Abelian.hasFiniteBiproducts
  let e : (𝒪(m) ⊗ G) ⊗ 𝒪(p) ≅ ⨁ fun _ : I ↦ L :=
    (tensorLeft (𝒪(m)) ⋙ tensorRight (𝒪(p))).mapIso
      (TauCeti.SheafOfModules.biproductIsoFree (R := (P).sheaf) I).symm ≪≫
    (tensorLeft (𝒪(m)) ⋙ tensorRight (𝒪(p))).mapBiproduct (fun _ : I ↦ U) ≪≫
    biproduct.mapIso (fun _ : I ↦
      whiskerRightIso (ρ_ (𝒪(m))) (𝒪(p)) ≪≫ Proj.twistingSheaf.tensorObjIso x hx hcover m p)
  let H := cohomologyFunctor P q
  have : Subsingleton (Cohomology L q) := b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt
    hm hq
  let eH := H.mapIso ((α_ (𝒪(m)) G (𝒪(p))).symm ≪≫ e)
  let := Fintype.ofFinite I
  have hL : Subsingleton (Cohomology (⨁ fun _ : I ↦ L) q) :=
    (cohomologyBiproductLinearEquiv R (fun _ : I ↦ L) q).toEquiv.subsingleton_congr.mpr
      inferInstance
  exact eH.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr hL

/-- **Serre vanishing on projective space.** Over a Noetherian ring, a sufficiently positive twist
of a quasi-coherent sheaf of finite type has zero cohomology in all positive degrees. -/
public theorem eventually_subsingleton_cohomology_twistingSheaf [IsNoetherianRing R]
    {κ : Type*} [Finite κ] (b : Basis κ R M)
    (F : (P).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∀ᶠ m : ℤ in atTop, ∀ q : ℕ, 0 < q → Subsingleton (Cohomology (𝒪(m) ⊗ F) q) := by
  let := Fintype.ofFinite κ
  let x : κ → SymmetricAlgebra R M := SymmetricAlgebra.ι R M ∘ b
  have hx (i : κ) : x i ∈ 𝒜 1 := ι_mem_homogeneousSubmodule R M (b i)
  have hcover : ⨆ i, Proj.basicOpen 𝒜 (x i) = ⊤ := iSup_basicOpen_ι_eq_top R M b b.span_eq
  have : Module.Finite R M := Module.Finite.of_basis b
  cases isEmpty_or_nonempty κ with
  | inl h =>
    have : IsEmpty P := ⟨fun y ↦ by
      obtain ⟨j, _⟩ := Opens.mem_iSup.mp (hcover.symm ▸ Opens.mem_top y)
      exact isEmptyElim j⟩
    exact Eventually.of_forall fun m q hq ↦ by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
      infer_instance
  | inr h =>
    have hcard : 0 < Fintype.card κ := Fintype.card_pos
    revert F
    refine Nat.decreasingInduction'
      (motive := fun j ↦ ∀ (F : (P).Modules) [F.IsQuasicoherent] [F.IsFiniteType],
        ∀ᶠ m : ℤ in atTop, ∀ q : ℕ, j < q → Subsingleton (Cohomology (𝒪(m) ⊗ F) q))
      (n := Fintype.card κ - 1) ?_ (Nat.zero_le _) ?_
    · intro j _ _ ih F _ _
      obtain ⟨p, I, _, π, _⟩ :=
        (Proj.eventually_exists_epi_free_tensor_twistingSheaf x hx hcover F).exists
      let S := ShortComplex.kernelSequence π
      have hS : S.ShortExact := TauCeti.kernelSequence_shortExact π
      let G : (P).Modules := SheafOfModules.free I
      let L := 𝒪(-(p : ℤ))
      have : G.IsFinitePresentation := TauCeti.SheafOfModules.isFinitePresentation_free I
      have : L.IsFinitePresentation := isFinitePresentation_of_isInvertible L
      have : (G ⊗ L).IsQuasicoherent := isQuasicoherent_tensorObj P G L
      have : (G ⊗ L).IsFiniteType := isFiniteType_tensorObj G L
      let K : (P).Modules := kernel π
      have : K.IsFinitePresentation := isFinitePresentation_kernel π
      have hKqc : K.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation K
      have hKft : K.IsFiniteType := isFiniteType_of_isFinitePresentation K
      filter_upwards [@ih K hKqc hKft, eventually_ge_atTop (p : ℤ)] with m hK hm q hq
      have htwist := shortExact_map_tensorLeft (𝒪(m)) hS
      exact subsingleton_cohomology_X₃ htwist q (q + 1) rfl
        (b.subsingleton_cohomology_twist_free_tensor_twistingSheaf I _ m (by omega) q (by omega))
        (hK (q + 1) (by omega))
    · intro F _ _
      exact Eventually.of_forall fun m q hq ↦
        b.subsingleton_cohomology_proj_of_card_le (𝒪(m) ⊗ F) q (by omega)

end Module.Basis

namespace AlgebraicGeometry.Scheme.Hom

/-- **Serre vanishing for the pullback of a projective twist.** If `i : X ⟶ ℙ(M)` is finite
and the coefficient ring is Noetherian, tensoring a quasi-coherent sheaf of finite type on `X`
with the pullback of `𝒪(m)` kills all its positive-degree cohomology for sufficiently large `m`. -/
public theorem eventually_subsingleton_cohomology_pullback_twistingSheaf
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
    {X : Scheme.{u}} (i : X ⟶ Proj (homogeneousSubmodule R M)) [IsFinite i]
    {κ : Type*} [Finite κ] (b : Module.Basis κ R M)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∀ᶠ m : ℤ in atTop, ∀ q : ℕ, 0 < q →
      Subsingleton (Cohomology
        ((Scheme.Modules.pullback i).obj (Proj.twistingSheaf (homogeneousSubmodule R M) m) ⊗ F)
        q) := by
  let Y := Proj (homogeneousSubmodule R M)
  have : Module.Finite R M := Module.Finite.of_basis b
  filter_upwards [b.eventually_subsingleton_cohomology_twistingSheaf ((pushforward i).obj F)]
    with m h q hq
  let L : TauCeti.AlgebraicGeometry.InvertibleSheaf Y := ⟨Proj.twistingSheaf _ m, inferInstance⟩
  let E := (TauCeti.AlgebraicGeometry.InvertibleSheaf.toFiniteLocallyFree Y).obj L
  let e' := (TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pushforwardTensorLeftIso i E).app F
  let e := e' ≪≫ (pushforward i).mapIso
    (whiskerRightIso (eqToIso
      (TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pullback_obj_obj i E)) F)
  let H := cohomologyFunctor Y q
  let eH := H.mapIso e ≪≫ i.cohomologyPushforwardIsoOfIsAffineHom _ q
  exact eH.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp (h q hq)

open TauCeti.AlgebraicGeometry

/-- A line bundle with a positive tensor power pulled back from `𝒪(1)` along a finite morphism
to projective space over a Noetherian ring satisfies Serre vanishing. The bound applies to all
sufficiently high powers of the line bundle and is uniform over positive cohomology degrees. -/
public theorem eventually_subsingleton_cohomology_tensorPow_of_finite_to_proj
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
    {X : Scheme.{u}} (i : X ⟶ Proj (homogeneousSubmodule R M)) [IsFinite i]
    {κ : Type*} [Finite κ] (b : Module.Basis κ R M)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (L : InvertibleSheaf X) {d : ℕ} (hd : 0 < d)
    (hL : Nonempty ((L.tensorPow d).obj ≅
      (Scheme.Modules.pullback i).obj (Proj.twistingSheaf (homogeneousSubmodule R M) 1))) :
    ∀ᶠ m : ℕ in atTop, ∀ q : ℕ, 0 < q → Subsingleton (Cohomology (F ⊗ (L.tensorPow m).obj) q) := by
  let T (m : ℤ) : InvertibleSheaf (Proj (homogeneousSubmodule R M)) :=
    ⟨Proj.twistingSheaf _ m, inferInstance⟩
  let K (m : ℤ) := (InvertibleSheaf.pullback i).obj (T m)
  have hL' : Nonempty ((K 1).obj ≅ (L.tensorPow d).obj) :=
    hL.map fun e ↦ eqToIso (InvertibleSheaf.pullback_obj_obj i (T 1)) ≪≫ e.symm
  have hClass : LineBundleClass.mk (K 1) = LineBundleClass.mk L ^ d := by
    simpa only [LineBundleClass.mk_tensorPow] using (LineBundleClass.mk_eq_mk_iff.mpr hL')
  -- Apply vanishing to one coefficient sheaf for each exponent residue class.
  refine Eventually.atTop_of_arithmetic hd.ne' fun r _ ↦ ?_
  let Lr := L.tensorPow r
  filter_upwards [(i.eventually_subsingleton_cohomology_pullback_twistingSheaf b
    (Lr.obj ⊗ F)).natCast_atTop] with m hm q hq
  have hTm : LineBundleClass.mk (T m) = LineBundleClass.mk (T 1) ^ m := by
    rw [← zpow_natCast]
    exact Proj.lineBundleClass_twistingSheaf_eq_zpow (SymmetricAlgebra.ι R M)
      (ι_mem_homogeneousSubmodule R M) (iSup_basicOpen_ι_eq_top R M id (by simp)) m
  have hKm : LineBundleClass.mk (K m) = LineBundleClass.mk L ^ (d * m) := by
    simp only [K, ← LineBundleClass.pullback_mk, hTm, LineBundleClass.pullback_pow]
    rw [LineBundleClass.pullback_mk, hClass, ← pow_mul]
  have hprod : LineBundleClass.mk ((K m).tensorProduct Lr) =
      LineBundleClass.mk (L.tensorPow (d * m + r)) := by
    simp only [LineBundleClass.mk_tensorProduct, hKm, Lr, LineBundleClass.mk_tensorPow, pow_add]
  obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.mp hprod
  let eF : (K m).obj ⊗ (Lr.obj ⊗ F) ≅ F ⊗ (L.tensorPow (d * m + r)).obj :=
    (α_ (K m).obj Lr.obj F).symm ≪≫
      whiskerRightIso (((K m).tensorProductObjIso Lr).symm ≪≫ e) F ≪≫
      (β_ _ _)
  exact ((cohomologyFunctor X q).mapIso eF).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp
    (hm q hq)

end AlgebraicGeometry.Scheme.Hom

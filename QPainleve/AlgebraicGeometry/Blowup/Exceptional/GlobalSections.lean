/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Restriction
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import Mathlib.AlgebraicGeometry.Noetherian
import QPainleve.AlgebraicGeometry.Blowup.PointCohomology
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Modules.Pushforward
import TauCeti.AlgebraicGeometry.Cohomology.AffinePushforward
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic
import TauCeti.AlgebraicGeometry.IdealSheaf.TensorSequence

/-!
# Global sections of nonnegative exceptional twists

Adding a positive multiple of the exceptional divisor to a pulled-back line bundle
preserves its direct image and hence its global sections. In each step the quotient is
a negative twist on the exceptional projective line. Its sections vanish and its
support maps to the center, so its direct image is zero.

The proof uses the comparison with a twist over the residue field and Tau Ceti's
tensor Cartier sequence.
-/

public section

open CategoryTheory Limits MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} (p : X)

local notation "Iₚ" => Scheme.Hom.ker (Scheme.fromSpecResidueField X p)
local notation "Y" => blowup Iₚ
local notation "π" => blowupToBase Iₚ
local notation "E" => comap Iₚ π
local notation "ι" => subschemeι E
local notation "𝒥" =>
  IsEffectiveCartier.toInvertibleSheaf (isEffectiveCartier_comap_blowupToBase Iₚ)
local notation:max "twist[" a ", " m "]" =>
  (LineBundleClass.pullback π a * (LineBundleClass.mk 𝒥) ^ (-m : ℤ))

/-- The restriction quotient of a positive exceptional twist has zero direct image along
the point blowup. -/
theorem isZero_pushforward_pointBlowup_exceptional_quotient
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (a : LineBundleClass X) (m : ℤ) (hm : 0 < m) (M : InvertibleSheaf Y)
    (hM : LineBundleClass.mk M = twist[a, m]) :
    IsZero ((pushforward π).obj (M.obj ⊗ (E).pushforwardSubscheme)) := by
  let κ : Type u := X.residueField p
  obtain ⟨e, he, htwist⟩ := exists_iso_projectiveLine_residueField_exceptional_twist
    p hp hdim
  obtain ⟨t⟩ := htwist a m M hM
  let X₀ := projectiveLine κ
  let : (E).subscheme.Over (Spec (.of κ)) := ⟨e.inv ≫ X₀ ↘ Spec (.of κ)⟩
  let : e.hom.IsOver (Spec (.of κ)) := ⟨by
    -- Unfold the structure morphism of the exceptional subscheme chosen just above.
    change e.hom ≫ e.inv ≫ (X₀ ↘ Spec (.of κ)) = _
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]⟩
  let N := (Scheme.Modules.pullback ι).obj M.obj
  let qIso : M.obj ⊗ (E).pushforwardSubscheme ≅ (pushforward ι).obj N := by
    simpa only [N, FiniteLocallyFreeSheaf.pullback_obj_obj, ObjectProperty.ιOfLE_obj_obj] using
      (E).tensorPushforwardSubschemeIso ((InvertibleSheaf.toFiniteLocallyFree Y).obj M)
  let c := ((e.hom.cohomologyPullbackBaseLinearEquivOfIsIso κ N 0).symm.trans
    (cohomologyBaseLinearEquivOfIso κ ((Scheme.Modules.pullbackComp e.hom ι).app M.obj) 0)).trans
      (cohomologyBaseLinearEquivOfIso κ t 0)
  have := TauCeti.SymmetricAlgebra.subsingleton_cohomology_zero_twistingSheaf_of_neg
    (R := κ) (neg_lt_zero.mpr hm) (Pi.basisFun κ (Fin 2))
  let : Subsingleton (Cohomology N 0) := c.injective.subsingleton
  let : Subsingleton Γ(N, ⊤) := (cohomologyZeroEquiv _).surjective.subsingleton
  have hfac : ι ≫ π = (e.inv ≫ (X₀ ↘ Spec (.of κ))) ≫ X.fromSpecResidueField p := by
    simpa only [← Category.assoc, e.inv_hom_id, Category.id_comp] using
      congrArg (e.inv ≫ ·) he.w
  have hι (y : (E).subscheme) : (ι ≫ π) y = p := by
    rw [hfac, Scheme.Hom.comp_apply]
    exact X.fromSpecResidueField_apply p _
  exact ((ι ≫ π).isZero_pushforward_of_constant N p hι).of_iso
    ((pushforward π).mapIso qIso ≪≫ (pushforwardComp ι π).app N)

/-- The direct image of the first arrow in the Cartier sequence of a positive exceptional
twist is an isomorphism. The arrow is induced by the inclusion of the exceptional ideal. -/
theorem isIso_pushforward_map_tensor_exceptional_ideal
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (a : LineBundleClass X) (m : ℤ) (hm : 0 < m) (M : InvertibleSheaf Y)
    (hM : LineBundleClass.mk M = twist[a, m]) :
    IsIso ((pushforward π).map (M.obj ◁ (E).sheafι)) := by
  let S := (ShortComplex.mk _ _ (E).sheafι_toPushforwardSubscheme).map (tensorLeft M.obj)
  have hS : S.ShortExact := (E).shortExact_tensor_toPushforwardSubscheme M.obj
  let P := pushforward π
  have hzero : IsZero (P.obj S.X₃) :=
    isZero_pushforward_pointBlowup_exceptional_quotient p hp hdim a m hm M hM
  let c := KernelFork.ofι (P.map S.f) (by rw [← P.map_comp, S.zero, P.map_zero])
  have hc : IsLimit c := KernelFork.mapIsLimit _ hS.fIsKernel P
  exact KernelFork.IsLimit.isIso_ι c hc (hzero.eq_of_tgt _ _)

/-- Direct image along a point blowup recovers the original line bundle from any
representative of its pullback twisted by a nonnegative multiple of the exceptional divisor.
The successive comparisons use the maps induced by the exceptional ideal inclusion. -/
noncomputable def pointBlowupPushforwardExceptionalTwistIso
    [IsLocallyNoetherian X] (hp : IsClosed ({p} : Set X))
    [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (L : InvertibleSheaf X) (n : ℕ) (M : InvertibleSheaf Y)
    (hM : LineBundleClass.mk M = twist[LineBundleClass.mk L, (n : ℤ)]) :
    L.obj ≅ (pushforward π).obj M.obj := by
  induction n generalizing M with
  | zero =>
    let N := (InvertibleSheaf.pullback π).obj L
    have hN : LineBundleClass.mk N = LineBundleClass.mk M := by
      simpa only [Nat.cast_zero, neg_zero, zpow_zero, mul_one, N, LineBundleClass.pullback_mk]
        using hM.symm
    let e : N.obj ≅ M.obj := Classical.choice (LineBundleClass.mk_eq_mk_iff.mp hN)
    have hbase : L.obj ≅ (pushforward π).obj N.obj := by
      dsimp only [N]
      rw [ker_fromSpecResidueField_eq_vanishingIdeal p]
      exact pointBlowupPushforwardPullbackIso hp hdim
        ((InvertibleSheaf.toFiniteLocallyFree X).obj L)
    exact hbase ≪≫ (pushforward π).mapIso e
  | succ n ih =>
    let N := M.tensorProduct 𝒥
    have hN : LineBundleClass.mk N = twist[LineBundleClass.mk L, (n : ℤ)] := by
      dsimp only [N]
      rw [LineBundleClass.mk_tensorProduct, hM, mul_assoc, ← zpow_add_one]
      congr 2
      omega
    have hM' : LineBundleClass.mk M = twist[LineBundleClass.mk L, (n + 1 : ℤ)] := by
      simpa only [Nat.cast_succ] using hM
    let e : N.obj ≅ M.obj ⊗ (E).sheaf := Classical.choice
      (exists_iso_tensor_exceptional_ideal_pointBlowup_twist p (LineBundleClass.mk L)
        (n + 1 : ℤ) (by simpa only [add_sub_cancel_right] using hN) hM')
    have := isIso_pushforward_map_tensor_exceptional_ideal
      p hp hdim (LineBundleClass.mk L) (n + 1 : ℤ) (by omega) M hM'
    exact ih N hN ≪≫ (pushforward π).mapIso e ≪≫
      asIso ((pushforward π).map (M.obj ◁ (E).sheafι)) ≪≫
      (pushforward π).mapIso (ρ_ M.obj)

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))]

/-- A nonnegative exceptional twist preserves global sections as a module over
the base ring. -/
noncomputable def cohomologyZeroPointBlowupExceptionalTwistLinearEquiv
    [IsLocallyNoetherian X] (hp : IsClosed ({p} : Set X))
    [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (L : InvertibleSheaf X) (n : ℕ) (M : InvertibleSheaf Y)
    (hM : LineBundleClass.mk M = twist[LineBundleClass.mk L, (n : ℤ)]) :
    let : Scheme.Over Y (Spec (.of R)) := ⟨π ≫ X ↘ Spec (.of R)⟩
    Cohomology L.obj 0 ≃ₗ[R] Cohomology M.obj 0 := by
  let : Scheme.Over Y (Spec (.of R)) := ⟨π ≫ X ↘ Spec (.of R)⟩
  have : (π).IsOver (Spec (.of R)) := ⟨rfl⟩
  exact (cohomologyBaseLinearEquivOfIso R
    (pointBlowupPushforwardExceptionalTwistIso p hp hdim L n M hM) 0).trans
    ((π).cohomologyZeroPushforwardBaseLinearEquiv (R := R) M.obj)

end AlgebraicGeometry.Scheme.IdealSheafData

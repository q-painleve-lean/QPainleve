/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import QPainleve.Geometry.Toric.CharacterTorus.Evaluation
public import TauCeti.CategoryTheory.Monoidal.Grp.Translation
import QPainleve.Geometry.Toric.CharacterTorus.Isomorphism
import QPainleve.Geometry.Toric.CharacterTorus.TranslationKernel
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Isogeny
import TauCeti.Algebra.MonoidAlgebra.FaithfullyFlat
import TauCeti.AlgebraicGeometry.GroupScheme.Rank

/-!
# Evaluation over a fixed center

Evaluation on the charge torus at a center factors through the scheme fiber of
restriction to the charge kernel. Translation by the center identifies this
fiber with the diagonalizable scheme of the charge image. The cover is flat and
surjective, with degree equal to the index when the charge image has finite
index. The rational point count uses the existing translation kernel.

The comparison uses `groupSchemeQuotientIsoKernel` for the identity fiber and
Tau Ceti's `leftTranslation` to transport it to an arbitrary center.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TauCeti DiagonalizableGroup
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace QPainleve.CharacterTorus

universe u

variable {k A N : Type u} [CommRing k] [AddCommGroup A] [AddCommGroup N]
  [IsAddFG A] [IsAddFG N]

local notation "S" => Spec (CommRingCat.of k)
local notation "D(" G ")" => (Grp.X (C := Over S) (groupScheme k (FGCommGrpCat.of G)))
local notation "f[" v "]" => groupSchemeMap k (FGCommGrpCat.ofHom v)
local notation "a[" v "]" => f[AddMonoidHom.toMultiplicative v]
local notation "c[" c "," hc "]" => (Over.homMk (U := 𝟙_ (Over S)) c hc)

private theorem eval_eq_mul (v : A →+ N) :
    (evaluation k v).hom.hom =
      a[AddMonoidHom.inl A N].hom.hom *
        (a[AddMonoidHom.inr A N].hom.hom ≫ a[v].hom.hom) := by
  have h : ((AddMonoidHom.id A).prod v).toMultiplicative =
      (AddMonoidHom.inl A N).toMultiplicative *
        ((AddMonoidHom.inr A N).comp v).toMultiplicative := by
    exact MonoidHom.ext fun a ↦
      Prod.ext (add_zero a.toAdd).symm (zero_add (v a.toAdd)).symm
  rw [evaluation_def, h, groupSchemeMap_mul (k := k)
    (G := FGCommGrpCat.of (Multiplicative A)) (H := FGCommGrpCat.of (Multiplicative (A × N)))
    (AddMonoidHom.inl A N).toMultiplicative
    ((AddMonoidHom.inr A N).comp v).toMultiplicative,
    ← Grp.comp_hom_hom, ← groupSchemeMap_comp]
  rfl

/-- Evaluation at a fixed center is the charge morphism followed by translation
by the center. -/
theorem evaluationAtCenter_eq_leftTranslation (v : A →+ N)
    (c : S ⟶ (D(Multiplicative A)).left) (hc : c ≫ (D(Multiplicative A)).hom = 𝟙 S) :
    evaluationAtCenter k v c hc =
      a[v].hom.hom.left ≫ (leftTranslation c[c,hc]).hom.left := by
  let s : D(Multiplicative N) ⟶ D(Multiplicative (A × N)) :=
    Over.homMk (pullback.lift ((D(Multiplicative N)).hom ≫ c) (𝟙 _) (by simp [hc]) ≫
      (prodIso k A N).hom) (by
        rw [Category.assoc, ← a[AddMonoidHom.inr A N].hom.hom.w,
          prodIso_hom_snd_assoc, pullback.lift_snd_assoc, Category.id_comp])
  have h₁ : s ≫ a[AddMonoidHom.inl A N].hom.hom = toUnit _ ≫ c[c,hc] := by
    ext : 1
    simp [s]
  have h₂ : s ≫ a[AddMonoidHom.inr A N].hom.hom = 𝟙 _ := by
    ext : 1
    simp [s]
  have h := congrArg (fun p ↦ s ≫ p) (eval_eq_mul (k := k) v)
  rw [MonObj.comp_mul, ← Category.assoc, h₁, h₂, Category.id_comp] at h
  rw [← Over.comp_left, comp_leftTranslation_hom]
  exact congrArg Over.Hom.left h

local notation "K[" v "]" => AddSubgroup.toSubgroup (AddMonoidHom.ker v)
local notation "Q[" v "]" => _ ⧸ (MonoidHom.range (Subgroup.subtype K[v]))
local notation "q[" v "]" => QuotientGroup.mk' (MonoidHom.range (Subgroup.subtype K[v]))

local notation "eQ[" v "]" => QuotientGroup.quotientMulEquivOfEq (Subgroup.range_subtype K[v])

omit [IsAddFG A] [IsAddFG N] in
private def quotientCharge (v : A →+ N) : Q[v] →* Multiplicative N :=
  (QuotientGroup.kerLift v.toMultiplicative).comp (eQ[v]).toMonoidHom

omit [IsAddFG A] [IsAddFG N] in
private theorem quotientCharge_comp (v : A →+ N) :
    (quotientCharge v).comp q[v] = v.toMultiplicative := by
  apply MonoidHom.ext
  intro a
  exact (congrArg (QuotientGroup.kerLift v.toMultiplicative)
    (QuotientGroup.quotientMulEquivOfEq_mk (Subgroup.range_subtype K[v]) a)).trans
    (QuotientGroup.kerLift_mk v.toMultiplicative a)

omit [IsAddFG A] [IsAddFG N] in
private theorem quotientCharge_injective (v : A →+ N) :
    Function.Injective (quotientCharge v) :=
  (QuotientGroup.kerLift_injective v.toMultiplicative).comp (eQ[v]).injective

omit [IsAddFG A] [IsAddFG N] in
private theorem quotientCharge_range (v : A →+ N) :
    (quotientCharge v).range = v.toMultiplicative.range := by
  have h := QuotientGroup.mk'_surjective (Subgroup.subtype K[v]).range
  apply SetLike.coe_injective
  rw [MonoidHom.coe_range, MonoidHom.coe_range, ← h.range_comp (quotientCharge v),
    ← MonoidHom.coe_comp, quotientCharge_comp]

omit [IsAddFG N] in
private theorem isPullback_quotientCharge (v : A →+ N) :
    IsPullback f[q[v]].hom.hom.left (D(Q[v])).hom
      f[Subgroup.subtype K[v]].hom.hom.left η[(D(K[v]))].left := by
  let e := (Grp.forget (Over S) ⋙ Over.forget S).mapIso
    (groupSchemeQuotientIsoKernel k (FGCommGrpCat.ofHom (Subgroup.subtype K[v])))
  refine (GroupScheme.isPullback_kernel_left f[Subgroup.subtype K[v]]).of_iso'
    e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · rw [Functor.mapIso_hom, Functor.comp_map, Over.forget_map, Grp.forget_map,
      ← Over.comp_left, ← Grp.comp_hom_hom, groupSchemeQuotientIsoKernel_hom_comp_ι]
    simp only [Iso.refl_hom, Category.comp_id, FGCommGrpCat.hom_hom_ofHom]
  · rw [Iso.refl_hom, Category.comp_id]
    exact (groupSchemeQuotientIsoKernel k
      (FGCommGrpCat.ofHom (Subgroup.subtype K[v]))).hom.hom.hom.w

local notation "ρ[" v "]" =>
  (Mon.Hom.hom (InducedCategory.Hom.hom f[Subgroup.subtype K[v]]))
local notation "cK[" v "," c "]" => (c ≫ Over.Hom.left ρ[v])

omit [IsAddFG N] in
private theorem isPullback_translateQuotient (v : A →+ N)
    (c : S ⟶ (D(Multiplicative A)).left) (hc : c ≫ (D(Multiplicative A)).hom = 𝟙 S) :
    IsPullback (f[q[v]].hom.hom.left ≫ (leftTranslation c[c,hc]).hom.left)
      (D(Q[v])).hom ρ[v].left cK[v,c] := by
  let e := (Over.forget S).mapIso (leftTranslation c[c,hc])
  let eK := (Over.forget S).mapIso (leftTranslation (c[c,hc] ≫ ρ[v]))
  refine (isPullback_quotientCharge (k := k) v).of_iso'
    (Iso.refl _) e.symm (Iso.refl _) eK.symm ?_ (by simp) ?_ ?_
  · rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, Iso.eq_comp_inv]
    rfl
  · have h := leftTranslation_hom_comp (ρ[v]) c[c,hc]
    rw [Iso.symm_hom, e.inv_comp_eq, Iso.symm_hom, ← Category.assoc, eK.eq_comp_inv]
    simpa only [e, eK, Over.comp_left, Functor.mapIso_hom, Over.forget_map] using
      (congrArg Over.Hom.left h).symm
  · rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, eK.eq_comp_inv]
    simpa only [eK, Functor.mapIso_hom, Over.forget_map, Over.comp_left, Over.homMk_left] using
      congrArg Over.Hom.left (by
        rw [comp_leftTranslation_hom, toUnit_unit, Category.id_comp]
        simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using mul_one (c[c,hc] ≫ ρ[v]) :
          η[D(K[v])] ≫ (leftTranslation (c[c,hc] ≫ ρ[v])).hom = c[c,hc] ≫ ρ[v])

variable (k)

omit [IsAddFG N] in
/-- The restriction fiber over a fixed center is a translate of the torus whose
character group is the charge image. -/
def fixedCenterFiberIso (v : A →+ N)
    (c : S ⟶ (D(Multiplicative A)).left) (hc : c ≫ (D(Multiplicative A)).hom = 𝟙 S) :
    (D(Q[v])).left ≅ pullback ρ[v].left cK[v,c] :=
  (isPullback_translateQuotient v c hc).isoPullback

omit [IsAddFG N] in
/-- The first projection of the restriction fiber is the translated quotient inclusion. -/
@[reassoc (attr := simp)]
theorem fixedCenterFiberIso_hom_fst (v : A →+ N)
    (c : S ⟶ (D(Multiplicative A)).left) (hc : c ≫ (D(Multiplicative A)).hom = 𝟙 S) :
    (fixedCenterFiberIso k v c hc).hom ≫ pullback.fst _ _ =
      f[q[v]].hom.hom.left ≫ (leftTranslation c[c,hc]).hom.left :=
  (isPullback_translateQuotient v c hc).isoPullback_hom_fst

omit [IsAddFG N] in
/-- The second projection of the restriction fiber is its structure morphism. -/
@[reassoc (attr := simp)]
theorem fixedCenterFiberIso_hom_snd (v : A →+ N)
    (c : S ⟶ (D(Multiplicative A)).left) (hc : c ≫ (D(Multiplicative A)).hom = 𝟙 S) :
    (fixedCenterFiberIso k v c hc).hom ≫ pullback.snd _ _ = (D(Q[v])).hom :=
  (isPullback_translateQuotient v c hc).isoPullback_hom_snd

/-- Evaluation at the fixed center, with codomain the fiber of restriction to the
charge kernel through that center. -/
def evaluationAtCenterToFiber (v : A →+ N)
    (c : S ⟶ (D(Multiplicative A)).left) (hc : c ≫ (D(Multiplicative A)).hom = 𝟙 S) :
    (D(Multiplicative N)).left ⟶ pullback ρ[v].left cK[v,c] :=
  f[quotientCharge v].hom.hom.left ≫ (fixedCenterFiberIso k v c hc).hom

/-- Forgetting the restriction-fiber condition recovers the fixed-center evaluation. -/
@[reassoc (attr := simp)]
theorem evaluationAtCenterToFiber_fst (v : A →+ N)
    (c : S ⟶ (D(Multiplicative A)).left) (hc : c ≫ (D(Multiplicative A)).hom = 𝟙 S) :
    evaluationAtCenterToFiber k v c hc ≫ pullback.fst _ _ = evaluationAtCenter k v c hc := by
  rw [evaluationAtCenterToFiber, Category.assoc, fixedCenterFiberIso_hom_fst,
    evaluationAtCenter_eq_leftTranslation]
  have h : f[quotientCharge v] ≫ f[q[v]] = a[v] := by
    rw [← groupSchemeMap_comp]
    exact congrArg (groupSchemeMap k) (FGCommGrpCat.hom_ext (quotientCharge_comp v))
  have hh := congrArg (fun z ↦ z.hom.hom.left) h
  simpa only [Grp.comp_hom_hom, Over.comp_left, Category.assoc] using
    congrArg (· ≫ (leftTranslation c[c,hc]).hom.left) hh

/-- Evaluation into the restriction fiber is over the coefficient ring. -/
@[reassoc (attr := simp)]
theorem evaluationAtCenterToFiber_snd (v : A →+ N)
    (c : S ⟶ (D(Multiplicative A)).left) (hc : c ≫ (D(Multiplicative A)).hom = 𝟙 S) :
    evaluationAtCenterToFiber k v c hc ≫ pullback.snd _ _ = (D(Multiplicative N)).hom := by
  rw [evaluationAtCenterToFiber, Category.assoc, fixedCenterFiberIso_hom_snd, Over.w]

/-- Two points have equal lifts into the restriction fiber exactly when their
fixed-center evaluations agree. -/
theorem comp_evaluationAtCenterToFiber_eq_iff (v : A →+ N)
    (c : S ⟶ (D(Multiplicative A)).left) (hc : c ≫ (D(Multiplicative A)).hom = 𝟙 S)
    {X : Scheme.{u}} (p q : X ⟶ (D(Multiplicative N)).left) :
    p ≫ evaluationAtCenterToFiber k v c hc = q ≫ evaluationAtCenterToFiber k v c hc ↔
      p ≫ evaluationAtCenter k v c hc = q ≫ evaluationAtCenter k v c hc := by
  have hw : cK[v,c] ≫ (D(K[v])).hom = 𝟙 S := (c[c,hc] ≫ ρ[v]).w
  have : Mono cK[v,c] := mono_of_mono_fac hw
  have := (IsPullback.of_hasPullback ρ[v].left cK[v,c]).mono_fst_of_mono
  rw [← cancel_mono (pullback.fst ρ[v].left cK[v,c])]
  simp only [Category.assoc, evaluationAtCenterToFiber_fst]

variable (v : A →+ N)

private theorem flat_surjective_quotientCharge :
    Flat f[quotientCharge v].hom.hom.left ∧ Surjective f[quotientCharge v].hom.hom.left := by
  let φ := FGCommGrpCat.ofHom (quotientCharge v)
  let e := eqToIso (groupScheme_X_left k (FGCommGrpCat.of (Multiplicative N)))
  let d := eqToIso (groupScheme_X_left k (FGCommGrpCat.of Q[v]))
  let F := CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom k (quotientCharge v))
  have h : f[quotientCharge v].hom.hom.left ≫ d.hom = e.hom ≫ Spec.map F :=
    groupSchemeMap_comp_toSpec k φ
  have hF := (flat_and_surjective_SpecMap_iff F).mpr
    (MonoidAlgebra.faithfullyFlat_mapDomainRingHom_of_injective k _ (quotientCharge_injective v))
  have := hF.1
  have := hF.2
  have he : f[quotientCharge v].hom.hom.left = e.hom ≫ Spec.map F ≫ d.inv :=
    by simpa only [Category.assoc] using d.eq_comp_inv.mpr h
  rw [he]
  exact ⟨inferInstance, inferInstance⟩

/-- Evaluation onto the restriction fiber is flat and surjective, for any rank of
the charge image. -/
theorem flat_surjective_evaluationAtCenterToFiber
    (c : S ⟶ (D(Multiplicative A)).left) (hc : c ≫ (D(Multiplicative A)).hom = 𝟙 S) :
    Flat (evaluationAtCenterToFiber k v c hc) ∧
      Surjective (evaluationAtCenterToFiber k v c hc) := by
  obtain ⟨_, _⟩ := flat_surjective_quotientCharge k v
  rw [evaluationAtCenterToFiber]
  exact ⟨inferInstance, inferInstance⟩

variable [Finite (Multiplicative N ⧸ v.toMultiplicative.range)]

private theorem finite_quotientCharge :
    Finite ((FGCommGrpCat.of (Multiplicative N)) ⧸
      (FGCommGrpCat.ofHom (quotientCharge v)).hom.hom.range) := by
  simp only [FGCommGrpCat.hom_hom_ofHom, quotientCharge_range]
  exact inferInstanceAs (Finite (Multiplicative N ⧸ v.toMultiplicative.range))

private theorem isCentralIsogeny_quotientCharge :
    GroupScheme.IsCentralIsogeny f[quotientCharge v] := by
  have := finite_quotientCharge v
  exact isCentralIsogeny_groupSchemeMap_of_injective_of_finite_quotient k _
    (quotientCharge_injective v)

/-- At finite charge index the fixed-center evaluation onto its restriction fiber is finite. -/
theorem isFinite_evaluationAtCenterToFiber
    (c : S ⟶ (D(Multiplicative A)).left) (hc : c ≫ (D(Multiplicative A)).hom = 𝟙 S) :
    IsFinite (evaluationAtCenterToFiber k v c hc) := by
  have := (isCentralIsogeny_quotientCharge k v).isFinite
  rw [evaluationAtCenterToFiber]
  infer_instance

/-- The degree at every point of the restriction fiber is the index of the charge image
in the ambient lattice. This holds in every characteristic. -/
theorem finrank_evaluationAtCenterToFiber
    (c : S ⟶ (D(Multiplicative A)).left) (hc : c ≫ (D(Multiplicative A)).hom = 𝟙 S)
    (y : ↥(pullback (C := Scheme) ρ[v].left cK[v,c])) :
    (evaluationAtCenterToFiber k v c hc).finrank y = v.toMultiplicative.range.index := by
  let φ := groupSchemeMap k (FGCommGrpCat.ofHom (quotientCharge v))
  have h := isCentralIsogeny_quotientCharge k v
  have : IsFinite φ.hom.hom.left := h.isFinite
  have : Flat φ.hom.hom.left := h.flat
  have : Surjective φ.hom.hom.left := h.surjective
  let e := fixedCenterFiberIso k v c hc
  obtain ⟨z, rfl⟩ := e.hom.surjective y
  rw [evaluationAtCenterToFiber, Scheme.Hom.finrank_comp_right_of_isIso,
    GroupScheme.finrank_left_eq, ← GroupScheme.finrank_kernel_hom φ]
  have := finite_quotientCharge v
  simpa only [FGCommGrpCat.hom_hom_ofHom, quotientCharge_range] using
    finrank_groupSchemeMap_kernel k (FGCommGrpCat.ofHom (quotientCharge v))
      ((D(Q[v])).hom z)

/-- The rational points over the evaluation of a given charge point are counted
by the charge index when the base has enough roots of unity. -/
theorem natCard_evaluationAtCenterToFiber_fiber
    [HasEnoughRootsOfUnity k (Monoid.exponent (Multiplicative N ⧸ v.toMultiplicative.range))]
    (c : S ⟶ (D(Multiplicative A)).left) (hc : c ≫ (D(Multiplicative A)).hom = 𝟙 S)
    (z₀ : (S).asOver S ⟶ D(Multiplicative N)) :
    Nat.card {z : (S).asOver S ⟶ D(Multiplicative N) //
      z.left ≫ evaluationAtCenterToFiber k v c hc =
        z₀.left ≫ evaluationAtCenterToFiber k v c hc} =
        v.toMultiplicative.range.index := by
  let e := schemePointsMulEquiv (R := k) (A := k) (FGCommGrpCat.of (Multiplicative N))
  let e' := schemePointsMulEquiv (R := k) (A := k) (FGCommGrpCat.of (Multiplicative A))
  have h (z : (S).asOver S ⟶ D(Multiplicative N)) :
      z.left ≫ evaluationAtCenterToFiber k v c hc =
        z₀.left ≫ evaluationAtCenterToFiber k v c hc ↔
        (e z).comp v.toMultiplicative = (e z₀).comp v.toMultiplicative := by
    rw [comp_evaluationAtCenterToFiber_eq_iff, evaluationAtCenter_eq_leftTranslation,
      ← Category.assoc, ← Category.assoc, cancel_mono, ← Over.comp_left, ← Over.comp_left,
      ← Over.OverMorphism.ext_iff]
    simpa only [e, e', schemePointsMulEquiv_groupSchemeMap, FGCommGrpCat.hom_hom_ofHom] using
      (e'.injective.eq_iff (a := z ≫ a[v].hom.hom) (b := z₀ ≫ a[v].hom.hom)).symm
  rw [Nat.card_congr ((e.toEquiv.subtypeEquiv h).trans
    (translationFiberKernelPointsEquiv k v (e z₀)))]
  let φ := FGCommGrpCat.ofHom v.toMultiplicative
  have : Finite (FGCommGrpCat.of (Multiplicative N) ⧸ φ.hom.hom.range) := by
    simpa only [φ, FGCommGrpCat.hom_hom_ofHom] using
      (inferInstance : Finite (Multiplicative N ⧸ v.toMultiplicative.range))
  have : HasEnoughRootsOfUnity k
      (Monoid.exponent (FGCommGrpCat.of (Multiplicative N) ⧸ φ.hom.hom.range)) := by
    simpa only [φ, FGCommGrpCat.hom_hom_ofHom] using
      (inferInstance : HasEnoughRootsOfUnity k
        (Monoid.exponent (Multiplicative N ⧸ v.toMultiplicative.range)))
  exact natCard_kernelSchemePoints k φ

end QPainleve.CharacterTorus

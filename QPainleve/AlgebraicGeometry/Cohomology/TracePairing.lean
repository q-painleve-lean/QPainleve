/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

import Mathlib.AlgebraicGeometry.Artinian
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import QPainleve.AlgebraicGeometry.Modules.InternalHom.Sections
public import TauCeti.AlgebraicGeometry.LineBundle.Dual
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.Cohomology.Support
import TauCeti.AlgebraicGeometry.Cohomology.PushforwardAcyclic.Affine
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.ZeroLocus
import TauCeti.Topology.KrullDimension.Irreducible
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Cokernel
import TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic

/-!
# Cohomology pairings defined by a trace

A global section of the internal Hom from `M` to `N` induces a map on cohomology.
Composing it with a trace on the cohomology of `N` gives a bilinear pairing.
In top degree on an integral projective scheme, a nonzero map between line bundles
induces a surjection because its cokernel is supported on a proper Cartier subscheme.
Consequently a nonzero trace separates global sections of the internal Hom.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonoidalClosed TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))]

/-- Pair a cohomology class with a section by applying its morphism and then the trace. -/
def cohomologyTracePairing (q : ℕ) (tr : Cohomology N q →ₗ[R] R) :
    Cohomology M q →ₗ[R] Γ((ihom M).obj N, ⊤) →ₗ[R] R :=
  LinearMap.flip
    { toFun := fun s ↦ tr.comp (cohomologyMapBaseLinear R X (internalHomSectionsEquiv s) q)
      map_add' := fun s t ↦ by
        simp [cohomologyMapBaseLinear_add, LinearMap.comp_add]
      map_smul' := fun r s ↦ by
        ext x
        simp only [base_smul_globalSections, internalHomSectionsEquiv_smul, LinearMap.comp_apply,
          cohomologyMapBaseLinear_comp, RingHom.id_apply, LinearMap.smul_apply]
        have hs (z : Cohomology N q) :
            cohomologyMapBaseLinear R X (N.globalSectionsSmul (baseRingToGlobalSections R X r))
              q z = r • z :=
          (cohomologyMapBaseLinear_apply _ _ _ _ _).trans
            ((cohomology_smul _ _ _ _).symm.trans (base_smul_cohomology _ _ _ _ _ _).symm)
        rw [hs]
        exact tr.map_smul _ _ }

/-- Evaluation of the trace pairing on a class and a global section. -/
@[simp]
theorem cohomologyTracePairing_apply (q : ℕ) (tr : Cohomology N q →ₗ[R] R)
    (x : Cohomology M q) (s : Γ((ihom M).obj N, ⊤)) :
    cohomologyTracePairing R q tr x s =
      tr (cohomologyMapBaseLinear R X (internalHomSectionsEquiv s) q x) :=
  (rfl)

/-- A nonzero trace separates sections whose corresponding nonzero morphisms
surject on cohomology. -/
theorem cohomologyTracePairing_injective_flip_of_surjective {q : ℕ}
    (tr : Cohomology N q →ₗ[R] R) (htr : tr ≠ 0)
    (hsurj : ∀ f : M ⟶ N, f ≠ 0 → Function.Surjective (cohomologyMapBaseLinear R X f q)) :
    Function.Injective (cohomologyTracePairing (M := M) R q tr).flip := by
  apply (injective_iff_map_eq_zero _).mpr
  intro s hs
  by_contra h
  have hφ : internalHomSectionsEquiv s ≠ 0 := fun hzero ↦
    h (internalHomSectionsEquiv.injective (hzero.trans internalHomSectionsEquiv_zero.symm))
  apply htr
  ext y
  obtain ⟨x, rfl⟩ := hsurj _ hφ y
  simpa only [LinearMap.flip_apply, LinearMap.zero_apply, cohomologyTracePairing_apply]
    using DFunLike.congr_fun hs x

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

open _root_.AlgebraicGeometry.Scheme.Modules

/-- The sections of the internal Hom between line bundles identify with the zeroth
cohomology of the target tensored with the dual of the source. -/
def sectionsInternalHomLinearEquiv {X : Scheme.{u}} (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] (L W : InvertibleSheaf X) :
    Γ((ihom L.obj).obj W.obj, ⊤) ≃ₗ[R] Cohomology (W.tensorProduct L.dual).obj 0 :=
  let e : (ihom L.obj).obj W.obj ≅ (W.tensorProduct L.dual).obj :=
    ((asIso (dualTensorIhom L.obj)).app W.obj).symm ≪≫
      (eqToIso (congrArg (· ⊗ W.obj) (dual_obj L))).symm ≪≫
      (β_ L.dual.obj W.obj) ≪≫ (tensorProductObjIso W L.dual).symm
  (cohomologyZeroBaseLinearEquiv R X _).symm.trans (cohomologyBaseLinearEquivOfIso R e 0)

section BaseRing

variable (R : Type u) [CommRing R] {X : Scheme.{u}}
  [IsIntegral X] [X.Over (Spec (.of R))] {q : ℕ}

private theorem surjective_cohomologyMap_of_cartierVanishing (L K : InvertibleSheaf X)
    (f : L.obj ⟶ K.obj) (hf : f ≠ 0)
    (hvan : ∀ I : X.IdealSheafData, I.IsEffectiveCartier →
      Subsingleton (Cohomology ((Scheme.Modules.pullback I.subschemeι).obj K.obj) q)) :
    Function.Surjective (cohomologyMapBaseLinear R X f q) := by
  let φ := L.twistedToUnit K f
  have hφ : φ ≠ 0 := fun h ↦ hf ((L.twistedToUnit_eq_zero_iff K f).mp h)
  let E : InvertibleSheaf X := L.tensorProduct (dual K)
  have : Mono φ := E.mono_of_ne_zero_to_unit φ hφ
  have : Mono f := (L.mono_twistedToUnit_iff K f).mp inferInstance
  let I := φ.imageIdealSheaf
  have hI : I.IsEffectiveCartier := E.isEffectiveCartier_imageIdealSheaf φ
  let i := I.subschemeι
  let : I.subscheme.Over (Spec (.of R)) := ⟨i ≫ X ↘ Spec (.of R)⟩
  let : i.IsOver (Spec (.of R)) := ⟨rfl⟩
  let EK := (InvertibleSheaf.toFiniteLocallyFree X).obj K
  let V : I.subscheme.Modules := ((FiniteLocallyFreeSheaf.pullback i).obj EK).obj
  have : Subsingleton (Cohomology V q) := by
    simpa only [V, FiniteLocallyFreeSheaf.pullback_obj_obj, EK, ObjectProperty.ιOfLE_obj_obj]
      using hvan I hI
  let eQ := cokernelIsoTensorPushforwardImageIdeal L K f ≪≫ I.tensorPushforwardSubschemeIso EK
  let eH := (cohomologyBaseLinearEquivOfIso R eQ q).trans
    (i.cohomologyPushforwardBaseLinearEquivOfIsAffineHom R V q)
  have : Subsingleton (Cohomology (cokernel f) q) := eH.injective.subsingleton
  rw [coe_cohomologyMapBaseLinear]
  intro y
  have hy : cohomologyMap (cokernel.π f) q y = 0 := Subsingleton.elim _ _
  exact (exact_cohomologyMap_cohomologyMap (TauCeti.cokernelSequence_shortExact f) q y).mp hy

/-- A nonzero morphism between line bundles on a Noetherian integral scheme of
dimension at most one induces a surjection on first cohomology. -/
theorem surjective_cohomologyMap_one_of_ne_zero [IsNoetherian X] (L K : InvertibleSheaf X)
    (f : L.obj ⟶ K.obj) (hf : f ≠ 0) (hdim : topologicalKrullDim X ≤ 1) :
    Function.Surjective (cohomologyMapBaseLinear R X f 1) := by
  refine surjective_cohomologyMap_of_cartierVanishing R L K f hf fun I hI ↦ ?_
  have : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  have : IsLocallyArtinian I.subscheme := .of_topologicalKrullDim_le_zero
    (hI.topologicalKrullDim_subscheme_le (d := 0) (by simpa using hdim))
  have : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
  have : Finite I.subscheme := finite_of_compact_of_discrete
  exact subsingleton_cohomology_succ_of_isAffine _ 0

end BaseRing

variable (k : Type u) [Field k] [Infinite k] {X : Scheme.{u}}
  [IsIntegral X] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] {q : ℕ}

/-- A nonzero morphism of line bundles induces a surjection in degree `q` if the
dimension of the integral projective scheme is at most `q`. -/
theorem surjective_cohomologyMap_of_ne_zero (L K : InvertibleSheaf X)
    (f : L.obj ⟶ K.obj) (hf : f ≠ 0) (hdim : topologicalKrullDim X ≤ q) :
    Function.Surjective (cohomologyMapBaseLinear k X f q) := by
  refine surjective_cohomologyMap_of_cartierVanishing k L K f hf fun I hI ↦ ?_
  let i := I.subschemeι
  let : I.subscheme.Over (Spec (.of k)) := ⟨i ≫ X ↘ Spec (.of k)⟩
  let : i.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : I.subscheme.IsProjectiveOver k := Scheme.IsProjectiveOver.of_isClosedImmersion k i
  have hproper : (I.support : Set X) ≠ Set.univ := by
    intro he
    apply hI.genericPoint_notMem_support
    have hmem : genericPoint X ∈ (I.support : Set X) := by rw [he]; trivial
    exact hmem
  have hs := topologicalKrullDim_subspace_le X (I.support : Set X)
  have hfinite : topologicalKrullDim X < ⊤ :=
    hdim.trans_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top q))
  have hs' := I.support.isClosed.topologicalKrullDim_lt hproper (ne_top_of_lt (hs.trans_lt hfinite))
  let e := i.isClosedEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr I.range_subschemeι)
  have hdim' : topologicalKrullDim I.subscheme < q :=
    e.isHomeomorph.topologicalKrullDim_eq.trans_lt (hs'.trans_le hdim)
  exact subsingleton_cohomology_of_projective_dim_lt (k := k) _ hdim'

/-- A nonzero top-degree trace on a line bundle separates global sections of
the internal Hom from any other line bundle on an integral projective scheme. -/
theorem cohomologyTracePairing_injective_flip (L K : InvertibleSheaf X)
    (hdim : topologicalKrullDim X ≤ q) (tr : Cohomology K.obj q →ₗ[k] k) (htr : tr ≠ 0) :
    Function.Injective (cohomologyTracePairing (M := L.obj) k q tr).flip := by
  exact cohomologyTracePairing_injective_flip_of_surjective k tr htr fun f hf ↦
    surjective_cohomologyMap_of_ne_zero k L K f hf hdim

/-- On a projective integral scheme, a nonzero trace in top degree yields a perfect
pairing exactly when the cohomology and the dual section space have equal dimensions. -/
theorem isPerfPair_cohomologyTracePairing_iff_finrank (L K : InvertibleSheaf X)
    (hdim : topologicalKrullDim X ≤ q) (tr : Cohomology K.obj q →ₗ[k] k) (htr : tr ≠ 0) :
    (cohomologyTracePairing (M := L.obj) k q tr).IsPerfPair ↔
      Module.finrank k (Cohomology L.obj q) = Module.finrank k Γ((ihom L.obj).obj K.obj, ⊤) := by
  have := moduleFinite_cohomology_of_isProjectiveOver k L.obj q
  have := moduleFinite_cohomology_of_isProjectiveOver k (K.tensorProduct L.dual).obj 0
  have := Module.Finite.equiv (L.sectionsInternalHomLinearEquiv k K).symm
  constructor
  · intro h
    exact Module.finrank_of_isPerfPair (cohomologyTracePairing (M := L.obj) k q tr)
  · intro h
    have hi := L.cohomologyTracePairing_injective_flip k K hdim tr htr
    have hd := h.symm.trans (Subspace.dual_finrank_eq (K := k) (V := Cohomology L.obj q)).symm
    have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi
    exact (LinearMap.IsPerfPair.of_bijective _ ⟨hi, hs⟩).flip

end TauCeti.AlgebraicGeometry.InvertibleSheaf

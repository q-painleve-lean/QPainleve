/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange

/-!
# Pullbacks of basis sections

A section giving a basis of a quasicoherent module on an affine open pulls back
to a basis on any affine open in its inverse image.
-/

public section

open CategoryTheory TensorProduct
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (g : Y ⟶ X) {M : X.Modules} [M.IsQuasicoherent]
  {U : X.Opens} {W : Y.Opens}

/-- A basis section on an affine open is still a basis after pullback to a smaller affine open. -/
theorem bijective_smul_pullbackSectionsLE (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (hle : W ≤ g ⁻¹ᵁ U) {s : Γ(M, U)}
    (hs : Function.Bijective (fun a : Γ(X, U) ↦ a • s)) :
    Function.Bijective (fun a : Γ(Y, W) ↦ a • g.pullbackSectionsLE M U W hle s) := by
  let j := W.ι ≫ g
  let T := j ⁻¹ᵁ U
  have hT : T = ⊤ := by
    rw [show T = W.ι ⁻¹ᵁ (g ⁻¹ᵁ U) from rfl]
    exact top_unique (W.ι_preimage_self.ge.trans (W.ι.preimage_mono hle))
  have : IsAffine W.toScheme := hW
  let hTa : IsAffineOpen T := hT ▸ isAffineOpen_top _
  let e : Γ(X, U) ≃ₗ[Γ(X, U)] Γ(M, U) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ s) hs
  let := (j.app U).hom.toAlgebra
  let e' :=
    (AlgebraTensorModule.rid Γ(X, U) Γ(W.toScheme, T) Γ(W.toScheme, T)).symm ≪≫ₗ
      e.baseChange Γ(X, U) Γ(W.toScheme, T) ≪≫ₗ j.pullbackSectionsEquiv M hU hTa
  have he₁ : e' 1 = j.pullbackSections M U s := by
    -- Expose the extension-of-scalars module as a tensor product.
    change j.pullbackSectionsEquiv M hU hTa
      ((e.baseChange Γ(X, U) Γ(W.toScheme, T)) ((1 : Γ(W.toScheme, T)) ⊗ₜ 1)) = _
    rw [LinearEquiv.baseChange_tmul]
    have he : e 1 = s := one_smul _ s
    exact (j.pullbackSectionsEquiv_one_tmul M hU hTa (e 1)).trans
      (congrArg (j.pullbackSections M U) he)
  have he' (a : Γ(W.toScheme, T)) : e' a = a • j.pullbackSections M U s := by
    rw [← he₁, ← e'.map_smul, smul_eq_mul, mul_one]
  have hle' : T ≤ W.ι ⁻¹ᵁ W := hT ▸ W.ι_preimage_self.ge
  let P := (pullback g).obj M
  let φ := W.ι.pullbackSectionsLE P W T hle'
  let ρ := W.ι.appLE W T hle'
  let ψ := ((pullbackComp W.ι g).hom.app M).app T
  have hρ' (V : W.toScheme.Opens) (hV : V = ⊤) :
      IsIso (W.ι.appLE W V (hV ▸ W.ι_preimage_self.ge)) := by
    subst V
    infer_instance
  have hρ : IsIso ρ := hρ' T hT
  have hψ : Function.Bijective ψ := by
    let := ((pullbackComp W.ι g).app M).isIso_hom
    exact ConcreteCategory.bijective_of_isIso _
  have hφ := bijective_pullbackSectionsLE_ι P W T hT
  have hc (a : Γ(Y, W)) : ψ (φ (a • g.pullbackSectionsLE M U W hle s)) = e' (ρ a) := by
    rw [map_smulₛₗ, Scheme.Modules.Hom.app_smul, he']
    congr 1
    rw [Scheme.Hom.pullbackSectionsLE_comp_hom, Scheme.Hom.pullbackSectionsLE_self]
  have hh := e'.bijective.comp (ConcreteCategory.bijective_of_isIso ρ)
  have hcomp : ((ψ ∘ φ) ∘ fun a : Γ(Y, W) ↦
      a • g.pullbackSectionsLE M U W hle s) = e' ∘ ρ := funext hc
  exact (Function.Bijective.of_comp_iff' (hψ.comp hφ) _).mp (hcomp.symm ▸ hh)

end AlgebraicGeometry.Scheme.Hom

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Kernel.Basic

/-!
# The kernel of the signed Picard action

The sign of a kernel element of `GeometricRealization.existsUnique_signedPicardHom`
forces even inversion parity. The normal form
`Quiver.Path.exists_xPullback_eq_of_even_inversionCount` supplies an inversion-free
representative. Comparing its marked realization with the identity detects
equality on the independent X coordinates, including for one- and two-component
boundaries.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MulOpposite Scheme
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric DiagonalizableGroup

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L : Type} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L} {E : SkewExchangeMatrix (Fin r)}
  {A N₀ : Type} [AddCommGroup A] [AddCommGroup N₀] [IsAddFG A] [IsAddFG N₀]
  [Module.Free ℤ A] [Module.Free ℤ N₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "X[" coeff "," r "]" => scheme coeff (Fin r →₀ ℤ)
local notation "sX[" k "," r "]" => structureMap k (Fin r →₀ ℤ)
local notation "T[" coeff "," M "]" => Grp.X (groupScheme coeff (FGCommGrpCat.of
  (Multiplicative M)))
local notation "Dtor[" coeff "," Φ "," h "]" => Scheme.IdealSheafData.subscheme
  (Fan.toricBoundaryIdeal coeff Φ h)
local notation "Loops[" E "]" => End (Prefunctor.obj (Paths.of (SkewExchangeMatrix (Fin r))) E)
local notation "F[" w "]" => Quiver.Path.xRationalMap k₀ (End.asHom (w : Loops[E]))
local notation "signedEval[" w "]" => op (signedClusterModularGroupMap k₀ E (w : Loops[E]))

local instance (w : Loops[E]) : F[w].IsDominant :=
  Quiver.Path.instIsDominantXRationalMap k₀ (End.asHom w)

local instance (w : Loops[E]) : F[w].IsOver sX[k₀,r] sX[k₀,r] :=
  Quiver.Path.instIsOverXRationalMapStructureMapFinsuppInt k₀ (End.asHom w)

variable [Smooth T[k₀,A].hom] [(Φ.finiteFanScheme k₀).IsProjectiveOver k₀] [B.IsPerfPair]
  {P : Point T[k₀,A] → MarkedSurface k₀ n B X[k₀,r]}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily (Dtor[k₀,Φ,hΦ₀] ↘ Spec (.of k₀))] {γ : Type*} {a : γ →
    (Dtor[k₀,Φ,hΦ₀] ↘ Spec (.of k₀)).smoothLocus}
  {T : NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] Additive (LineBundleClass (Φ.finiteFanScheme k₀)) × (Fin r → ℤ)}
  (centers : Point T[k₀,A] → Multiplicative (Fin r → ℤ) →* k₀ˣ)

variable (hc : Φ.IsComplete) (u : ZMod m ≃ Φ.Ray)
  (hvertices : ∀ j, Dtor[k₀,Φ,hΦ₀].dualGraphVertexEquiv a (T.vertex j) =
    Φ.boundaryNormalizationComponentEquiv k₀ hΦ (u j))
  (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
  (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
    (Fan.toricBoundaryIdeal k₀ Φ hΦ₀).subschemeι (Dtor[k₀,Φ,hΦ₀].dualGraphEdgeEquiv a
      (T.edge j)).val =
      (Φ.distinguishedSection (R := k₀) σ) (IsLocalRing.closedPoint k₀))
  (survives : Set Φ.Ray)
  (hmodels : ∀ c, ∃ p : ContractedToricFiber b s hΦ T origin ι (centers c) (P c),
    p.IsNodalContraction ∧ Set.range p.boundaryRayEmbedding = survives)
  (D : ZMod n → L)
  (hmark : ∀ c j, (P c).boundaryClass (hmodels c).choose_spec.1.cartier j = D j)
  (e : T[k₀,A].left ≅ X[k₀,r]) (he : e.hom ≫ sX[k₀,r] = T[k₀,A].hom)
  (v : A →+ N₀)
  (hchart : ∀ c : Point T[k₀,A], ∃ (j : T[k₀,N₀].left ⤏ (P c).surface) (_ : j.IsDominant),
    j.comp (P c).evaluation = ((evaluationAtCenter k₀ v c.left (Over.w c)) ≫ e.hom).toRationalMap)

open SignedBoundaryIsometryGroup

include hc hvertices hdet hnodes hmodels hmark he hchart in
/-- The signed Picard homomorphism of a fixed ordered toric presentation has
trivial kernel if it evaluates on loop representatives by inversion parity and
marked pullback, and inversion-free loops admit geometric realizations. -/
theorem signedPicardHom_ker_eq_bot
    (ρ : (SignedClusterModularGroup k₀ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B D)
    (hρ : ∀ (w : Loops[E]),
      sign B D (ρ (signedEval[w])) = (-1 : ℤˣ) ^ (End.asHom w).inversionCount ∧
      ∀ {C : T[k₀,A].left.PartialMap T[k₀,A].left} [IsDominant C.hom]
        [C.IsOver T[k₀,A].hom T[k₀,A].hom]
        (R : GeometricRealization P P C F[w]),
        ρ (signedEval[w]) =
          R.toSignedBoundaryIsometry D (fun c ↦ (hmodels c).choose_spec.1.cartier) hmark)
    (hreal : ∀ w : inversionFreeLoops E, ∃ (C : T[k₀,A].left.PartialMap T[k₀,A].left)
      (hC : IsDominant C.hom) (hCO : C.IsOver T[k₀,A].hom T[k₀,A].hom),
      letI := hC
      letI := hCO
      Nonempty (GeometricRealization P P C F[w.val]))
    (hinj : Function.Injective D) : ρ.ker = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨w, hw⟩ := signedClusterModularGroupMap_surjective k₀ E g.unop
  have hw' : signedEval[w] = g := (congrArg op hw).trans (op_unop g)
  have hwρ : ρ (signedEval[w]) = 1 := hw'.symm ▸ MonoidHom.mem_ker.mp hg
  have hsign := (hρ w).1.symm.trans (congrArg (sign B D) hwρ)
  rw [map_one, neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)] at hsign
  obtain ⟨wfree, hfree, hword⟩ := (End.asHom w).exists_xPullback_eq_of_even_inversionCount k₀ hsign
  let loop : Loops[E] := End.of wfree
  let freeLoop : inversionFreeLoops E := ⟨loop, (mem_inversionFreeLoops_iff E loop).mpr hfree⟩
  have hrep : signedClusterModularGroupMap k₀ E w = signedClusterModularGroupMap k₀ E loop :=
    (signedClusterModularGroupMap_eq_iff k₀ E _ _).mpr hword
  obtain ⟨C, hC, hCO, ⟨R⟩⟩ := hreal freeLoop
  let : F[freeLoop.val].IsDominant := Quiver.Path.instIsDominantXRationalMap k₀ wfree
  let : F[freeLoop.val].IsOver sX[k₀,r] sX[k₀,r] :=
    Quiver.Path.instIsOverXRationalMapStructureMapFinsuppInt k₀ wfree
  let hCartier (c : Point T[k₀,A]) := (hmodels c).choose_spec.1.cartier
  have hR : R.toSignedBoundaryIsometry D hCartier hmark = 1 := by
    rw [← (hρ loop).2 R, ← hrep, hwρ]
  have hactions := congrArg Subtype.val
    (hR.trans (toSignedBoundaryIsometry_refl (P := P) D hCartier hmark).symm)
  simp only [coe_toSignedBoundaryIsometry, Prod.mk.injEq, refl_picard] at hactions
  have hI : R.picard = .refl B := B.isometryGroupEquivIsometryEquiv.symm.injective hactions.1
  have hη : R.orientation = 1 := by
    simpa only [orientation_def, refl_boundaryAction, map_one] using hactions.2
  have hF := xMap_eq_id_of_picard_eq_refl centers hc u hvertices hdet hnodes survives hmodels
    D hmark e he v hchart R hinj hI hη
  have hid : signedClusterModularGroupMap k₀ E loop = signedClusterModularGroupMap k₀ E 1 :=
    (signedClusterModularGroupMap_eq_iff k₀ E _ _).mpr
      ((Quiver.Path.xRationalMap_eq_iff k₀ _ _).mp
        (hF.trans (Quiver.Path.xRationalMap_nil k₀).symm))
  rw [← hw', hrep, hid, map_one, op_one]

end QPainleve.SignedClusterModularGroup.GeometricRealization

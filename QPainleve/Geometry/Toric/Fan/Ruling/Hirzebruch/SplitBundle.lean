/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.ProjectiveLineCharts.Overlap
public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Gluing

import QPainleve.Geometry.Toric.Fan.Hirzebruch.CoordinateBoundary
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Construction
import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Sections
import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.SplitTransition
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality

/-!
# Boundary comparison for split Hirzebruch rulings

The two summand sections and the two coordinate fibers of a split projective
bundle correspond to the invariant boundary of the Hirzebruch fan under the
comparison of ruling charts. The comparison is scheme-theoretic, as required
for the ruled case of [Gross, Hacking and Keel, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module Opposite
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable (K : Type) [Field K]

local notation "S" => Spec (CommRingCat.of K)
local notation "P" => projectiveLine K
local notation "p" => (P ↘ S)
local notation "A[" k "]" => Fan.finiteFanScheme K (projectiveLineAffineFan k)
local notation "j[" k "]" => projectiveLineAffineFanι K k
local notation "s[" k "]" => Fan.finiteFanSchemeToSpec K (projectiveLineAffineFan k)
local notation "Pₐ[" k "]" => pullback p s[k]
local notation "p₀[" l "]" => projectiveLine.polynomialPoint K (RingHom.id K) l 0
local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule K (Fin 2 → K)
local notation "line[" n "]" =>
  Functor.obj (InvertibleSheaf.toFixedRankOne (projectiveLine K))
    (Proj.symmetricAlgebraTwistingBundle K (Fin 2 → K) n)
local notation "F[" a "," b "]" =>
  Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent (projectiveLine K))
    (ObjectProperty.FullSubcategory.obj (FiniteLocallyFreeSheaf.FixedRank.biprod line[a] line[b]))
local notation "B[" a "," b "]" =>
  ObjectProperty.FullSubcategory.obj
    (Functor.obj (gradedSymmetricAlgebra (projectiveLine K)) F[a,b])

private def affineSite (k : Fin 2) : (P).AffineZariskiSite :=
  ⟨(j[k]).opensRange, isAffineOpen_opensRange (j[k])⟩

local notation "V[" k "]" => affineSite K k

private abbrev affineSiteRing (k : Fin 2) : CommRingCat := Γ(P, (V[k]).toOpens)

local notation "Γ[" k "]" => affineSiteRing K k
local notation "U[" k "]" => Spec (CommRingCat.of Γ[k])

private abbrev affineSiteFromSpec (k : Fin 2) : U[k] ⟶ P := (V[k]).property.fromSpec

local notation "i[" k "]" => affineSiteFromSpec K k

private theorem affineSite_toOpens (k : Fin 2) :
    (V[k]).toOpens = Proj.basicOpen 𝒜 (projectiveLine.coord K k) := by
  apply TopologicalSpace.Opens.ext
  exact (range_projectiveLineAffineFanι K k).trans <|
    congrArg SetLike.coe (projectiveLine.opensRange_polynomialChartι K k)

private def affineSiteIso (k : Fin 2) : A[k] ≅ U[k] :=
  IsOpenImmersion.isoOfRangeEq j[k] i[k] (IsAffineOpen.range_fromSpec (V[k]).property).symm

@[reassoc]
private theorem affineSiteIso_hom_comp_fromSpec (k : Fin 2) :
    (affineSiteIso K k).hom ≫ i[k] = j[k] :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private abbrev affineSiteAlgebra (k : Fin 2) : Algebra K Γ[k] :=
  (Spec.preimage (i[k] ≫ p)).hom.toAlgebra

private theorem isPullback_affineSiteProduct (k : Fin 2) :
    let := affineSiteAlgebra K k
    IsPullback (projectiveLine.baseChangeProjection K Γ[k])
      ((projectiveLine Γ[k] ↘ U[k]) ≫ (affineSiteIso K k).inv) p s[k] := by
  intro
  refine (projectiveLine.isPullback_baseChangeProjection K Γ[k]).of_iso
    (Iso.refl _) (Iso.refl _) (affineSiteIso K k).symm (Iso.refl _) (by simp) (by simp)
    (by simp) ?_
  rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← cancel_epi (affineSiteIso K k).hom,
    Iso.hom_inv_id_assoc, RingHom.algebraMap_toAlgebra]
  rw [CommRingCat.ofHom_hom, Spec.map_preimage,
    affineSiteIso_hom_comp_fromSpec_assoc, projectiveLineAffineFanι_def, Category.assoc,
    comp_over, finiteFanScheme_over K,
    FanHom.finiteFanSchemeHom_comp_finiteFanSchemeToSpec K]

private def affineProductIso (k : Fin 2) : Pₐ[k] ≅ projectiveLine Γ[k] :=
  (isPullback_affineSiteProduct K k).isoPullback.symm

@[reassoc]
private theorem affineProductIso_hom_toBase (k : Fin 2) :
    (affineProductIso K k).hom ≫ (projectiveLine Γ[k] ↘ U[k]) =
      pullback.snd p s[k] ≫ (affineSiteIso K k).hom := by
  simp only [← cancel_mono (affineSiteIso K k).inv,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (isPullback_affineSiteProduct K k).isoPullback_inv_snd

private abbrev splitTwistingSiteChart (a b : ℤ) (k : Fin 2) :
    projectiveLine Γ[k] ⟶ B[a,b].relativeProj :=
  projectiveLine.relativeProjSplitTwistingChart K a b k V[k] (affineSite_toOpens K k).le

local notation "c[" a "," b ";" k "]" => splitTwistingSiteChart K a b k

/-- The split chart over the affine toric base chart, with the two twisting summands
as fiber coordinates. -/
def splitTwistingProductChart (a b : ℤ) (k : Fin 2) : Pₐ[k] ⟶ B[a,b].relativeProj :=
  (affineProductIso K k).hom ≫ c[a,b;k]

local notation "u[" a "," b ";" k "]" => splitTwistingProductChart K a b k
local notation "σ[" a "," b ";" l "]" => projectiveLine.relativeProjSplitTwistingSection K a b l

/-- The split product chart is the preimage of its affine toric base chart. -/
theorem isPullback_splitTwistingProductChart (a b : ℤ) (k : Fin 2) :
    IsPullback u[a,b;k] (pullback.snd p s[k]) B[a,b].relativeProjToBase j[k] := by
  refine (projectiveLine.isPullback_relativeProjSplitTwistingChart K a b k V[k]
    (affineSite_toOpens K k).le).of_iso' (affineProductIso K k) (Iso.refl _)
    (affineSiteIso K k) (Iso.refl _) (by simp [splitTwistingProductChart]) ?_ (by simp) ?_
  · exact affineProductIso_hom_toBase K k
  · simpa only [Iso.refl_hom, Category.comp_id] using
      affineSiteIso_hom_comp_fromSpec K k

instance (a b : ℤ) (k : Fin 2) : IsOpenImmersion u[a,b;k] :=
  MorphismProperty.of_isPullback (isPullback_splitTwistingProductChart K a b k).flip inferInstance

/-- The split product chart lies over the prescribed affine toric chart of the base. -/
@[reassoc (attr := simp)]
theorem splitTwistingProductChart_toBase (a b : ℤ) (k : Fin 2) :
    u[a,b;k] ≫ B[a,b].relativeProjToBase = pullback.snd p s[k] ≫ j[k] :=
  (isPullback_splitTwistingProductChart K a b k).w

/-- The split product chart uses the split frame over the ring of sections on
the corresponding base open. The comparison preserves both product projections,
so restriction and change of frame can be computed in these affine coordinates. -/
theorem exists_relativeProjSplitTwistingChart_eq_splitTwistingProductChart (k : Fin 2) :
    ∃ (U : (P).AffineZariskiSite)
      (hU : U.toOpens = Proj.basicOpen 𝒜 (projectiveLine.coord K k))
      (a : A[k] ≅ Spec (.of Γ(P, U.toOpens)))
      (v : Pₐ[k] ≅ projectiveLine Γ(P, U.toOpens)),
      a.hom ≫ U.property.fromSpec = j[k] ∧
      v.hom ≫ (projectiveLine Γ(P, U.toOpens) ↘ Spec (.of Γ(P, U.toOpens))) =
        pullback.snd p s[k] ≫ a.hom ∧
      let := (Spec.preimage (U.property.fromSpec ≫ p)).hom.toAlgebra
      v.hom ≫ projectiveLine.baseChangeProjection K Γ(P, U.toOpens) = pullback.fst p s[k] ∧
      ∀ m n : ℤ, v.hom ≫ projectiveLine.relativeProjSplitTwistingChart K m n k U hU.le = u[m,n;k] :=
  ⟨V[k], affineSite_toOpens K k, affineSiteIso K k, affineProductIso K k,
    affineSiteIso_hom_comp_fromSpec K k, affineProductIso_hom_toBase K k,
    (isPullback_affineSiteProduct K k).isoPullback_inv_fst, fun _ _ ↦ rfl⟩

private theorem ker_coordinatePoint_comap_affineProductIso (k l : Fin 2) :
    (projectiveLine.polynomialPoint Γ[k] (RingHom.id _) l 0).ker.comap (affineProductIso K k).hom =
      (p₀[l]).ker.comap (pullback.fst p s[k]) := by
  let := affineSiteAlgebra K k
  have hp : (p₀[l]) ≫ p = 𝟙 S := by simp [projectiveLine.polynomialPoint_over]
  let : IsClosedImmersion (p₀[l]) := (p₀[l]).isClosedImmersion_of_comp_eq_id hp
  have h := (projectiveLine.isPullback_baseChangeProjection K Γ[k]).ker_eq_comap_of_comp_eq_id
    hp (x' := projectiveLine.polynomialPoint Γ[k] (RingHom.id _) l 0)
    (by simp [projectiveLine.polynomialPoint_over]) (by
      rw [projectiveLine.polynomialPoint_comp_baseChangeProjection, RingHom.id_comp]
      conv_rhs => rw [projectiveLine.polynomialPoint_def]
      rw [projectiveLine.polynomialPoint_def, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
      congr 2
      apply CommRingCat.hom_ext
      apply Polynomial.ringHom_ext <;> simp)
  rw [h, ← comap_comp]
  exact congrArg ((p₀[l]).ker.comap) (isPullback_affineSiteProduct K k).isoPullback_inv_fst

/-- The two summand sections restrict to the constant homogeneous coordinate
sections on each product chart. -/
theorem comap_ker_splitTwistingSection_productChart (a b : ℤ) (k l : Fin 2) :
    (σ[a,b;l]).ker.comap u[a,b;k] = (p₀[l]).ker.comap (pullback.fst p s[k]) := by
  rw [splitTwistingProductChart, comap_comp, splitTwistingSiteChart,
    projectiveLine.relativeProjSplitTwistingChart_def,
    ← projectiveLine.ker_polynomialPoint_eq_comap_relativeProjSplitTwistingSection]
  exact ker_coordinatePoint_comap_affineProductIso K k l

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℤ) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "X" => Fan.finiteFanScheme K Φ
local notation "q" => Φ.characterRuling K (LinearMap.toAddMonoidHom (Basis.coord b 1))
  (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)
local notation "E[" k "]" => hirzebruchRulingAffineIso K b e r hr hΦ hc k
local notation "v[" k "]" => Iso.inv (E[k]) ≫ pullback.fst q j[k]
local notation "I[" l "]" => Φ.rayDivisorIdeal K hΦ (r ((![0, 2] : Fin 2 → Fin 4) l))

private def rulingCover : (X).OpenCover :=
  (Scheme.Cover.mkOfCovers (Fin 2) (fun k ↦ A[k]) (projectiveLineAffineFanι K)
    (exists_projectiveLineAffineFanι_apply_eq K)).pullback₁ q

include hr in
private theorem comap_ker_splitTwistingSection_of_chart_comparison [IsAlgClosed K] (a b' : ℤ)
    (f : X ⟶ B[a,b'].relativeProj) (hf : ∀ k, v[k] ≫ f = u[a,b';k]) (l : Fin 2) :
    (σ[a,b';l]).ker.comap f = I[l] := by
  refine ext_of_comap_openCover (rulingCover K b e r hr) fun (k : Fin 2) ↦ ?_
  -- The cover is pulled back along the ruling, with first projection on each chart.
  change ((σ[a,b';l]).ker.comap f).comap (pullback.fst q j[k]) =
    I[l].comap (pullback.fst q j[k])
  rw [← comap_coordinate_section_hirzebruch_ruling_affine_iso K b e r hr hΦ hc k l]
  have h := congrArg ((σ[a,b';l]).ker.comap) (hf k)
  rw [comap_ker_splitTwistingSection_productChart, Category.assoc, comap_comp, comap_comp] at h
  simpa only [← comap_comp, Iso.hom_inv_id_assoc] using
    congrArg (fun J ↦ Scheme.IdealSheafData.comap J (E[k]).hom) h

local notation "d[" k "]" => projectiveLineTorusProductToAffine K k

/-- The two standard split product charts glue by the Hirzebruch transition of
parameter `b - a` on the base torus. -/
theorem splitTwistingProductChart_overlap (a b : ℤ) :
    d[0] ≫ u[a,b;0] = (hirzebruchRulingOverlapTransition K (b - a)).hom ≫ d[1] ≫ u[a,b;1] :=
  split_twisting_product_chart_overlap K a b (affineSite K) (affineSite_toOpens K)
    (fun k ↦ (affineSiteIso K k).hom) (affineSiteIso_hom_comp_fromSpec K)
    (fun k ↦ (affineProductIso K k).hom)
    (fun k ↦ (isPullback_affineSiteProduct K k).isoPullback_inv_fst)
    (affineProductIso_hom_toBase K)

include hr in
/-- For summand degrees whose difference is the signed Hirzebruch parameter, the
isomorphism over the base identifies the product charts, each horizontal ray with
its summand section, and the toric boundary with the two sections and coordinate fibers. -/
theorem exists_hirzebruch_boundary_iso_of_split_twisting [IsAlgClosed K]
    (a b' : ℤ) (he : e = b' - a) :
    ∃ f : X ≅ B[a,b'].relativeProj, f.hom ≫ B[a,b'].relativeProjToBase = q ∧
      (∀ k : Fin 2, v[k] ≫ f.hom = u[a,b';k]) ∧
      (∀ l : Fin 2, (σ[a,b';l]).ker.comap f.hom = I[l]) ∧
      let π := B[a,b'].relativeProjToBase
      let D := (σ[a,b';0]).ker * (σ[a,b';1]).ker * (p₀[0].ker.comap π) * (p₀[1].ker.comap π)
      D.comap f.hom = Φ.toricBoundaryIdeal K hc.nonempty_cones := by
  let := hc.nonempty_cones
  obtain ⟨f, ⟨hbase, hcharts⟩, -⟩ := existsUnique_hirzebruch_ruling_iso_of_overlap_transition
    K B[a,b'].relativeProjToBase b e r hr hΦ hc (fun k ↦ u[a,b';k])
    (isPullback_splitTwistingProductChart K a b')
    (by rw [he]; exact splitTwistingProductChart_overlap K a b')
  have hsec :=
    comap_ker_splitTwistingSection_of_chart_comparison K b e r hr hΦ hc a b' f.hom hcharts
  refine ⟨f, hbase, hcharts, hsec, ?_⟩
  obtain ⟨s', -, hs', -, hD⟩ :=
    exists_hirzebruch_toric_boundary_sections_and_fibers K b e hΦ r hr hc
  simp only [comap_mul, hsec, ← comap_comp, hbase, hD, hs']

/-- The projectivization of two twists has a Hirzebruch model of index `|b' - a|`
in the prescribed lattice basis. The isomorphism is over the projective line and
identifies the toric boundary with the two summand sections and coordinate fibers. -/
theorem exists_hirzebruch_model_of_split_twisting [IsAlgClosed K]
    (hi : IsIntegralLattice i) (a b' : ℤ) :
    let n := (b' - a).natAbs
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (hΨc : Ψ.IsComplete) (s : Fin 4 ≃ Ψ.Ray)
      (hs : (fun j ↦ (s j).primitiveGenerator) = ![b 0, b 1, -b 0, (n : ℤ) • b 0 - b 1])
      (f : (Ψ.finiteFanScheme K) ≅ B[a,b'].relativeProj),
      f.hom ≫ B[a,b'].relativeProjToBase = Ψ.characterRuling K (b.coord 1).toAddMonoidHom
        (nonneg_or_nonpos_hirzebruch_ruling_character b (n : ℤ) s hs) ∧
      let π := B[a,b'].relativeProjToBase
      let D := (σ[a,b';0]).ker * (σ[a,b';1]).ker * (p₀[0].ker.comap π) * (p₀[1].ker.comap π)
      D.comap f.hom = Ψ.toricBoundaryIdeal K hΨc.nonempty_cones := by
  dsimp only
  let n := (b' - a).natAbs
  obtain ⟨Ψ, ⟨hΨ, hΨc, hrange⟩, -⟩ := existsUnique_hirzebruch_fan b hi n
  obtain ⟨s, hs⟩ := exists_rayEquiv_of_hirzebruch_ray_generators b (n : ℤ) hrange
  -- Choose the section marking with the sign prescribed by the order of the summands.
  have hmark : ∃ (c : Basis (Fin 2) ℤ N) (t : Fin 4 ≃ Ψ.Ray),
      (fun j ↦ (t j).primitiveGenerator) = ![c 0, c 1, -c 0, (b' - a) • c 0 - c 1] ∧
      c.coord 1 = b.coord 1 := by
    rcases le_total a b' with hab | hba
    · have he : (n : ℤ) = b' - a := by omega
      exact ⟨b, s, he ▸ hs, rfl⟩
    have he : -(n : ℤ) = b' - a := by omega
    obtain ⟨c, t, ht, ht₁, ht₀⟩ := exists_hirzebruch_opposite_section_basis b (n : ℤ) s hs
    have h₀ : c 0 = -b 0 := calc
      c 0 = (t 0).primitiveGenerator := (congrFun ht 0).symm
      _ = -b 0 := by rw [ht₀]; exact congrFun hs 2
    have h₁ : c 1 = b 1 := calc
      c 1 = (t 1).primitiveGenerator := (congrFun ht 1).symm
      _ = b 1 := by rw [ht₁]; exact congrFun hs 1
    have hcoord : c.coord 1 = b.coord 1 := by
      apply c.ext
      intro j
      fin_cases j
      · calc
          c.coord 1 (c 0) = 0 := by simp [Basis.coord_apply]
          _ = b.coord 1 (c 0) := by simp [h₀, Basis.coord_apply]
      · calc
          c.coord 1 (c 1) = 1 := by simp [Basis.coord_apply]
          _ = b.coord 1 (c 1) := by simp [h₁, Basis.coord_apply]
    exact ⟨c, t, he ▸ ht, hcoord⟩
  obtain ⟨c, t, ht, hcoord⟩ := hmark
  obtain ⟨f, hf, -, -, hD⟩ :=
    exists_hirzebruch_boundary_iso_of_split_twisting K c (b' - a) t ht hΨ hΨc a b' rfl
  refine ⟨Ψ, hΨ, hΨc, s, hs, f, hf.trans ?_, hD⟩
  congr 1
  exact congrArg LinearMap.toAddMonoidHom hcoord

end TauCeti.Toric.Fan

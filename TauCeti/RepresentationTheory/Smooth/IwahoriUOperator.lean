/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.UOperator
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Iwahori

/-!
# Multiplicativity of the `U_t` operators at pro-`p` Iwahori level

Let `K` be a valued field with valuation subring `A` and let `I₁ ⊆ GL_m(K)` be the image of the
pro-`p` Iwahori subgroup `TauCeti.iwahoriOne m A`. Combining the Iwahori factorization
(`TauCeti.exists_eq_mul_diagGL_mul_permutationGL_mul_and_isLowerTriangular`) with conjugation of
upper- and lower-triangular elements of `I₁` by dominant diagonal matrices shows that `I₁` splits
along every pair of dominant diagonal matrices `diagGL t`, `diagGL t'`.

For a smooth representation `ρ` of `GL_m(K)` on an `A`-module `V` (with `I₁` compact of invertible
pro-order), `Representation.uOperator_uOperator_apply` then yields multiplicativity
`U_{diag t} (U_{diag t'} v) = U_{diag (t * t')} v` on `V^{I₁}`.

## Main results

* `TauCeti.exists_map_iwahoriOne_split`: `I₁` splits along every pair of dominant diagonal
  matrices `diagGL t`, `diagGL t'`.
* `Representation.uOperator_diagGL_uOperator_diagGL_apply`:
  `U_{diag t} ∘ U_{diag t'} = U_{diag (t * t')}` on `I₁`-invariants for dominant `t`, `t'`.

## References

* W. Casselman, *Introduction to the theory of admissible representations of `p`-adic reductive
  groups* (unpublished notes, 1995).
* Adapted from `src/Lib/LocalGL/Iwahori/ParahoricStructure.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.compactMean_diagGL_compactMean_diagGL`.
-/

public section

open Matrix

namespace TauCeti

variable {K : Type*} [Field K] (A : ValuationSubring K) {m : Type*} [Fintype m] [LinearOrder m]

/-- The pro-`p` Iwahori subgroup `I₁ ⊆ GL_m(K)` splits along every pair of dominant diagonal
matrices `diagGL t`, `diagGL t'`: every `c ∈ I₁` factors as `c = a * b` with
`diagGL t * a * (diagGL t)⁻¹ ∈ I₁` and `(diagGL t')⁻¹ * b * diagGL t' ∈ I₁`. -/
theorem exists_map_iwahoriOne_split {t t' : m → Kˣ}
    (ht : Monotone fun i ↦ A.valuation (t i : K))
    (ht' : Monotone fun i ↦ A.valuation (t' i : K)) {c : GL m K}
    (hc : c ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K))) :
    ∃ a b : GL m K, c = a * b ∧
      diagGL t * a * (diagGL t)⁻¹ ∈
        (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)) ∧
      (diagGL t')⁻¹ * b * diagGL t' ∈
        (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)) := by
  obtain ⟨u, hu_ut, -, -, -, -, -, h_iw⟩ :=
    exists_eq_mul_diagGL_mul_permutationGL_mul_and_isLowerTriangular A c
  obtain ⟨hu_mem, hlow⟩ := h_iw hc
  have hu_tri : (u : Matrix m m K).IsUpperTriangular :=
    (UpperUnitriangularGroup.mem_iff.mp hu_ut).isUpperTriangular
  refine ⟨u, u⁻¹ * c, (mul_inv_cancel_left u c).symm,
    diagGL_mul_mul_inv_mem_map_iwahoriOne_of_isUpperTriangular A ht hu_mem hu_tri,
    diagGL_inv_mul_mul_mem_map_iwahoriOne_of_isLowerTriangular A ht'
      (mul_mem (inv_mem hu_mem) hc) hlow⟩

end TauCeti

namespace Representation

variable {R K Γ₀ V : Type*} [CommRing R] [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  [Valued K Γ₀] [AddCommGroup V] [Module R V]
  {m : Type*} [Fintype m] [LinearOrder m]

/-- For a smooth representation `ρ` of `GL_m(K)` over a valued field `K` and dominant diagonal
matrices `t`, `t'`, the pro-`p` Iwahori `U`-operators multiply on `I₁`-invariants:
`U_{diag t} (U_{diag t'} v) = U_{diag (t * t')} v`. -/
theorem uOperator_diagGL_uOperator_diagGL_apply (ρ : Representation R (GL m K) V) [IsSmooth ρ]
    [CompactSpace ((TauCeti.iwahoriOne m (Valued.v (R := K)).valuationSubring).map
      (GeneralLinearGroup.map (algebraMap _ K)))]
    (hI : TauCeti.HasUnitProOrder R
      ((TauCeti.iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (GeneralLinearGroup.map (algebraMap _ K))))
    {t t' : m → Kˣ}
    (ht : Monotone fun i ↦ (Valued.v (R := K)).valuationSubring.valuation (t i : K))
    (ht' : Monotone fun i ↦ (Valued.v (R := K)).valuationSubring.valuation (t' i : K))
    {v : V} (hv : v ∈ invariants (ρ.comp
      ((TauCeti.iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (GeneralLinearGroup.map (algebraMap _ K))).subtype)) :
    ρ.uOperator _ hI (TauCeti.diagGL t) (ρ.uOperator _ hI (TauCeti.diagGL t') v) =
      ρ.uOperator _ hI (TauCeti.diagGL (t * t')) v := by
  rw [map_mul TauCeti.diagGL]
  exact ρ.uOperator_uOperator_apply _ hI
    (fun _ hc ↦ TauCeti.exists_map_iwahoriOne_split _ ht ht' hc) hv

end Representation

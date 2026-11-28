/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.GLn.HallAlgebra.Adjunction

/-!
# Rank parts, cuspidality, and orthogonality in the Hall algebra

Let `k` be a field. For `F : TauCeti.HallAlgebra k` and `n : ℕ`, `F.rankPart n` restricts `F` to
similarity classes of dimension `n` and vanishes elsewhere. This file develops the interaction of
`rankPart` with block averages, cuspidality, and the rank inner product `rankInner`, directly
supporting the cuspidality and orthogonality of Green's functions `τ_P = (-1)^d · (C_{θ_x})|_d`:

* `TauCeti.HallAlgebra.rankPart_rankPart_self`, `TauCeti.HallAlgebra.rankPart_rankPart_of_ne`:
  idempotence and orthogonality of the projections `rankPart n`.
* `TauCeti.HallAlgebra.blockAverage_rankPart`:
  `δ(F|_n)(a, b) = if a.dim + b.dim = n then δF(a, b) else 0`.
* `TauCeti.HallAlgebra.IsCuspidal.rankPart`: restricting a cuspidal element to a single rank
  preserves cuspidality.
* `TauCeti.HallAlgebra.rankInner_rankPart_left`, `TauCeti.HallAlgebra.rankInner_rankPart_right`,
  `TauCeti.HallAlgebra.rankInner_rankPart_rankPart_of_ne`: elements supported in different ranks
  are orthogonal for `rankInner`.

## References

* Adapted from `src/Lib/LocalGL/Green/TauFunctions.lean` and
  `src/Lib/LocalGL/Green/LabelCharacters.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC).
-/

public section

open TauCeti.SimilarityClass

namespace TauCeti.HallAlgebra

variable {k : Type*} [Field k]

/-- Applying `rankPart n` twice is the same as applying it once. -/
@[simp]
theorem rankPart_rankPart_self (n : ℕ) (F : HallAlgebra k) :
    rankPart n (rankPart n F) = rankPart n F := by
  ext c
  simp only [rankPart_apply]
  split_ifs <;> rfl

/-- Applying `rankPart m` after `rankPart n` for `m ≠ n` gives `0`. -/
theorem rankPart_rankPart_of_ne {m n : ℕ} (h : m ≠ n) (F : HallAlgebra k) :
    rankPart m (rankPart n F) = 0 := by
  ext c
  simp only [rankPart_apply, zero_apply]
  split_ifs with h1 h2
  · exact absurd (h1.symm.trans h2) h
  · rfl
  · rfl

/-- `rankPart n` vanishes on `0`. -/
@[simp]
theorem rankPart_zero (n : ℕ) : rankPart n (0 : HallAlgebra k) = 0 := by
  ext c
  simp [rankPart_apply]

/-- `rankPart n` distributes over addition. -/
@[simp]
theorem rankPart_add (n : ℕ) (F H : HallAlgebra k) :
    rankPart n (F + H) = rankPart n F + rankPart n H := by
  ext c
  simp only [rankPart_apply, add_apply]
  split_ifs <;> simp

/-- `rankPart n` commutes with scalar multiplication. -/
@[simp]
theorem rankPart_smul (n : ℕ) (a : ℂ) (F : HallAlgebra k) :
    rankPart n (a • F) = a • rankPart n F := by
  ext c
  simp only [rankPart_apply, smul_apply]
  split_ifs <;> simp

section Fintype

variable [Fintype k]

/-- The block average of `F|_n` at `(a, b)` equals the block average of `F` when `a.dim + b.dim = n`
and vanishes otherwise. -/
theorem blockAverage_rankPart (n : ℕ) (F : HallAlgebra k) (a b : SimilarityClass k) :
    blockAverage (rankPart n F) a b = if a.dim + b.dim = n then blockAverage F a b else 0 := by
  let _ := Fintype.ofEquiv (Matrix (Fin a.dim) (Fin b.dim) k) Matrix.toLin'.toEquiv
  rw [← ofEnd_rep a, ← ofEnd_rep b, blockAverage_ofEnd, blockAverage_ofEnd]
  simp only [rankPart_apply, dim_ofEnd, Module.finrank_prod]
  split_ifs <;> simp

/-- Restricting a cuspidal element of the Hall algebra to a single rank preserves cuspidality. -/
theorem IsCuspidal.rankPart {F : HallAlgebra k} (hF : F.IsCuspidal) (n : ℕ) :
    (rankPart n F).IsCuspidal := by
  rw [isCuspidal_iff]
  intro a b ha hb
  rw [blockAverage_rankPart, hF.blockAverage_eq_zero ha hb, ite_self]

/-- The rank-`n` inner product with `F|_m` on the left is `⟨F, H⟩_n` if `n = m` and `0`
otherwise. -/
theorem rankInner_rankPart_left [DecidableEq k] (n m : ℕ) (F H : HallAlgebra k) :
    rankInner n (rankPart m F) H = if n = m then rankInner n F H else 0 := by
  split_ifs with h
  · subst h
    simp [rankInner_def, rankPart_apply]
  · exact rankInner_eq_zero_of_left (fun c hc ↦ by simp [rankPart_apply, hc, h]) H

/-- The rank-`n` inner product with `H|_m` on the right is `⟨F, H⟩_n` if `n = m` and `0`
otherwise. -/
theorem rankInner_rankPart_right [DecidableEq k] (n m : ℕ) (F H : HallAlgebra k) :
    rankInner n F (rankPart m H) = if n = m then rankInner n F H else 0 := by
  split_ifs with h
  · subst h
    simp [rankInner_def, rankPart_apply]
  · exact rankInner_eq_zero_of_right F (fun c hc ↦ by simp [rankPart_apply, hc, h])

/-- Elements supported in distinct ranks are orthogonal for `rankInner n` for every `n`. -/
theorem rankInner_rankPart_rankPart_of_ne [DecidableEq k] (n : ℕ) {m m' : ℕ} (h : m ≠ m')
    (F H : HallAlgebra k) :
    rankInner n (rankPart m F) (rankPart m' H) = 0 := by
  rw [rankInner_rankPart_left, rankInner_rankPart_right]
  split_ifs with h1 h2
  · exact absurd (h1.symm.trans h2) h
  · rfl
  · rfl

end Fintype

end TauCeti.HallAlgebra

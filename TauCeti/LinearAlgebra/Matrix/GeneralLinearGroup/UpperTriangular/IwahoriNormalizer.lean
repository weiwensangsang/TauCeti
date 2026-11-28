/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.IwasawaBruhat
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# Normaliser and transvection membership for the pro-`p` Iwahori subgroup

Let `K` be a field with a valuation subring `A`, and let `I₁ ⊆ GL_m(K)` be the image of the
pro-`p` Iwahori subgroup `TauCeti.iwahoriOne m A` of `GL_m(A)`. This file establishes basic
entrywise and conjugation properties used in the Iwahori–Hecke quadratic relation and exponent
identities:

* `TauCeti.valuation_diag_eq_one_of_mem_map_iwahoriOne`: every diagonal entry of `g ∈ I₁` has
  valuation `1`.
* `TauCeti.diagGL_mul_mul_inv_mem_map_iwahoriOne_of_valuation_eq_one`: diagonal matrices whose
  entries all have valuation `1` normalise `I₁`.
* `TauCeti.transvectionUnit_mem_map_iwahoriOne_iff`: a transvection `1 + c E_{ij}` (`i ≠ j`) lies
  in `I₁` iff `v(c) ≤ 1` when `i < j`, and `v(c) < 1` when `j < i`.

## References

* Adapted from `src/Lib/LocalGL/Iwahori/ParahoricStructure.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.v_diag_eq_one_of_mem_proIwahori`, `New.diagGL_conj_mem_proIwahori_of_v_eq_one`, and
  `New.transvectionGL_mem_proIwahori`.
-/

public section

namespace TauCeti

open Matrix

variable {K : Type*} [Field K] (A : ValuationSubring K) {m : Type*} [Fintype m] [LinearOrder m]

/-- Every diagonal entry of an element of the pro-`p` Iwahori subgroup `I₁ ⊆ GL_m(K)` has
valuation `1`. -/
theorem valuation_diag_eq_one_of_mem_map_iwahoriOne {g : GL m K}
    (hg : g ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K))) (i : m) :
    A.valuation (g i i) = 1 := by
  have hlt : A.valuation (g i i - 1) < A.valuation (1 : K) := by
    simpa only [map_one] using ((mem_map_iwahoriOne_iff A).mp hg).2.2 i
  simpa only [sub_add_cancel, map_one] using Valuation.map_add_eq_of_lt_right A.valuation hlt

/-- A diagonal matrix whose entries all have valuation `1` normalises the pro-`p` Iwahori
subgroup `I₁ ⊆ GL_m(K)`. -/
theorem diagGL_mul_mul_inv_mem_map_iwahoriOne_of_valuation_eq_one {t : m → Kˣ}
    (ht : ∀ i : m, A.valuation (t i : K) = 1) {g : GL m K}
    (hg : g ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K))) :
    diagGL t * g * (diagGL t)⁻¹ ∈
      (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)) := by
  obtain ⟨h1, hlow, hdiag⟩ := (mem_map_iwahoriOne_iff A).mp hg
  rw [mem_map_iwahoriOne_iff]
  refine ⟨fun i j ↦ ?_, fun i j hji ↦ ?_, fun i ↦ ?_⟩
  · rw [diagGL_mul_mul_inv_apply, Units.val_inv_eq_inv_val]
    simpa only [map_mul, map_inv₀, ht i, ht j, inv_one, one_mul, mul_one] using h1 i j
  · rw [diagGL_mul_mul_inv_apply, Units.val_inv_eq_inv_val]
    simpa only [map_mul, map_inv₀, ht i, ht j, inv_one, one_mul, mul_one] using hlow hji
  · rw [diagGL_mul_mul_inv_apply, mul_right_comm, Units.mul_inv, one_mul]
    exact hdiag i

/-- A transvection `1 + c E_{ij}` (`i ≠ j`) lies in the pro-`p` Iwahori subgroup `I₁ ⊆ GL_m(K)`
iff `A.valuation c ≤ 1` when `i < j` and `A.valuation c < 1` when `j < i`. -/
theorem transvectionUnit_mem_map_iwahoriOne_iff {i j : m} (hij : i ≠ j) (c : K) :
    transvectionUnit hij c ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)) ↔
      (i < j ∧ A.valuation c ≤ 1) ∨ (j < i ∧ A.valuation c < 1) := by
  rw [mem_map_iwahoriOne_iff]
  constructor
  · rintro ⟨h1, hlow, -⟩
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact Or.inl ⟨hlt, by simpa [coe_transvectionUnit_eq_one_add_single, hij] using h1 i j⟩
    · exact Or.inr ⟨hgt, by simpa [coe_transvectionUnit_eq_one_add_single, hij] using hlow hgt⟩
  · intro h
    refine ⟨fun a b ↦ ?_, fun a b hba ↦ ?_, fun a ↦ ?_⟩
    · rw [coe_transvectionUnit_eq_one_add_single, Matrix.add_apply]
      by_cases hab : i = a ∧ j = b
      · rcases hab with ⟨rfl, rfl⟩
        rw [Matrix.one_apply_ne hij, zero_add, Matrix.single_apply_same]
        rcases h with ⟨-, hle⟩ | ⟨-, hlt⟩
        · exact hle
        · exact hlt.le
      · rw [Matrix.single_apply_of_ne (h := hab), add_zero, Matrix.one_apply]
        split_ifs <;> simp
    · rw [coe_transvectionUnit_eq_one_add_single, Matrix.add_apply, Matrix.one_apply_ne hba.ne',
        zero_add]
      by_cases hab : i = a ∧ j = b
      · rcases hab with ⟨rfl, rfl⟩
        rw [Matrix.single_apply_same]
        rcases h with ⟨hlt, -⟩ | ⟨-, hc⟩
        · exact absurd hba (lt_asymm hlt)
        · exact hc
      · simp [Matrix.single_apply_of_ne (h := hab)]
    · have hne : ¬ (i = a ∧ j = a) := fun ⟨h1, h2⟩ ↦ hij (h1.trans h2.symm)
      simp [coe_transvectionUnit_eq_one_add_single, Matrix.single_apply_of_ne (h := hne)]

end TauCeti

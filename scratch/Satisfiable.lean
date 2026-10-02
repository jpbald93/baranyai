import Baranyai

/-!
# Satisfiability certificates (outside the library)

Baranyai's theorem is an existence statement. This file gives kernel-checked concrete instances:
explicit factorisations for `(n, k) = (4, 2)` and `(6, 3)` (checked by `decide`, not derived from
the theorem), the hypotheses of `baranyai` met jointly, an explicit witness of the induction
invariant `Baranyai.Inv` at the final stage (the hypothesis of `exists_partition_of_inv`), and
instances of the transported and partition forms. The library has no `False_of_*` lemma.
-/

open Finset

namespace BaranyaiSat

/-- An explicit 1-factorisation of `K_4`: {01,23}, {02,13}, {03,12}. -/
def c42 (S : {S : Finset (Fin 4) // S.card = 2}) : Fin 3 :=
  if S.1 = {0, 1} ∨ S.1 = {2, 3} then 0 else if S.1 = {0, 2} ∨ S.1 = {1, 3} then 1 else 2

theorem c42_factorisation :
    ∀ i (v : Fin 4), ∃! S : {S : Finset (Fin 4) // S.card = 2}, c42 S = i ∧ v ∈ S.1 := by
  unfold ExistsUnique; decide

/-- The 10 triples of `Fin 6` containing `0`; a triple and its complement get the same colour. -/
def L63 : List (Finset (Fin 6)) :=
  [{0,1,2}, {0,1,3}, {0,1,4}, {0,1,5}, {0,2,3}, {0,2,4}, {0,2,5}, {0,3,4}, {0,3,5}, {0,4,5}]

/-- An explicit Baranyai factorisation for `n = 6`, `k = 3` into `C(5,2) = 10` classes. -/
def c63 (S : {S : Finset (Fin 6) // S.card = 3}) : Fin 10 :=
  Fin.ofNat 10 (L63.idxOf (if (0 : Fin 6) ∈ S.1 then S.1 else univ \ S.1))

theorem c63_factorisation :
    ∀ i (v : Fin 6), ∃! S : {S : Finset (Fin 6) // S.card = 3}, c63 S = i ∧ v ∈ S.1 := by
  unfold ExistsUnique; decide

/-- The colour count of `baranyai` in these cases. -/
example : (4 - 1).choose (2 - 1) = 3 ∧ (6 - 1).choose (3 - 1) = 10 := by decide

/-- The hypotheses of `baranyai` hold jointly, e.g. for `(n, k) = (6, 3)`. -/
example : 0 < 3 ∧ 3 ∣ 6 := by decide

/-- The explicit `K_4` factorisation is an instance of the conclusion of `baranyai 4 2`. -/
example : ∃ c : {S : Finset (Fin 4) // S.card = 2} → Fin ((4 - 1).choose (2 - 1)),
    ∀ i (v : Fin 4), ∃! S : {S : Finset (Fin 4) // S.card = 2}, c S = i ∧ v ∈ S.1 :=
  ⟨c42, c42_factorisation⟩

example : ∃ c : {S : Finset (Fin 6) // S.card = 3} → Fin ((6 - 1).choose (3 - 1)),
    ∀ i (v : Fin 6), ∃! S : {S : Finset (Fin 6) // S.card = 3}, c S = i ∧ v ∈ S.1 :=
  ⟨c63, c63_factorisation⟩

/-- The invariant at the final stage for `n = 4, k = 2, m = 2, M = 3`, from the `K_4`
factorisation: class `i` has slots {01,23}, {02,13}, {03,12}. Meets the hypothesis of
`Baranyai.exists_partition_of_inv`. -/
def A42 : Fin 3 → Fin 2 → Finset (Fin 4) :=
  ![![{0, 1}, {2, 3}], ![{0, 2}, {1, 3}], ![{0, 3}, {1, 2}]]

theorem A42_inv : Baranyai.Inv 4 2 2 3 4 A42 where
  disj := by decide
  cover := by decide
  size := by decide
  cnt := by decide

example := Baranyai.exists_partition_of_inv A42_inv

/-- The theorem applied to a `Finset` vertex set and to a non-`Fin` type. -/
example := Baranyai.baranyai_finset ({1, 5, 7, 9} : Finset ℕ) 2 (by decide) (by decide)
example := Baranyai.baranyai_of_card (α := Fin 2 × Fin 3) 6 3 (by decide) (by decide) (by decide)
example := Baranyai.baranyai_partition (α := Bool × Bool) 4 2 (by decide) (by decide) (by decide)
  (by decide)

end BaranyaiSat

import Baranyai

/-!
# Referee checks (outside the library)

* Non-triviality: for `n = 3`, `k = 2` there is no colouring of the 2-subsets of `Fin 3` with
  two colours in which every colour class is a perfect matching (checked by `decide`). Two is
  the count prescribed by the main theorem, `choose (3 - 1) (2 - 1) = 2`; a colouring into
  `Fin 0` does not exist at all, there being three 2-subsets.
* The converse corollary `Baranyai.dvd_card_of_factorisation` applied at `n = 3`, `k = 2`.
* A witness meeting the hypotheses of `Baranyai.step`, which carries `j < n`: the stage-0
  invariant from `Baranyai.init` at `n = 4`, `k = 2`, `m = 2`, with `0 < 4`.
* Three hypotheses used by the proof are logically removable: `baranyai` without `0 < k`,
  `choose_mul` without `0 < n`, and `weight_eq` without `j < n` still hold.
-/

open Finset

namespace BaranyaiReferee

/-- The assertion fails at `n = 3`, `k = 2` (two colours). -/
theorem no_factorisation_three_two :
    ¬ ∃ c : {S : Finset (Fin 3) // S.card = 2} → Fin 2,
      ∀ i (v : Fin 3), ∃! S : {S : Finset (Fin 3) // S.card = 2}, c S = i ∧ v ∈ S.1 := by
  unfold ExistsUnique; decide

/-- The same, for any number of colours `M > 0`, via the converse corollary. -/
example (M : ℕ) (hM : 0 < M) :
    ¬ ∃ c : {S : Finset (Fin 3) // S.card = 2} → Fin M,
      ∀ i (v : Fin 3), ∃! S : {S : Finset (Fin 3) // S.card = 2}, c S = i ∧ v ∈ S.1 := by
  rintro ⟨c, hc⟩
  have h := Baranyai.dvd_card_of_factorisation (c := c) ⟨⟨0, hM⟩, hc ⟨0, hM⟩⟩
  simp at h

/-- The hypotheses of `Baranyai.step` (including `j < n`) met jointly at `n = 4`, `k = 2`,
`m = 2`, stage `j = 0`. -/
example : ∃ A' : Fin ((4 - 1).choose (2 - 1)) → Fin 2 → Finset (Fin 4),
    Baranyai.Inv 4 2 2 ((4 - 1).choose (2 - 1)) 1 A' :=
  Baranyai.step (Baranyai.init (n := 4) (k := 2) (m := 2) (by decide) (by decide))
    (by decide) (by decide)

/-- `baranyai` without `0 < k`: still true (for `k = 0`, `k ∣ n` forces `n = 0`). -/
example (n k : ℕ) (hkn : k ∣ n) :
    ∃ c : {S : Finset (Fin n) // S.card = k} → Fin ((n - 1).choose (k - 1)),
      ∀ i (v : Fin n), ∃! S : {S : Finset (Fin n) // S.card = k}, c S = i ∧ v ∈ S.1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain rfl : n = 0 := Nat.eq_zero_of_zero_dvd hkn
    exact ⟨fun _ => ⟨0, by simp⟩, fun _ v => v.elim0⟩
  · exact baranyai n k hk hkn

/-- `choose_mul` without `0 < n`: still true. -/
example (n k : ℕ) (hk : 0 < k) : n * (n - 1).choose (k - 1) = n.choose k * k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.choose_eq_zero_of_lt hk]
  · exact Baranyai.choose_mul hk hn

/-- `weight_eq` without `j < n`: still true. -/
example (n k j : ℕ) (S : Finset (Fin n)) :
    (k - S.card) * (n - j).choose (k - S.card) = (n - j) * Baranyai.dem n k j S := by
  rcases Nat.lt_or_ge j n with hj | hj
  · exact Baranyai.weight_eq hj S
  · have h0 : n - j = 0 := by omega
    rw [h0, zero_mul]
    rcases Nat.eq_zero_or_pos (k - S.card) with h | h
    · rw [h, zero_mul]
    · rw [Nat.choose_eq_zero_of_lt h, mul_zero]

end BaranyaiReferee

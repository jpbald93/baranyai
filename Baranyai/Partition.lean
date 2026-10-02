import Baranyai.Transport

/-!
# Corollaries of Baranyai's theorem

* The colouring given by `baranyai` is a genuine partition of the `k`-subsets into perfect
  matchings: distinct colour classes are disjoint, together they contain every `k`-subset, the
  blocks of one class are pairwise disjoint, every class has exactly `n / k` blocks, and the
  number of classes is `C(n, k) / (n / k)` (`baranyai_partition`).
* Transport from `Fin n` to an arbitrary finite vertex type of cardinality `n`
  (`factorisation_congr`, `baranyai_of_card`). For a `Finset` `s` take the vertex type `↥s`.

These are consequences of the statement of `baranyai`; the hard direction is not reproved.
-/

open Finset

namespace Baranyai

variable {α : Type*}

/-- Distinct colour classes are disjoint sets of `k`-subsets. -/
theorem class_disjoint [Fintype α] {k M : ℕ} (c : {S : Finset α // S.card = k} → Fin M)
    {i j : Fin M} (hij : i ≠ j) :
    Disjoint (univ.filter fun S => c S = i) (univ.filter fun S => c S = j) := by
  rw [disjoint_filter]
  rintro S - rfl
  exact hij

/-- The colour classes together contain every `k`-subset. -/
theorem classes_cover [Fintype α] [DecidableEq α] {k M : ℕ}
    (c : {S : Finset α // S.card = k} → Fin M) :
    univ.biUnion (fun i => univ.filter fun S => c S = i) = univ := by
  ext S
  simp

/-- In a factorisation, two different blocks of the same colour are disjoint. -/
theorem block_disjoint {k M : ℕ} {c : {S : Finset α // S.card = k} → Fin M}
    (hc : ∀ i (v : α), ∃! S : {S : Finset α // S.card = k}, c S = i ∧ v ∈ S.1)
    {S T : {S : Finset α // S.card = k}} (hST : S ≠ T) (h : c S = c T) :
    Disjoint S.1 T.1 := by
  rw [Finset.disjoint_left]
  intro v hS hT
  obtain ⟨U, -, hU⟩ := hc (c T) v
  exact hST ((hU S ⟨h, hS⟩).trans (hU T ⟨rfl, hT⟩).symm)

/-- In a factorisation, each colour class has `|α| / k` blocks (stated without division). -/
theorem class_card_mul [Fintype α] [DecidableEq α] {k M : ℕ}
    {c : {S : Finset α // S.card = k} → Fin M}
    (hc : ∀ i (v : α), ∃! S : {S : Finset α // S.card = k}, c S = i ∧ v ∈ S.1) (i : Fin M) :
    (univ.filter fun S => c S = i).card * k = Fintype.card α := by
  set F := univ.filter fun S : {S : Finset α // S.card = k} => c S = i with hF
  have h1 : ∑ S ∈ F, S.1.card = F.card * k := sum_const_nat (fun S _ => S.2)
  have h2 : ∑ S ∈ F, S.1.card = ∑ v : α, (F.filter fun S => v ∈ S.1).card := by
    calc ∑ S ∈ F, S.1.card = ∑ S ∈ F, ∑ v : α, if v ∈ S.1 then 1 else 0 :=
          sum_congr rfl fun S _ => by rw [sum_boole]; simp
      _ = ∑ v : α, ∑ S ∈ F, if v ∈ S.1 then 1 else 0 := sum_comm
      _ = ∑ v : α, (F.filter fun S => v ∈ S.1).card :=
          sum_congr rfl fun v _ => by rw [sum_boole]; simp
  have h3 : ∀ v : α, (F.filter fun S => v ∈ S.1).card = 1 := by
    intro v
    obtain ⟨U, hU, hu⟩ := hc i v
    refine card_eq_one.2 ⟨U, ?_⟩
    ext S
    simp only [hF, mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun h => hu S h, fun h => h ▸ hU⟩
  rw [← h1, h2, sum_congr rfl fun v _ => h3 v]
  simp

/-- In a factorisation, each colour class has exactly `|α| / k` blocks. -/
theorem class_card [Fintype α] [DecidableEq α] {k M : ℕ} (hk : 0 < k)
    {c : {S : Finset α // S.card = k} → Fin M}
    (hc : ∀ i (v : α), ∃! S : {S : Finset α // S.card = k}, c S = i ∧ v ∈ S.1) (i : Fin M) :
    (univ.filter fun S => c S = i).card = Fintype.card α / k :=
  (Nat.div_eq_of_eq_mul_left hk (class_card_mul hc i).symm).symm

/-- The number of colours in Baranyai's theorem is `C(n, k) / (n / k)`. -/
theorem num_classes {n k : ℕ} (hk : 0 < k) (hn : 0 < n) (hkn : k ∣ n) :
    (n - 1).choose (k - 1) = n.choose k / (n / k) := by
  have h := choose_mul hk hn
  obtain ⟨m, rfl⟩ := hkn
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  rw [Nat.mul_div_cancel_left m hk]
  refine (Nat.div_eq_of_eq_mul_left hm ?_).symm
  apply Nat.eq_of_mul_eq_mul_left hk
  linarith

/-- Baranyai's theorem as a partition statement, for any finite vertex type of size `n`. -/
theorem baranyai_partition [Fintype α] [DecidableEq α] (n k : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hkn : k ∣ n) (hα : Fintype.card α = n) :
    ∃ c : {S : Finset α // S.card = k} → Fin ((n - 1).choose (k - 1)),
      (∀ i (v : α), ∃! S : {S : Finset α // S.card = k}, c S = i ∧ v ∈ S.1) ∧
      (∀ S T, S ≠ T → c S = c T → Disjoint S.1 T.1) ∧
      (∀ i j, i ≠ j →
        Disjoint (univ.filter fun S => c S = i) (univ.filter fun S => c S = j)) ∧
      univ.biUnion (fun i => univ.filter fun S => c S = i) = univ ∧
      (∀ i, (univ.filter fun S => c S = i).card = n / k) ∧
      (n - 1).choose (k - 1) = n.choose k / (n / k) := by
  obtain ⟨c, hc⟩ := baranyai_of_card n k hk hkn hα
  refine ⟨c, hc, fun S T hST h => block_disjoint hc hST h, fun i j hij => class_disjoint c hij,
    classes_cover c, fun i => ?_, num_classes hk hn hkn⟩
  rw [class_card hk hc i, hα]

/-- Converse: if some colour class of a colouring of the `k`-subsets of `α` covers every vertex
exactly once, then `k ∣ |α|`. So `k ∣ n` is necessary in `baranyai` (when there is a colour). -/
theorem dvd_card_of_factorisation [Fintype α] [DecidableEq α] {k M : ℕ}
    {c : {S : Finset α // S.card = k} → Fin M}
    (hc : ∃ i, ∀ v : α, ∃! S : {S : Finset α // S.card = k}, c S = i ∧ v ∈ S.1) :
    k ∣ Fintype.card α := by
  obtain ⟨i, hi⟩ := hc
  set F := univ.filter fun S : {S : Finset α // S.card = k} => c S = i with hF
  have h1 : ∑ S ∈ F, S.1.card = F.card * k := sum_const_nat (fun S _ => S.2)
  have h2 : ∑ S ∈ F, S.1.card = ∑ v : α, (F.filter fun S => v ∈ S.1).card := by
    calc ∑ S ∈ F, S.1.card = ∑ S ∈ F, ∑ v : α, if v ∈ S.1 then 1 else 0 :=
          sum_congr rfl fun S _ => by rw [sum_boole]; simp
      _ = ∑ v : α, ∑ S ∈ F, if v ∈ S.1 then 1 else 0 := sum_comm
      _ = ∑ v : α, (F.filter fun S => v ∈ S.1).card :=
          sum_congr rfl fun v _ => by rw [sum_boole]; simp
  have h3 : ∀ v : α, (F.filter fun S => v ∈ S.1).card = 1 := by
    intro v
    obtain ⟨U, hU, hu⟩ := hi v
    refine card_eq_one.2 ⟨U, ?_⟩
    ext S
    simp only [hF, mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun h => hu S h, fun h => h ▸ hU⟩
  refine ⟨F.card, ?_⟩
  rw [mul_comm, ← h1, h2, sum_congr rfl fun v _ => h3 v]
  simp

end Baranyai

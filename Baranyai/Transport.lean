import Baranyai.Basic

/-!
# Transport of Baranyai's theorem to an arbitrary finite vertex type

A factorisation of the `k`-subsets of `α` transports along any bijection `α ≃ β`; hence
Baranyai's theorem holds for every finite type of cardinality `n` (for a `Finset` `s`, take `↥s`).
-/

open Finset

namespace Baranyai

variable {α β : Type*}

/-- A factorisation of the `k`-subsets transports along a bijection of vertex types. -/
theorem factorisation_congr (e : α ≃ β) {k M : ℕ}
    (h : ∃ c : {S : Finset α // S.card = k} → Fin M,
      ∀ i (v : α), ∃! S : {S : Finset α // S.card = k}, c S = i ∧ v ∈ S.1) :
    ∃ c : {S : Finset β // S.card = k} → Fin M,
      ∀ i (w : β), ∃! T : {T : Finset β // T.card = k}, c T = i ∧ w ∈ T.1 := by
  obtain ⟨c, hc⟩ := h
  set f : Finset α ≃ Finset β := e.finsetCongr with hf
  have hcard : ∀ s, (f s).card = s.card := fun s => by simp [hf, Equiv.finsetCongr_apply]
  have hmem : ∀ s (w : β), w ∈ f s ↔ e.symm w ∈ s := fun s w => by
    simp [hf, Equiv.finsetCongr_apply, mem_map_equiv]
  have hcs : ∀ T : {T : Finset β // T.card = k}, (f.symm T.1).card = k := fun T => by
    rw [← hcard, f.apply_symm_apply]; exact T.2
  refine ⟨fun T => c ⟨f.symm T.1, hcs T⟩, fun i w => ?_⟩
  obtain ⟨S, ⟨hSi, hSv⟩, hu⟩ := hc i (e.symm w)
  have hfS : (f S.1).card = k := by rw [hcard]; exact S.2
  refine ⟨⟨f S.1, hfS⟩, ⟨?_, (hmem _ _).2 hSv⟩, ?_⟩
  · rw [← hSi]; exact congrArg c (Subtype.ext (f.symm_apply_apply _))
  · rintro T ⟨h1, h2⟩
    have h2' : e.symm w ∈ f.symm T.1 := by
      rw [← hmem, f.apply_symm_apply]; exact h2
    have := hu ⟨f.symm T.1, hcs T⟩ ⟨h1, h2'⟩
    apply Subtype.ext
    change T.1 = f S.1
    rw [← this, f.apply_symm_apply]

/-- **Baranyai's theorem** for an arbitrary finite vertex type of cardinality `n`. -/
theorem baranyai_of_card [Fintype α] (n k : ℕ) (hk : 0 < k) (hkn : k ∣ n)
    (hα : Fintype.card α = n) :
    ∃ c : {S : Finset α // S.card = k} → Fin ((n - 1).choose (k - 1)),
      ∀ i (v : α), ∃! S : {S : Finset α // S.card = k}, c S = i ∧ v ∈ S.1 :=
  factorisation_congr (Fintype.equivFinOfCardEq hα).symm (baranyai n k hk hkn)

/-- **Baranyai's theorem** for the vertex set `s` of a `Finset`, as subsets of `s`. -/
theorem baranyai_finset {γ : Type*} (s : Finset γ) (k : ℕ) (hk : 0 < k)
    (hks : k ∣ s.card) :
    ∃ c : {S : Finset s // S.card = k} → Fin ((s.card - 1).choose (k - 1)),
      ∀ i (v : s), ∃! S : {S : Finset s // S.card = k}, c S = i ∧ v ∈ S.1 :=
  baranyai_of_card s.card k hk hks (Fintype.card_coe s)

end Baranyai

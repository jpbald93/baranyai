import Mathlib

/-!
# Baranyai's theorem

If `k ∣ n` (and `0 < k`), the complete `k`-uniform hypergraph on `Fin n` can be partitioned into
perfect matchings: there is a colouring of the `k`-subsets of `Fin n` with `C(n-1, k-1)`
colours such that every colour class is a partition of `Fin n`.

Proof: Baranyai's vertex-by-vertex induction. At stage `j` we keep `M` "classes", each consisting
of `m = n / k` slots (subsets of `{0,…,j-1}`, possibly empty) partitioning `{0,…,j-1}`, such that
each set `S` with `|S| ≤ k` occurs in exactly `C(n-j, k-|S|)` slots. To add vertex `j`, every class
chooses one slot to receive `j`, with set `S` chosen exactly `C(n-j-1, k-|S|-1)` times. The integral
choice comes from Hall's marriage theorem (Mathlib); Hall's condition follows from the fractional
choice with weights `(k-|S|)/(n-j)` by double counting. So max-flow integrality is not needed.
-/

open Finset

namespace Baranyai

variable {n k m M : ℕ}

/-- The invariant at stage `j`: classes `i : Fin M`, slots `p : Fin m`. -/
structure Inv (n k m M j : ℕ) (A : Fin M → Fin m → Finset (Fin n)) : Prop where
  disj : ∀ i p q, p ≠ q → Disjoint (A i p) (A i q)
  cover : ∀ i (v : Fin n), (∃ p, v ∈ A i p) ↔ v.val < j
  size : ∀ i p, (A i p).card ≤ k
  cnt : ∀ S : Finset (Fin n), (∀ v ∈ S, v.val < j) → S.card ≤ k →
    (univ.filter (fun x : Fin M × Fin m => A x.1 x.2 = S)).card = (n - j).choose (k - S.card)

/-- How many classes must add vertex `j` to a slot equal to `S`. -/
def dem (n k j : ℕ) (S : Finset (Fin n)) : ℕ :=
  if S.card < k then (n - j - 1).choose (k - S.card - 1) else 0

lemma choose_key (N t : ℕ) : (t + 1) * (N + 1).choose (t + 1) = (N + 1) * N.choose t := by
  have := Nat.add_one_mul_choose_eq N t
  linarith

lemma weight_eq {j : ℕ} (hj : j < n) (S : Finset (Fin n)) :
    (k - S.card) * (n - j).choose (k - S.card) = (n - j) * dem n k j S := by
  unfold dem
  split_ifs with h
  · obtain ⟨N, hN⟩ : ∃ N, n - j = N + 1 := ⟨n - j - 1, by omega⟩
    obtain ⟨t, ht⟩ : ∃ t, k - S.card = t + 1 := ⟨k - S.card - 1, by omega⟩
    have h1 : n - j - 1 = N := by omega
    have h2 : k - S.card - 1 = t := by omega
    rw [h1, h2, hN, ht, choose_key]
  · have : k - S.card = 0 := by omega
    simp [this]

lemma pascal_dem {j : ℕ} (hj : j < n) (S : Finset (Fin n)) (hS : S.card ≤ k) :
    (n - j).choose (k - S.card) = dem n k j S + (n - j - 1).choose (k - S.card) := by
  unfold dem
  split_ifs with h
  · obtain ⟨N, hN⟩ : ∃ N, n - j = N + 1 := ⟨n - j - 1, by omega⟩
    obtain ⟨t, ht⟩ : ∃ t, k - S.card = t + 1 := ⟨k - S.card - 1, by omega⟩
    have h1 : n - j - 1 = N := by omega
    have h2 : k - S.card - 1 = t := by omega
    rw [h1, h2, hN, ht, Nat.choose_succ_succ']
  · have : k - S.card = 0 := by omega
    simp [this]

lemma choose_mul (hk : 0 < k) (hn : 0 < n) : n * (n - 1).choose (k - 1) = n.choose k * k := by
  have key := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
  have e1 : n - 1 + 1 = n := by omega
  have e2 : k - 1 + 1 = k := by omega
  rw [e1, e2] at key
  exact key

lemma row_card_sum {j : ℕ} {A : Fin M → Fin m → Finset (Fin n)} (hI : Inv n k m M j A)
    (hj : j ≤ n) (i : Fin M) : ∑ p, (A i p).card = j := by
  have hU : univ.biUnion (A i) = univ.filter (fun v : Fin n => v.val < j) := by
    ext v; simp [← hI.cover i v]
  have := card_biUnion (s := univ) (t := A i) (fun p _ q _ hpq => hI.disj i p q hpq)
  rw [← this, hU, Fin.card_filter_val_lt]; omega

lemma row_weight_sum {j : ℕ} {A : Fin M → Fin m → Finset (Fin n)} (hI : Inv n k m M j A)
    (hj : j ≤ n) (hm : n = m * k) (i : Fin M) : ∑ p, (k - (A i p).card) = n - j := by
  have h2 : ∑ _p : Fin m, k = n := by rw [hm]; simp
  rw [sum_tsub_distrib _ (fun p _ => hI.size i p), row_card_sum hI hj i, h2]

/-- Double counting: weighted number of slots whose set lies in `Y`. -/
lemma weighted_count {j : ℕ} {A : Fin M → Fin m → Finset (Fin n)} (hI : Inv n k m M j A)
    (hj : j < n) (Y : Finset (Finset (Fin n)))
    (hY : ∀ S ∈ Y, (∀ v ∈ S, v.val < j) ∧ S.card ≤ k) :
    ∑ x ∈ univ.filter (fun x : Fin M × Fin m => A x.1 x.2 ∈ Y), (k - (A x.1 x.2).card)
      = (n - j) * ∑ S ∈ Y, dem n k j S := by
  rw [← sum_fiberwise_of_maps_to (s := univ.filter (fun x : Fin M × Fin m => A x.1 x.2 ∈ Y))
    (g := fun x : Fin M × Fin m => A x.1 x.2) (t := Y) (fun x hx => (mem_filter.1 hx).2), mul_sum]
  refine sum_congr rfl (fun S hS => ?_)
  have h2 : ((univ.filter (fun x : Fin M × Fin m => A x.1 x.2 ∈ Y)).filter
      (fun x => A x.1 x.2 = S)).card = (n - j).choose (k - S.card) := by
    rw [← hI.cnt S (hY S hS).1 (hY S hS).2]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by rw [h]; exact hS, h⟩
  rw [sum_const_nat (m := k - S.card)
    (fun x hx => by rw [mem_filter] at hx; exact congrArg (fun T => k - T.card) hx.2), h2,
    mul_comm, weight_eq hj]

/-- One induction step: add vertex `j`. -/
lemma step {j : ℕ} {A : Fin M → Fin m → Finset (Fin n)} (hI : Inv n k m M j A) (hj : j < n)
    (hm : n = m * k) : ∃ A' : Fin M → Fin m → Finset (Fin n), Inv n k m M (j + 1) A' := by
  let t : Fin M → Finset ((_ : Finset (Fin n)) × ℕ) :=
    fun i => (univ.image (A i)).sigma (fun S => range (dem n k j S))
  have hall : ∀ X : Finset (Fin M), X.card ≤ (X.biUnion t).card := by
    intro X
    obtain ⟨Y, hYdef⟩ : ∃ Y, Y = X.biUnion (fun i => univ.image (A i)) := ⟨_, rfl⟩
    have hXY : X.biUnion t = Y.sigma (fun S => range (dem n k j S)) := by
      ext ⟨S, r⟩
      simp only [t, hYdef, mem_biUnion, mem_sigma, mem_image, mem_univ, true_and, mem_range]
      constructor
      · rintro ⟨i, hi, ⟨p, hp⟩, hr⟩; exact ⟨⟨i, hi, p, hp⟩, hr⟩
      · rintro ⟨⟨i, hi, p, hp⟩, hr⟩; exact ⟨i, hi, ⟨p, hp⟩, hr⟩
    rw [hXY, card_sigma]
    simp only [card_range]
    have hY : ∀ S ∈ Y, (∀ v ∈ S, v.val < j) ∧ S.card ≤ k := by
      intro S hS
      rw [hYdef, mem_biUnion] at hS
      obtain ⟨i, -, hS⟩ := hS
      obtain ⟨p, -, rfl⟩ := mem_image.1 hS
      exact ⟨fun v hv => (hI.cover i v).1 ⟨p, hv⟩, hI.size i p⟩
    have key := weighted_count hI hj Y hY
    have hle : (n - j) * X.card ≤ (n - j) * ∑ S ∈ Y, dem n k j S := by
      rw [← key]
      calc (n - j) * X.card = ∑ i ∈ X, ∑ p, (k - (A i p).card) := by
            rw [sum_congr rfl (fun i _ => row_weight_sum hI hj.le hm i), sum_const, smul_eq_mul,
              mul_comm]
        _ = ∑ x ∈ X ×ˢ univ, (k - (A x.1 x.2).card) := by rw [sum_product]
        _ ≤ _ := by
            apply sum_le_sum_of_subset
            intro x hx
            rw [mem_product] at hx
            rw [mem_filter, hYdef, mem_biUnion]
            exact ⟨mem_univ _, x.1, hx.1, mem_image.2 ⟨x.2, mem_univ _, rfl⟩⟩
    exact Nat.le_of_mul_le_mul_left hle (by omega)
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hf1 : ∀ i, ∃ p, A i p = (f i).1 := fun i => by
    have := hft i
    simp only [t, mem_sigma, mem_image, mem_univ, true_and] at this
    exact this.1
  have hf2 : ∀ i, ((f i).2 : ℕ) < dem n k j (f i).1 := fun i => by
    have := hft i
    simp only [t, mem_sigma, mem_range] at this
    exact this.2
  choose p hp using hf1
  have hpick_le : ∀ S, (univ.filter (fun i => A i (p i) = S)).card ≤ dem n k j S := by
    intro S
    have := card_le_card_of_injOn (fun i => ((f i).2 : ℕ))
      (s := univ.filter (fun i => A i (p i) = S)) (t := range (dem n k j S)) ?_ ?_
    · simpa using this
    · intro i hi
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hi
      simp only [mem_coe, mem_range]
      have := hf2 i
      rw [← hp i, hi] at this
      exact this
    · intro i hi i' hi' h
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hi hi'
      apply hfinj
      apply Sigma.ext
      · rw [← hp i, ← hp i', hi, hi']
      · exact heq_of_eq h
  obtain ⟨U, hU⟩ : ∃ U : Finset (Finset (Fin n)),
      U = univ.filter (fun S => (∀ v ∈ S, v.val < j) ∧ S.card ≤ k) := ⟨_, rfl⟩
  have hUmem : ∀ i q, A i q ∈ U := fun i q => by
    rw [hU, mem_filter]
    exact ⟨mem_univ _, fun v hv => (hI.cover i v).1 ⟨q, hv⟩, hI.size i q⟩
  have hsum_pick : ∑ S ∈ U, (univ.filter (fun i => A i (p i) = S)).card = M := by
    have h := card_eq_sum_card_fiberwise (s := univ) (t := U) (f := fun i => A i (p i))
      (fun i _ => mem_coe.2 (hUmem i (p i)))
    simp only [card_univ, Fintype.card_fin] at h
    exact h.symm
  have hsum_d : ∑ S ∈ U, dem n k j S = M := by
    have key := weighted_count hI hj U (fun S hS => by rw [hU, mem_filter] at hS; exact hS.2)
    have hfull : univ.filter (fun x : Fin M × Fin m => A x.1 x.2 ∈ U) = univ := by
      ext x; simp only [mem_filter, mem_univ, true_and, iff_true]; exact hUmem x.1 x.2
    have hall_sum : ∑ x ∈ univ.filter (fun x : Fin M × Fin m => A x.1 x.2 ∈ U),
        (k - (A x.1 x.2).card) = M * (n - j) := by
      rw [hfull, Fintype.sum_prod_type]
      simp only [row_weight_sum hI hj.le hm, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    have : (n - j) * ∑ S ∈ U, dem n k j S = (n - j) * M := by rw [← key, hall_sum, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have hpick : ∀ S ∈ U, (univ.filter (fun i => A i (p i) = S)).card = dem n k j S :=
    (sum_eq_sum_iff_of_le (fun S _ => hpick_le S)).1 (hsum_pick.trans hsum_d.symm)
  have hpsize : ∀ i, (A i (p i)).card < k := fun i => by
    have h := hf2 i
    rw [← hp i] at h
    by_contra hc
    simp only [dem, if_neg hc] at h
    omega
  obtain ⟨jv, hjvdef⟩ : ∃ jv : Fin n, jv.val = j := ⟨⟨j, hj⟩, rfl⟩
  have hjv : ∀ i q, jv ∉ A i q := fun i q h => by
    have := (hI.cover i jv).1 ⟨q, h⟩
    omega
  obtain ⟨A', hA'⟩ : ∃ A' : Fin M → Fin m → Finset (Fin n),
      ∀ i q, A' i q = if q = p i then insert jv (A i q) else A i q := ⟨_, fun _ _ => rfl⟩
  have hinj : Function.Injective (fun i : Fin M => (i, p i)) := fun a b h => (Prod.mk.inj h).1
  refine ⟨A', ⟨?_, ?_, ?_, ?_⟩⟩
  · intro i q q' hqq'
    rw [hA', hA']
    split_ifs with h1 h2 h2
    · exact absurd (h1.trans h2.symm) hqq'
    · rw [disjoint_insert_left]; exact ⟨hjv i q', hI.disj i q q' hqq'⟩
    · rw [disjoint_insert_right]; exact ⟨hjv i q, hI.disj i q q' hqq'⟩
    · exact hI.disj i q q' hqq'
  · intro i v
    constructor
    · rintro ⟨q, hq⟩
      rw [hA'] at hq
      split_ifs at hq with h1
      · rcases mem_insert.1 hq with rfl | hq
        · omega
        · have := (hI.cover i v).1 ⟨q, hq⟩; omega
      · have := (hI.cover i v).1 ⟨q, hq⟩; omega
    · intro hv
      by_cases hvj : v.val < j
      · obtain ⟨q, hq⟩ := (hI.cover i v).2 hvj
        refine ⟨q, ?_⟩
        rw [hA']
        split_ifs
        · exact mem_insert_of_mem hq
        · exact hq
      · have hveq : v = jv := Fin.ext (by omega)
        refine ⟨p i, ?_⟩
        rw [hA', if_pos rfl, hveq]
        exact mem_insert_self _ _
  · intro i q
    rw [hA']
    split_ifs with h
    · subst h
      exact (card_insert_le _ _).trans (by have := hpsize i; omega)
    · exact hI.size i q
  · intro S hS hSk
    by_cases hjS : jv ∈ S
    · obtain ⟨T, hT⟩ : ∃ T, T = S.erase jv := ⟨_, rfl⟩
      have hTj : ∀ v ∈ T, v.val < j := by
        intro v hv
        rw [hT, mem_erase] at hv
        have h1 := hS v hv.2
        have h2 : v.val ≠ j := fun h => hv.1 (Fin.ext (by omega))
        omega
      have hTcard : T.card + 1 = S.card := by rw [hT]; exact card_erase_add_one hjS
      have hTU : T ∈ U := by rw [hU, mem_filter]; exact ⟨mem_univ _, hTj, by omega⟩
      have hset : univ.filter (fun x : Fin M × Fin m => A' x.1 x.2 = S)
          = (univ.filter (fun i => A i (p i) = T)).image (fun i => (i, p i)) := by
        ext ⟨i, q⟩
        simp only [mem_filter, mem_univ, true_and, mem_image,
          Prod.mk.injEq, hA']
        constructor
        · intro h
          split_ifs at h with hq
          · subst hq
            refine ⟨i, ?_, rfl, rfl⟩
            rw [hT, ← h, erase_insert (hjv i _)]
          · exact absurd (by rw [h]; exact hjS) (hjv i q)
        · rintro ⟨i', hi', rfl, rfl⟩
          rw [if_pos rfl, hi', hT, insert_erase hjS]
      rw [hset, card_image_of_injective _ hinj, hpick T hTU]
      unfold dem
      rw [if_pos (by omega)]
      congr 1; omega
    · have hSj : ∀ v ∈ S, v.val < j := by
        intro v hv
        have h1 := hS v hv
        have h2 : v.val ≠ j := fun h => hjS (by rwa [show jv = v from Fin.ext (by omega)])
        omega
      have hSU : S ∈ U := by rw [hU, mem_filter]; exact ⟨mem_univ _, hSj, hSk⟩
      have hsplit : univ.filter (fun x : Fin M × Fin m => A x.1 x.2 = S)
          = univ.filter (fun x : Fin M × Fin m => A' x.1 x.2 = S)
            ∪ (univ.filter (fun i => A i (p i) = S)).image (fun i => (i, p i)) := by
        ext ⟨i, q⟩
        simp only [mem_union, mem_filter, mem_univ, true_and, mem_image,
          Prod.mk.injEq, hA']
        constructor
        · intro h
          by_cases hq : q = p i
          · right; exact ⟨i, by rw [← hq]; exact h, rfl, hq.symm⟩
          · left; rw [if_neg hq]; exact h
        · rintro (h | ⟨i', hi', rfl, rfl⟩)
          · split_ifs at h with hq
            · exact absurd (by rw [← h]; exact mem_insert_self jv _) hjS
            · exact h
          · exact hi'
      have hdisj : Disjoint (univ.filter (fun x : Fin M × Fin m => A' x.1 x.2 = S))
          ((univ.filter (fun i => A i (p i) = S)).image (fun i => (i, p i))) := by
        rw [disjoint_left]
        rintro ⟨i, q⟩ h1 h2
        simp only [mem_filter, mem_univ, true_and, mem_image,
          Prod.mk.injEq, hA'] at h1 h2
        obtain ⟨i', hi', rfl, rfl⟩ := h2
        rw [if_pos rfl] at h1
        exact hjS (by rw [← h1]; exact mem_insert_self jv _)
      have hc := hI.cnt S hSj hSk
      rw [hsplit, card_union_of_disjoint hdisj, card_image_of_injective _ hinj, hpick S hSU, pascal_dem hj S hSk] at hc
      rw [show n - (j + 1) = n - j - 1 by omega]
      omega

/-- Stage 0: all slots empty. -/
lemma init (hk : 0 < k) (hm : n = m * k) :
    Inv n k m ((n - 1).choose (k - 1)) 0 (fun _ _ => ∅) := by
  have hcomb : (n - 1).choose (k - 1) * m = n.choose k := by
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · have hm0 : m = 0 := by
        rcases Nat.eq_zero_or_pos m with h | h
        · exact h
        · have : 0 < m * k := Nat.mul_pos h hk
          omega
      rw [hm0, h0, Nat.choose_eq_zero_of_lt hk]; simp
    · apply Nat.eq_of_mul_eq_mul_right hk
      rw [← choose_mul hk hn, mul_assoc, ← hm, mul_comm]
  refine ⟨fun _ _ _ _ => disjoint_empty_left _, fun i v => ?_, fun _ _ => by simp, fun S hS _ => ?_⟩
  · simp
  · have hS0 : S = ∅ := eq_empty_of_forall_notMem (fun v hv => by have := hS v hv; omega)
    subst hS0
    simp only [card_empty, Nat.sub_zero]
    rw [← hcomb]
    simp

/-- From the final stage, read off the colouring. -/
theorem exists_partition_of_inv {A : Fin M → Fin m → Finset (Fin n)} (hI : Inv n k m M n A) :
    ∃ c : {S : Finset (Fin n) // S.card = k} → Fin M,
      ∀ i (v : Fin n), ∃! S : {S : Finset (Fin n) // S.card = k}, c S = i ∧ v ∈ S.1 := by
  have hcnt : ∀ S : Finset (Fin n), S.card ≤ k →
      (univ.filter (fun x : Fin M × Fin m => A x.1 x.2 = S)).card = (0 : ℕ).choose (k - S.card) := by
    intro S hS
    have := hI.cnt S (fun v _ => v.isLt) hS
    rwa [Nat.sub_self] at this
  have hslot_k : ∀ i q, (A i q).card = k := by
    intro i q
    have h1 := hcnt (A i q) (hI.size i q)
    have h2 : 0 < (univ.filter (fun x : Fin M × Fin m => A x.1 x.2 = A i q)).card :=
      card_pos.2 ⟨(i, q), by simp⟩
    have h3 : k - (A i q).card = 0 := by
      by_contra h
      rw [h1, Nat.choose_eq_zero_of_lt (by omega)] at h2
      exact lt_irrefl _ h2
    have := hI.size i q
    omega
  have hone : ∀ S : {S : Finset (Fin n) // S.card = k},
      ∃ x : Fin M × Fin m, univ.filter (fun x : Fin M × Fin m => A x.1 x.2 = S.1) = {x} := by
    intro S
    have := hcnt S.1 S.2.le
    rw [S.2, Nat.sub_self, Nat.choose_zero_right] at this
    exact card_eq_one.1 this
  choose slot hslot using hone
  have hslot_spec : ∀ S x, A x.1 x.2 = S.1 ↔ x = slot S := by
    intro S x
    have := congrArg (x ∈ ·) (hslot S)
    simpa using this
  refine ⟨fun S => (slot S).1, fun i v => ?_⟩
  obtain ⟨q, hq⟩ := (hI.cover i v).2 v.isLt
  refine ⟨⟨A i q, hslot_k i q⟩, ⟨?_, hq⟩, ?_⟩
  · have := (hslot_spec ⟨A i q, hslot_k i q⟩ (i, q)).1 rfl
    show (slot ⟨A i q, hslot_k i q⟩).1 = i
    rw [← this]
  · rintro ⟨S', hS'⟩ ⟨hc, hv⟩
    have h1 := (hslot_spec ⟨S', hS'⟩ (slot ⟨S', hS'⟩)).2 rfl
    change (slot ⟨S', hS'⟩).1 = i at hc
    change v ∈ S' at hv
    rw [hc] at h1
    have hqq : (slot ⟨S', hS'⟩).2 = q := by
      by_contra hne
      exact disjoint_left.1 (hI.disj i _ _ hne) (by rw [h1]; exact hv) hq
    apply Subtype.ext
    show S' = A i q
    rw [← hqq]
    exact h1.symm

theorem exists_final (hk : 0 < k) (hm : n = m * k) :
    ∃ A : Fin ((n - 1).choose (k - 1)) → Fin m → Finset (Fin n),
      Inv n k m ((n - 1).choose (k - 1)) n A := by
  have : ∀ j ≤ n, ∃ A : Fin ((n - 1).choose (k - 1)) → Fin m → Finset (Fin n),
      Inv n k m ((n - 1).choose (k - 1)) j A := by
    intro j
    induction j with
    | zero => intro _; exact ⟨_, init hk hm⟩
    | succ j ih =>
      intro hj
      obtain ⟨A, hA⟩ := ih (by omega)
      exact step hA (by omega) hm
  exact this n le_rfl

end Baranyai

open Baranyai

/-- **Baranyai's theorem.** If `0 < k` and `k ∣ n`, the `k`-subsets of `Fin n` can be coloured
with `C(n-1, k-1)` colours so that each colour class is a partition of `Fin n` (a perfect
matching of the complete `k`-uniform hypergraph): every vertex lies in exactly one block of each
colour. -/
theorem baranyai (n k : ℕ) (hk : 0 < k) (hkn : k ∣ n) :
    ∃ c : {S : Finset (Fin n) // S.card = k} → Fin ((n - 1).choose (k - 1)),
      ∀ i (v : Fin n), ∃! S : {S : Finset (Fin n) // S.card = k}, c S = i ∧ v ∈ S.1 := by
  obtain ⟨m, hm⟩ := hkn
  obtain ⟨A, hA⟩ := exists_final (n := n) (k := k) (m := m) hk (by rw [hm, mul_comm])
  exact exists_partition_of_inv hA

/-- Baranyai's theorem with the number of colours written as `C(n,k)·k/n`. -/
theorem baranyai' (n k : ℕ) (hk : 0 < k) (hn : 0 < n) (hkn : k ∣ n) :
    ∃ c : {S : Finset (Fin n) // S.card = k} → Fin (n.choose k * k / n),
      ∀ i (v : Fin n), ∃! S : {S : Finset (Fin n) // S.card = k}, c S = i ∧ v ∈ S.1 := by
  have e : (n - 1).choose (k - 1) = n.choose k * k / n := by
    rw [← choose_mul hk hn, Nat.mul_div_cancel_left _ hn]
  obtain ⟨c, hc⟩ := baranyai n k hk hkn
  refine ⟨fun S => Fin.cast e (c S), fun i v => ?_⟩
  obtain ⟨S, hS, huniq⟩ := hc (Fin.cast e.symm i) v
  refine ⟨S, ⟨?_, hS.2⟩, fun S' hS' => huniq S' ⟨?_, hS'.2⟩⟩
  · apply Fin.ext; simp [hS.1]
  · apply Fin.ext
    have := congrArg Fin.val hS'.1
    simpa using this

/-- The case `k = 2`: a 1-factorisation of the complete graph `K_n`, `n` even. -/
theorem complete_graph_one_factorisation (n : ℕ) (hn : Even n) :
    ∃ c : {S : Finset (Fin n) // S.card = 2} → Fin (n - 1),
      ∀ i (v : Fin n), ∃! S : {S : Finset (Fin n) // S.card = 2}, c S = i ∧ v ∈ S.1 := by
  have h := baranyai n 2 (by norm_num) (even_iff_two_dvd.1 hn)
  have e : (n - 1).choose (2 - 1) = n - 1 := by simp
  rw [e] at h
  exact h

/-- Non-vacuity example: `K_4` splits into `3` perfect matchings. -/
theorem baranyai_four_two :
    ∃ c : {S : Finset (Fin 4) // S.card = 2} → Fin 3,
      ∀ i (v : Fin 4), ∃! S : {S : Finset (Fin 4) // S.card = 2}, c S = i ∧ v ∈ S.1 :=
  complete_graph_one_factorisation 4 (by decide)

import Baranyai.Partition

/-!
# Layer 14: Mathlib-only restatements of the main theorems, with witnesses

Every `l14_*` theorem below has a type that mentions only Mathlib notions (`Finpartition`,
`Finset.powersetCard`, `SimpleGraph.Subgraph.IsPerfectMatching`, ...), and is proved from the
corresponding library theorem. Every `l14w_*` theorem instantiates the hypotheses on an explicit
small configuration and shows that the objects in the conclusion are non-degenerate.
-/

open Finset

variable {α : Type*}

/-- Bridge: a factorising colouring gives an injective family of partitions of the vertex set
into `k`-blocks, each `k`-subset lying in exactly one of them. -/
private lemma l14_classes [Fintype α] [DecidableEq α] {n k M : ℕ} (hk : 0 < k)
    (hα : Fintype.card α = n) (hM : n = 0 → M ≤ 1)
    {c : {S : Finset α // S.card = k} → Fin M}
    (hc : ∀ i (v : α), ∃! S : {S : Finset α // S.card = k}, c S = i ∧ v ∈ S.1) :
    ∃ P : Fin M → Finpartition (univ : Finset α), Function.Injective P ∧
      (∀ i, ∀ t ∈ (P i).parts, t.card = k) ∧
      (∀ t : Finset α, t.card = k → ∃! i, t ∈ (P i).parts) ∧
      (∀ i, (P i).parts.card * k = n) := by
  classical
  let cls : Fin M → Finset (Finset α) := fun i =>
    (univ.filter fun S => c S = i).map (Function.Embedding.subtype _)
  have hmem : ∀ i T, T ∈ cls i ↔ ∃ h : T.card = k, c ⟨T, h⟩ = i := by
    intro i T; simp [cls]
  let P : Fin M → Finpartition (univ : Finset α) := fun i =>
    Finpartition.ofExistsUnique (cls i) (fun _ _ => subset_univ _)
      (by
        intro a _
        obtain ⟨S, ⟨hS, haS⟩, hu⟩ := hc i a
        refine ⟨S.1, ⟨(hmem i _).2 ⟨S.2, hS⟩, haS⟩, ?_⟩
        rintro T ⟨hT, haT⟩
        obtain ⟨h, hcT⟩ := (hmem i T).1 hT
        exact congrArg Subtype.val (hu ⟨T, h⟩ ⟨hcT, haT⟩))
      (by
        intro h
        obtain ⟨h0, -⟩ := (hmem i ∅).1 h
        simp at h0; omega)
  have hP : ∀ i, (P i).parts = cls i := fun i => rfl
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rcases isEmpty_or_nonempty α with hα0 | ⟨⟨v⟩⟩
    · have h1 := hM (by rw [← hα]; exact Fintype.card_eq_zero)
      exact Fin.ext (by have := i.2; have := j.2; omega)
    · obtain ⟨S, ⟨hS, -⟩, -⟩ := hc i v
      have h1 : S.1 ∈ (P i).parts := (hmem i _).2 ⟨S.2, hS⟩
      rw [hij, hP] at h1
      obtain ⟨_, h2⟩ := (hmem j _).1 h1
      exact hS.symm.trans h2
  · intro i t ht
    exact ((hmem i t).1 ht).1
  · intro t ht
    refine ⟨c ⟨t, ht⟩, (hmem _ _).2 ⟨ht, rfl⟩, fun j hj => ?_⟩
    obtain ⟨_, hj⟩ := (hmem j t).1 hj
    exact hj.symm
  · intro i
    rw [hP, ← hα, ← Baranyai.class_card_mul hc i]
    simp [cls]

private lemma l14_choose_le {n k : ℕ} (h : n = 0) : (n - 1).choose (k - 1) ≤ 1 := by
  subst h; rcases Nat.eq_zero_or_pos (k - 1) with h | h
  · rw [h]; simp
  · rw [Nat.zero_sub, Nat.choose_eq_zero_of_lt h]; omega

/-- **Baranyai** (Mathlib-only form of `baranyai`): for `0 < k ∣ n` there is an injective family
of `C(n-1,k-1)` partitions of `Fin n` into `k`-blocks (so each has `n/k` blocks) such that every
`k`-subset of `Fin n` is a block of exactly one of them. -/
theorem l14_baranyai (n k : ℕ) (hk : 0 < k) (hkn : k ∣ n) :
    ∃ P : Fin ((n - 1).choose (k - 1)) → Finpartition (univ : Finset (Fin n)),
      Function.Injective P ∧ (∀ i, ∀ t ∈ (P i).parts, t.card = k) ∧
      (∀ t : Finset (Fin n), t.card = k → ∃! i, t ∈ (P i).parts) ∧
      (∀ i, (P i).parts.card * k = n) := by
  obtain ⟨c, hc⟩ := baranyai n k hk hkn
  exact l14_classes hk (Fintype.card_fin n) l14_choose_le hc

/-- Mathlib-only form of `baranyai'` (number of classes written as `C(n,k)·k/n`). -/
theorem l14_baranyai' (n k : ℕ) (hk : 0 < k) (hn : 0 < n) (hkn : k ∣ n) :
    ∃ P : Fin (n.choose k * k / n) → Finpartition (univ : Finset (Fin n)),
      Function.Injective P ∧ (∀ i, ∀ t ∈ (P i).parts, t.card = k) ∧
      (∀ t : Finset (Fin n), t.card = k → ∃! i, t ∈ (P i).parts) ∧
      (∀ i, (P i).parts.card * k = n) := by
  obtain ⟨c, hc⟩ := baranyai' n k hk hn hkn
  exact l14_classes hk (Fintype.card_fin n) (by omega) hc

/-- Mathlib-only form of `Baranyai.baranyai_of_card`: the same for any finite vertex type. -/
theorem l14_baranyai_of_card [Fintype α] [DecidableEq α] (n k : ℕ) (hk : 0 < k) (hkn : k ∣ n)
    (hα : Fintype.card α = n) :
    ∃ P : Fin ((n - 1).choose (k - 1)) → Finpartition (univ : Finset α),
      Function.Injective P ∧ (∀ i, ∀ t ∈ (P i).parts, t.card = k) ∧
      (∀ t : Finset α, t.card = k → ∃! i, t ∈ (P i).parts) ∧
      (∀ i, (P i).parts.card * k = n) := by
  obtain ⟨c, hc⟩ := Baranyai.baranyai_of_card n k hk hkn hα
  exact l14_classes hk hα l14_choose_le hc

/-- Mathlib-only form of `Baranyai.baranyai_partition`: the set of all `k`-subsets of `α` has a
`Finpartition` into exactly `C(n-1,k-1)` classes, each class being a perfect matching of `α`
(every vertex lies in exactly one block) with `n / k` blocks of size `k`. -/
theorem l14_baranyai_partition [Fintype α] [DecidableEq α] (n k : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hkn : k ∣ n) (hα : Fintype.card α = n) :
    ∃ Q : Finpartition (powersetCard k (univ : Finset α)),
      Q.parts.card = (n - 1).choose (k - 1) ∧
      ∀ C ∈ Q.parts, (∀ t ∈ C, t.card = k) ∧ (∀ a : α, ∃! t, t ∈ C ∧ a ∈ t) ∧
        C.card = n / k := by
  classical
  obtain ⟨c, hc, -, -, -, hcard, -⟩ := Baranyai.baranyai_partition n k hk hn hkn hα
  let cls : Fin ((n - 1).choose (k - 1)) → Finset (Finset α) := fun i =>
    (univ.filter fun S => c S = i).map (Function.Embedding.subtype _)
  have hmem : ∀ i T, T ∈ cls i ↔ ∃ h : T.card = k, c ⟨T, h⟩ = i := by
    intro i T; simp [cls]
  have hv : Nonempty α := Fintype.card_pos_iff.1 (hα ▸ hn)
  obtain ⟨v⟩ := hv
  have hne : ∀ i, ∃ T, T ∈ cls i := fun i => by
    obtain ⟨S, ⟨hS, -⟩, -⟩ := hc i v
    exact ⟨S.1, (hmem i _).2 ⟨S.2, hS⟩⟩
  have hinj : Function.Injective cls := by
    intro i j hij
    obtain ⟨T, hT⟩ := hne i
    obtain ⟨h1, h2⟩ := (hmem i T).1 hT
    rw [hij] at hT
    obtain ⟨_, h3⟩ := (hmem j T).1 hT
    exact h2.symm.trans h3
  let Q : Finpartition (powersetCard k (univ : Finset α)) :=
    Finpartition.ofExistsUnique (univ.image cls)
      (by
        intro p hp t ht
        obtain ⟨i, -, rfl⟩ := mem_image.1 hp
        exact mem_powersetCard.2 ⟨subset_univ _, ((hmem i t).1 ht).1⟩)
      (by
        intro t ht
        have htk := (mem_powersetCard.1 ht).2
        refine ⟨cls (c ⟨t, htk⟩), ⟨mem_image_of_mem _ (mem_univ _), (hmem _ _).2 ⟨htk, rfl⟩⟩, ?_⟩
        rintro p ⟨hp, htp⟩
        obtain ⟨j, -, rfl⟩ := mem_image.1 hp
        obtain ⟨_, hj⟩ := (hmem j t).1 htp
        rw [hj])
      (by
        intro h
        obtain ⟨i, -, hi⟩ := mem_image.1 h
        obtain ⟨T, hT⟩ := hne i
        rw [hi] at hT
        exact notMem_empty T hT)
  have hQ : Q.parts = univ.image cls := rfl
  refine ⟨Q, ?_, ?_⟩
  · rw [hQ, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  · intro C hC
    rw [hQ] at hC
    obtain ⟨i, -, rfl⟩ := mem_image.1 hC
    refine ⟨fun t ht => ((hmem i t).1 ht).1, fun a => ?_, ?_⟩
    · obtain ⟨S, ⟨hS, haS⟩, hu⟩ := hc i a
      refine ⟨S.1, ⟨(hmem i _).2 ⟨S.2, hS⟩, haS⟩, ?_⟩
      rintro T ⟨hT, haT⟩
      obtain ⟨h, hcT⟩ := (hmem i T).1 hT
      exact congrArg Subtype.val (hu ⟨T, h⟩ ⟨hcT, haT⟩)
    · rw [← hcard i]; simp [cls]

/-- Bridge: a factorising colouring of the 2-subsets gives perfect matchings of the complete
graph that partition its edges. -/
private lemma l14_matchings {V : Type*} [DecidableEq V] {M : ℕ} (hM : IsEmpty V → M ≤ 1)
    {c : {S : Finset V // S.card = 2} → Fin M}
    (hc : ∀ i (v : V), ∃! S : {S : Finset V // S.card = 2}, c S = i ∧ v ∈ S.1) :
    ∃ G : Fin M → (⊤ : SimpleGraph V).Subgraph, Function.Injective G ∧
      (∀ i, (G i).IsPerfectMatching) ∧ ∀ v w : V, v ≠ w → ∃! i, (G i).Adj v w := by
  have pair : ∀ (S : Finset V) v w, S.card = 2 → v ∈ S → w ∈ S → v ≠ w → S = {v, w} :=
    fun S v w hS hv hw hvw => (eq_of_subset_of_card_le (by
      intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;>
        assumption) (by rw [hS, card_pair hvw])).symm
  let G : Fin M → (⊤ : SimpleGraph V).Subgraph := fun i =>
    { verts := Set.univ
      Adj := fun v w => v ≠ w ∧ ∃ S : {S : Finset V // S.card = 2}, c S = i ∧ v ∈ S.1 ∧ w ∈ S.1
      adj_sub := fun h => h.1
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun _ _ ⟨h, S, h1, h2, h3⟩ => ⟨h.symm, S, h1, h3, h2⟩⟩ }
  have hG : ∀ i v w, (G i).Adj v w ↔
      v ≠ w ∧ ∃ S : {S : Finset V // S.card = 2}, c S = i ∧ v ∈ S.1 ∧ w ∈ S.1 :=
    fun _ _ _ => Iff.rfl
  have hedge : ∀ v w, v ≠ w → ∃! i, (G i).Adj v w := by
    intro v w hvw
    let S : {S : Finset V // S.card = 2} := ⟨{v, w}, card_pair hvw⟩
    refine ⟨c S, (hG _ _ _).2 ⟨hvw, S, rfl, by simp [S], by simp [S]⟩, fun j hj => ?_⟩
    obtain ⟨-, S', h1, h2, h3⟩ := (hG _ _ _).1 hj
    have : S' = S := Subtype.ext (pair _ _ _ S'.2 h2 h3 hvw)
    rw [← h1, this]
  have hperf : ∀ i, (G i).IsPerfectMatching := by
    intro i
    rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    intro v
    obtain ⟨S, ⟨hS, hvS⟩, hu⟩ := hc i v
    obtain ⟨x, y, hxy, hSxy⟩ := card_eq_two.1 S.2
    have : ∃ w, w ≠ v ∧ w ∈ S.1 := by
      rw [hSxy] at hvS ⊢
      simp only [mem_insert, mem_singleton] at hvS
      rcases hvS with rfl | rfl
      · exact ⟨y, hxy.symm, by simp⟩
      · exact ⟨x, hxy, by simp⟩
    obtain ⟨w, hwv, hwS⟩ := this
    refine ⟨w, (hG _ _ _).2 ⟨hwv.symm, S, hS, hvS, hwS⟩, fun w' hw' => ?_⟩
    obtain ⟨hvw', S', h1, h2, h3⟩ := (hG _ _ _).1 hw'
    have hS' : S' = S := hu S' ⟨h1, h2⟩
    rw [hS', pair _ _ _ S.2 hvS hwS hwv.symm] at h3
    simp only [mem_insert, mem_singleton] at h3
    rcases h3 with h3 | h3
    · exact absurd h3.symm hvw'
    · exact h3
  refine ⟨G, ?_, hperf, hedge⟩
  intro i j hij
  by_cases hV : Nonempty V
  · obtain ⟨v⟩ := hV
    obtain ⟨w, hw, -⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.1 (hperf i) v
    have hw' : (G j).Adj v w := hij ▸ hw
    exact (hedge v w hw.1).unique hw hw'
  · have h1 := hM (not_nonempty_iff.1 hV)
    exact Fin.ext (by have := i.2; have := j.2; omega)

/-- Mathlib-only form of `complete_graph_one_factorisation`: for `n` even, the complete graph on
`Fin n` has `n - 1` distinct perfect matchings, and every edge lies in exactly one of them. -/
theorem l14_complete_graph_one_factorisation (n : ℕ) (hn : Even n) :
    ∃ G : Fin (n - 1) → (⊤ : SimpleGraph (Fin n)).Subgraph, Function.Injective G ∧
      (∀ i, (G i).IsPerfectMatching) ∧ ∀ v w : Fin n, v ≠ w → ∃! i, (G i).Adj v w := by
  obtain ⟨c, hc⟩ := complete_graph_one_factorisation n hn
  exact l14_matchings (fun h => by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · omega
    · exact (h.false ⟨0, h0⟩).elim) hc

/-- Mathlib-only form of `baranyai_four_two`: `K_4` has 3 distinct perfect matchings partitioning
its edges. -/
theorem l14_baranyai_four_two :
    ∃ G : Fin 3 → (⊤ : SimpleGraph (Fin 4)).Subgraph, Function.Injective G ∧
      (∀ i, (G i).IsPerfectMatching) ∧ ∀ v w : Fin 4, v ≠ w → ∃! i, (G i).Adj v w :=
  l14_complete_graph_one_factorisation 4 (by decide)

/-- Mathlib-only form of `Baranyai.baranyai_finset`: Baranyai for the elements of a `Finset`. -/
theorem l14_baranyai_finset {γ : Type*} [DecidableEq γ] (s : Finset γ) (k : ℕ) (hk : 0 < k)
    (hks : k ∣ s.card) :
    ∃ P : Fin ((s.card - 1).choose (k - 1)) → Finpartition (univ : Finset s),
      Function.Injective P ∧ (∀ i, ∀ t ∈ (P i).parts, t.card = k) ∧
      (∀ t : Finset s, t.card = k → ∃! i, t ∈ (P i).parts) ∧
      (∀ i, (P i).parts.card * k = s.card) := by
  obtain ⟨c, hc⟩ := Baranyai.baranyai_finset s k hk hks
  exact l14_classes hk (Fintype.card_coe s) l14_choose_le hc

/-- Mathlib-only form of `Baranyai.dvd_card_of_factorisation`: if the finite type `α` has a
partition into blocks of size `k`, then `k ∣ |α|`. -/
theorem l14_dvd_card_of_factorisation [Fintype α] [DecidableEq α] {k : ℕ}
    (P : Finpartition (univ : Finset α)) (hP : ∀ t ∈ P.parts, t.card = k) :
    k ∣ Fintype.card α := by
  classical
  let c : {S : Finset α // S.card = k} → Fin 2 := fun S => if S.1 ∈ P.parts then 0 else 1
  refine Baranyai.dvd_card_of_factorisation (c := c) ⟨0, fun v => ?_⟩
  obtain ⟨t, ⟨ht, hvt⟩, hu⟩ := P.existsUnique_mem (mem_univ v)
  refine ⟨⟨t, hP t ht⟩, ⟨by simp [c, ht], hvt⟩, ?_⟩
  rintro ⟨T, hT⟩ ⟨h1, h2⟩
  have hTP : T ∈ P.parts := by
    by_contra h; simp [c, h] at h1
  exact Subtype.ext (hu T ⟨hTP, h2⟩)

/-! ## Witnesses -/

/-- Bounded (decidable) form of unique existence in a finset. -/
private lemma l14_eu {β : Type*} {C : Finset β} {p : β → Prop}
    (h : ∃ t ∈ C, p t ∧ ∀ u ∈ C, p u → u = t) : ∃! t, t ∈ C ∧ p t := by
  obtain ⟨t, ht, hp, hu⟩ := h
  exact ⟨t, ⟨ht, hp⟩, fun u ⟨h1, h2⟩ => hu u h1 h2⟩

/-- Witness for `l14_baranyai` (`n = 4`, `k = 2`, written out by hand) and for its Mathlib-only
reading: the explicit family of three classes consists of three distinct classes, each a perfect
matching of `Fin 4` by 2-blocks, and every 2-subset lies in exactly one class. -/
theorem l14w_baranyai_explicit :
    ∃ K : Finset (Finset (Finset (Fin 4))),
      K = {{{0, 1}, {2, 3}}, {{0, 2}, {1, 3}}, {{0, 3}, {1, 2}}} ∧
      K.card = (4 - 1).choose (2 - 1) ∧
      (∀ C ∈ K, (∀ t ∈ C, t.card = 2) ∧ (∀ a : Fin 4, ∃! t, t ∈ C ∧ a ∈ t)) ∧
      (∀ t ∈ powersetCard 2 (univ : Finset (Fin 4)), ∃! C, C ∈ K ∧ t ∈ C) := by
  refine ⟨_, rfl, by decide, ?_⟩
  have h1 : ∀ C ∈ ({{{0, 1}, {2, 3}}, {{0, 2}, {1, 3}}, {{0, 3}, {1, 2}}} :
      Finset (Finset (Finset (Fin 4)))), (∀ t ∈ C, t.card = 2) ∧
      (∀ a : Fin 4, ∃ t ∈ C, a ∈ t ∧ ∀ u ∈ C, a ∈ u → u = t) := by
    intro C hC
    simp only [mem_insert, mem_singleton] at hC
    rcases hC with rfl | rfl | rfl <;> decide
  have h2 : ∀ t ∈ powersetCard 2 (univ : Finset (Fin 4)),
      ∃ C ∈ ({{{0, 1}, {2, 3}}, {{0, 2}, {1, 3}}, {{0, 3}, {1, 2}}} :
        Finset (Finset (Finset (Fin 4)))), t ∈ C ∧ ∀ D ∈ ({{{0, 1}, {2, 3}}, {{0, 2}, {1, 3}},
          {{0, 3}, {1, 2}}} : Finset (Finset (Finset (Fin 4)))), t ∈ D → D = C := by
    intro t ht
    rw [mem_powersetCard] at ht
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 ht.2
    fin_cases x <;> fin_cases y <;>
      simp only [mem_insert, mem_singleton, exists_eq_left, forall_eq_or_imp, forall_eq,
        exists_eq_or_imp] <;> first | exact absurd rfl hxy | decide
  exact ⟨fun C hC => ⟨(h1 C hC).1, fun a => l14_eu ((h1 C hC).2 a)⟩,
    fun t ht => l14_eu (h2 t ht)⟩

/-- Witness for `l14_baranyai`: `n = 6`, `k = 3` satisfy the hypotheses, and the conclusion
gives `10` pairwise distinct partitions of `Fin 6`, each into exactly two disjoint triples. -/
theorem l14w_baranyai :
    0 < 3 ∧ 3 ∣ 6 ∧ (6 - 1).choose (3 - 1) = 10 ∧
    ∃ P : Fin 10 → Finpartition (univ : Finset (Fin 6)),
      (∀ i j, i ≠ j → P i ≠ P j) ∧ (∀ i, (P i).parts.card = 2) ∧
      (∀ i, ∀ t ∈ (P i).parts, t.card = 3) ∧
      (∀ t : Finset (Fin 6), t.card = 3 → ∃! i, t ∈ (P i).parts) := by
  obtain ⟨P, hinj, hk, hu, hc⟩ := l14_baranyai 6 3 (by norm_num) (by norm_num)
  refine ⟨by norm_num, by norm_num, by decide, P, fun i j hij h => hij (hinj h), fun i => ?_,
    hk, hu⟩
  have := hc i; omega

/-- Witness for `l14_baranyai'`: `n = 6`, `k = 2`; `C(6,2)·2/6 = 5` distinct perfect matchings. -/
theorem l14w_baranyai' :
    0 < 2 ∧ 0 < 6 ∧ 2 ∣ 6 ∧ (6 : ℕ).choose 2 * 2 / 6 = 5 ∧
    ∃ P : Fin 5 → Finpartition (univ : Finset (Fin 6)),
      (∀ i j, i ≠ j → P i ≠ P j) ∧ (∀ i, (P i).parts.card = 3) ∧
      (∀ t : Finset (Fin 6), t.card = 2 → ∃! i, t ∈ (P i).parts) := by
  obtain ⟨P, hinj, -, hu, hc⟩ := l14_baranyai' 6 2 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨by norm_num, by norm_num, by norm_num, by decide, P, fun i j hij h => hij (hinj h),
    fun i => ?_, hu⟩
  have := hc i; omega

/-- Witness for `l14_baranyai_of_card`: the vertex type `Fin 2 × Fin 3` (6 vertices, not of the
form `Fin n`), `k = 3`; the 10 resulting partitions are distinct, each with two triples. -/
theorem l14w_baranyai_of_card :
    Fintype.card (Fin 2 × Fin 3) = 6 ∧
    ∃ P : Fin 10 → Finpartition (univ : Finset (Fin 2 × Fin 3)),
      (∀ i j, i ≠ j → P i ≠ P j) ∧ (∀ i, (P i).parts.card = 2) ∧
      (∀ t : Finset (Fin 2 × Fin 3), t.card = 3 → ∃! i, t ∈ (P i).parts) := by
  obtain ⟨P, hinj, -, hu, hc⟩ :=
    l14_baranyai_of_card (α := Fin 2 × Fin 3) 6 3 (by norm_num) (by norm_num) (by simp)
  refine ⟨by simp, P, fun i j hij h => hij (hinj h), fun i => ?_, hu⟩
  have := hc i; omega

/-- Witness for `l14_baranyai_finset`: `s = {0, 2, 4, 6} ⊆ ℕ`, `k = 2`; three distinct perfect
matchings of `s`, each with two pairs. -/
theorem l14w_baranyai_finset :
    ({0, 2, 4, 6} : Finset ℕ).card = 4 ∧
    (({0, 2, 4, 6} : Finset ℕ).card - 1).choose (2 - 1) = 3 ∧
    ∃ P : Fin ((({0, 2, 4, 6} : Finset ℕ).card - 1).choose (2 - 1)) →
        Finpartition (univ : Finset ({0, 2, 4, 6} : Finset ℕ)),
      (∀ i j, i ≠ j → P i ≠ P j) ∧ (∀ i, (P i).parts.card = 2) ∧
      (∀ t : Finset ({0, 2, 4, 6} : Finset ℕ), t.card = 2 → ∃! i, t ∈ (P i).parts) := by
  have h4 : ({0, 2, 4, 6} : Finset ℕ).card = 4 := by decide
  obtain ⟨P, hinj, -, hu, hc⟩ :=
    l14_baranyai_finset ({0, 2, 4, 6} : Finset ℕ) 2 (by norm_num) (by rw [h4]; norm_num)
  refine ⟨h4, by rw [h4]; decide, P, fun i j hij h => hij (hinj h), fun i => ?_, hu⟩
  have := hc i; rw [h4] at this; omega

/-- Witness for `l14_baranyai_partition`: `α = Fin 6`, `k = 3`. The partition of the 20 triples
has 10 classes, each class consists of two distinct, disjoint triples. -/
theorem l14w_baranyai_partition :
    ∃ Q : Finpartition (powersetCard 3 (univ : Finset (Fin 6))),
      Q.parts.card = 10 ∧ (powersetCard 3 (univ : Finset (Fin 6))).card = 20 ∧
      ∀ C ∈ Q.parts, C.card = 2 ∧ ∃ t ∈ C, ∃ u ∈ C, t ≠ u ∧ Disjoint t u := by
  obtain ⟨Q, hQ, hC⟩ := l14_baranyai_partition (α := Fin 6) 6 3 (by norm_num) (by norm_num)
    (by norm_num) (by simp)
  refine ⟨Q, by rw [hQ]; decide, by decide, fun C hCQ => ?_⟩
  obtain ⟨hk, hcov, hcard⟩ := hC C hCQ
  refine ⟨by rw [hcard], ?_⟩
  obtain ⟨t, ⟨ht, h0t⟩, hu⟩ := hcov 0
  obtain ⟨t', ht'⟩ : ∃ u ∈ C, u ≠ t := by
    by_contra h; push Not at h
    have : C ⊆ {t} := fun u hu => mem_singleton.2 (h u hu)
    have := card_le_card this; rw [hcard] at this; simp at this
  refine ⟨t, ht, t', ht'.1, ht'.2.symm, ?_⟩
  rw [disjoint_left]
  intro a hat hat'
  obtain ⟨w, -, hw⟩ := hcov a
  exact ht'.2 ((hw t' ⟨ht'.1, hat'⟩).trans (hw t ⟨ht, hat⟩).symm)

/-- Witness for `l14_complete_graph_one_factorisation`: `n = 6`; the five perfect matchings of
`K_6` are distinct and each has three edges. -/
theorem l14w_complete_graph_one_factorisation :
    Even 6 ∧ ∃ G : Fin 5 → (⊤ : SimpleGraph (Fin 6)).Subgraph,
      (∀ i j, i ≠ j → G i ≠ G j) ∧ (∀ i, (G i).IsPerfectMatching) ∧
      (∀ i, (G i).verts = Set.univ) ∧
      ∀ v w : Fin 6, v ≠ w → ∃! i, (G i).Adj v w := by
  obtain ⟨G, hinj, hp, he⟩ := l14_complete_graph_one_factorisation 6 (by decide)
  exact ⟨by decide, G, fun i j hij h => hij (hinj h), hp,
    fun i => (SimpleGraph.Subgraph.isSpanning_iff.1 (hp i).2), he⟩

/-- Witness for `l14_baranyai_four_two`: the three matchings of `K_4` are pairwise distinct, and
the edge `01` is in exactly one of them while each vertex has a partner in each matching. -/
theorem l14w_baranyai_four_two :
    ∃ G : Fin 3 → (⊤ : SimpleGraph (Fin 4)).Subgraph,
      G 0 ≠ G 1 ∧ G 0 ≠ G 2 ∧ G 1 ≠ G 2 ∧ (∀ i, (G i).IsPerfectMatching) ∧
      ∃! i, (G i).Adj 0 1 := by
  obtain ⟨G, hinj, hp, he⟩ := l14_baranyai_four_two
  exact ⟨G, fun h => by simpa using hinj h, fun h => by simpa using hinj h,
    fun h => by simpa using hinj h, hp, he 0 1 (by decide)⟩

/-- Witness for `l14_dvd_card_of_factorisation`: `Fin 6` with the partition `{012, 345}` into
triples (a genuine 2-block partition) satisfies the hypotheses, so `3 ∣ 6`; and the conclusion is
not vacuous: `Fin 5` admits no partition into pairs, since `¬ 2 ∣ 5`. -/
theorem l14w_dvd_card_of_factorisation :
    (∃ P : Finpartition (univ : Finset (Fin 6)), P.parts.card = 2 ∧ ∀ t ∈ P.parts, t.card = 3) ∧
    3 ∣ Fintype.card (Fin 6) ∧
    ¬ ∃ P : Finpartition (univ : Finset (Fin 5)), ∀ t ∈ P.parts, t.card = 2 := by
  refine ⟨⟨Finpartition.ofExistsUnique {{0, 1, 2}, {3, 4, 5}} (fun _ _ => subset_univ _)
    (fun a _ => l14_eu (by revert a; decide)) (by decide), by decide, by decide⟩, ?_, ?_⟩
  · obtain ⟨P, -, hP⟩ : ∃ P : Finpartition (univ : Finset (Fin 6)), P.parts.card = 2 ∧
        ∀ t ∈ P.parts, t.card = 3 :=
      ⟨Finpartition.ofExistsUnique {{0, 1, 2}, {3, 4, 5}} (fun _ _ => subset_univ _)
        (fun a _ => l14_eu (by revert a; decide)) (by decide), by decide, by decide⟩
    exact l14_dvd_card_of_factorisation P hP
  · rintro ⟨P, hP⟩
    have := l14_dvd_card_of_factorisation P hP
    simp at this

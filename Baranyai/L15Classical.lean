import Baranyai.Basic
import Baranyai.Transport
import Baranyai.Partition
import Mathlib

/-!
# Layer 15: classical-statement comparison

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.

The writer's `classical_*` theorems are restated below with their text unchanged; each proof is
`apply cov_X <;> assumption`. The general form `classical_Baranyai3_main` (arbitrary class sizes,
`k ∤ n`) is not formalised in this repository and is kept as a `Prop`; only the divisible
equal-size instance is proved (`cov_Baranyai3_main_part`). No writer statement was found false.
-/

open Finset

namespace Baranyai.Classical

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Writer's definitions (verbatim) -/

/-- OWN DEFINITION. A family `M` of `k`-subsets of `X` is a *perfect matching* (1-factor) of the
complete `k`-uniform hypergraph on `X`: its members are `k`-sets, pairwise disjoint,
and their union is all of `X`. -/
def IsPerfectMatchingK (k : ℕ) (M : Finset (Finset X)) : Prop :=
  (∀ e ∈ M, e.card = k) ∧ (M : Set (Finset X)).PairwiseDisjoint id ∧ ∀ x : X, ∃ e ∈ M, x ∈ e

/-- OWN DEFINITION. `A` is a partition of the family of all `k`-subsets of `X` into the
classes `A i`, `i : Fin t`: each class consists of `k`-subsets, and each `k`-subset lies in
exactly one class. -/
def IsPartitionOfKSubsets (k t : ℕ) (A : Fin t → Finset (Finset X)) : Prop :=
  (∀ i, A i ⊆ powersetCard k (univ : Finset X)) ∧
    ∀ s ∈ powersetCard k (univ : Finset X), ∃! i, s ∈ A i

/-- OWN DEFINITION. Degree of a point `x` in a family `A` of subsets: number of members of
`A` containing `x`. -/
def pointDegree (A : Finset (Finset X)) (x : X) : ℕ := (A.filter (fun e => x ∈ e)).card

/-- OWN DEFINITION. A family `A` of `k`-subsets of the `n`-set `X` is *almost regular*: every
point lies in either `⌊k·|A|/n⌋` or `⌈k·|A|/n⌉` members of `A`. -/
def IsAlmostRegular (n k : ℕ) (A : Finset (Finset X)) : Prop :=
  ∀ x : X, pointDegree A x = ⌊((k * A.card : ℕ) : ℚ) / n⌋₊ ∨
    pointDegree A x = ⌈((k * A.card : ℕ) : ℚ) / n⌉₊

/-! ## Bridge: colouring `c` (repository form) ↦ colour classes (writer form) -/

/-- Colour class `i` of a colouring of the `k`-subsets, as a family of finsets. -/
def classesOf {k M : ℕ} (c : {S : Finset X // S.card = k} → Fin M) (i : Fin M) :
    Finset (Finset X) :=
  (univ.filter fun S => c S = i).map (Function.Embedding.subtype _)

lemma mem_classesOf {k M : ℕ} (c : {S : Finset X // S.card = k} → Fin M) (i : Fin M)
    (e : Finset X) : e ∈ classesOf c i ↔ ∃ h : e.card = k, c ⟨e, h⟩ = i := by
  simp only [classesOf, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨⟨s, hs⟩, h1, rfl⟩; exact ⟨hs, h1⟩
  · rintro ⟨h, h1⟩; exact ⟨⟨e, h⟩, h1, rfl⟩

lemma classesOf_spec {k M : ℕ} (hk : 0 < k) (c : {S : Finset X // S.card = k} → Fin M)
    (hc : ∀ i (v : X), ∃! S : {S : Finset X // S.card = k}, c S = i ∧ v ∈ S.1) :
    IsPartitionOfKSubsets k M (classesOf c) ∧
      ∀ i, IsPerfectMatchingK k (classesOf c i) ∧ (classesOf c i).card = Fintype.card X / k := by
  refine ⟨⟨fun i e he => ?_, fun s hs => ?_⟩, fun i => ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · obtain ⟨h, -⟩ := (mem_classesOf c i e).1 he
    exact mem_powersetCard.2 ⟨subset_univ _, h⟩
  · have hs' := (mem_powersetCard.1 hs).2
    refine ⟨c ⟨s, hs'⟩, (mem_classesOf c _ s).2 ⟨hs', rfl⟩, fun j hj => ?_⟩
    obtain ⟨h, hj⟩ := (mem_classesOf c j s).1 hj
    exact hj.symm
  · intro e he; exact ((mem_classesOf c i e).1 he).1
  · intro e he f hf hef
    obtain ⟨h1, h1'⟩ := (mem_classesOf c i e).1 he
    obtain ⟨h2, h2'⟩ := (mem_classesOf c i f).1 hf
    exact Baranyai.block_disjoint hc (S := ⟨e, h1⟩) (T := ⟨f, h2⟩)
      (fun h => hef (congrArg Subtype.val h)) (h1'.trans h2'.symm)
  · intro x
    obtain ⟨S, ⟨hS, hx⟩, -⟩ := hc i x
    exact ⟨S.1, (mem_classesOf c i S.1).2 ⟨S.2, hS⟩, hx⟩
  · rw [classesOf, card_map]
    exact Baranyai.class_card hk hc i

/-- The repository's `baranyai_of_card`, restated in the writer's class form (no `0 < n`). -/
lemma classes_exist (n k : ℕ) (hk : 0 < k) (hkn : k ∣ n) (hX : Fintype.card X = n) :
    ∃ M : Fin (Nat.choose (n - 1) (k - 1)) → Finset (Finset X),
      IsPartitionOfKSubsets k _ M ∧ ∀ i, IsPerfectMatchingK k (M i) ∧ (M i).card = n / k := by
  obtain ⟨c, hc⟩ := Baranyai.baranyai_of_card (α := X) n k hk hkn hX
  obtain ⟨h1, h2⟩ := classesOf_spec hk c hc
  exact ⟨classesOf c, h1, fun i => ⟨(h2 i).1, hX ▸ (h2 i).2⟩⟩

/-- A perfect matching of `k`-sets, viewed as a `Finpartition` of `univ`. -/
def toFinpartition {k : ℕ} (hk : 0 < k) (A : Finset (Finset X)) (hA : IsPerfectMatchingK k A) :
    Finpartition (univ : Finset X) where
  parts := A
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.2 hA.2.1
  sup_parts := by
    ext x
    simp only [mem_sup, id, mem_univ, iff_true]
    obtain ⟨e, he, hx⟩ := hA.2.2 x
    exact ⟨e, he, hx⟩
  bot_notMem := by
    intro h
    have := hA.1 ⊥ h
    rw [Finset.bot_eq_empty, card_empty] at this
    omega

lemma pointDegree_eq_one {k : ℕ} {A : Finset (Finset X)} (hA : IsPerfectMatchingK k A) (x : X) :
    pointDegree A x = 1 := by
  obtain ⟨e, he, hx⟩ := hA.2.2 x
  rw [pointDegree, card_eq_one]
  refine ⟨e, ?_⟩
  ext f
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨hf, hxf⟩
    by_contra hfe
    exact Finset.disjoint_left.1 (hA.2.1 hf he hfe) hxf hx
  · rintro rfl; exact ⟨he, hx⟩

lemma ratio_eq_one (n k : ℕ) (hn : 0 < n) (hkn : k ∣ n) :
    ((k * (n / k) : ℕ) : ℚ) / n = 1 := by
  rw [Nat.mul_div_cancel' hkn]
  have : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  exact div_self this

/-! ## Comparisons -/

/-- (E) `classical_Baranyai1_b` ← `Baranyai.choose_mul`. -/
theorem cov_Baranyai1_b (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    Nat.choose (n - 1) (k - 1) * n = Nat.choose n k * k := by
  rw [mul_comm]; exact Baranyai.choose_mul hk hn

/-- (E) `classical_Baranyai1_a` ← `Baranyai.baranyai_of_card` + `block_disjoint` + `class_card`. -/
theorem cov_Baranyai1_a (n k : ℕ) (_hn : 0 < n) (hk : 0 < k) (hkn : k ∣ n)
    (hX : Fintype.card X = n) :
    ∃ M : Fin (Nat.choose (n - 1) (k - 1)) → Finset (Finset X),
      IsPartitionOfKSubsets k _ M ∧
        ∀ i, IsPerfectMatchingK k (M i) ∧ (M i).card = n / k :=
  classes_exist n k hk hkn hX

/-- (E) `classical_Baranyai2_a` (including `n = 0`). -/
theorem cov_Baranyai2_a (n k : ℕ) (hk : 0 < k) (hkn : k ∣ n)
    (hX : Fintype.card X = n) :
    ∃ P : Fin (Nat.choose (n - 1) (k - 1)) → Finpartition (univ : Finset X),
      IsPartitionOfKSubsets k _ (fun i => (P i).parts) ∧
        ∀ i, (∀ b ∈ (P i).parts, b.card = k) ∧ (P i).parts.card = n / k := by
  obtain ⟨M, h1, h2⟩ := classes_exist n k hk hkn hX
  exact ⟨fun i => toFinpartition hk (M i) (h2 i).1, h1, fun i => ⟨(h2 i).1.1, (h2 i).2⟩⟩

/-- (E) `classical_Baranyai2_b` (including `n = 0`). -/
theorem cov_Baranyai2_b (n k : ℕ) (hk : 0 < k) (hkn : k ∣ n)
    (hX : Fintype.card X = n) :
    ∃ P : Fin (Nat.choose (n - 1) (k - 1)) → Finpartition (univ : Finset X),
      (∀ i, ∀ b ∈ (P i).parts, b.card = k) ∧
        ∀ s ∈ powersetCard k (univ : Finset X), ∃! i, s ∈ (P i).parts := by
  obtain ⟨M, h1, h2⟩ := classes_exist n k hk hkn hX
  exact ⟨fun i => toFinpartition hk (M i) (h2 i).1, fun i => (h2 i).1.1, h1.2⟩

/-- (E) `classical_Baranyai3_a`. -/
theorem cov_Baranyai3_a (n k : ℕ) (hk : 0 < k) (hkn' : k ≤ n) (hkn : k ∣ n)
    (hX : Fintype.card X = n) :
    ∃ A : Fin (Nat.choose (n - 1) (k - 1)) → Finset (Finset X),
      IsPartitionOfKSubsets k _ A ∧
        ∀ i, (A i).card = n / k ∧ IsAlmostRegular n k (A i) ∧ IsPerfectMatchingK k (A i) := by
  obtain ⟨M, h1, h2⟩ := classes_exist n k hk hkn hX
  refine ⟨M, h1, fun i => ⟨(h2 i).2, fun x => Or.inl ?_, (h2 i).1⟩⟩
  rw [pointDegree_eq_one (h2 i).1 x, (h2 i).2, ratio_eq_one n k (by omega) hkn, Nat.floor_one]

/-- (O, NEW PROOF) `classical_Baranyai3_a_implication`: elementary, not in the repository. -/
theorem cov_Baranyai3_a_implication (n k : ℕ) (hk : 0 < k) (hkn' : k ≤ n) (hkn : k ∣ n)
    (hX : Fintype.card X = n) (A : Fin (Nat.choose (n - 1) (k - 1)) → Finset (Finset X))
    (hA : IsPartitionOfKSubsets k _ A)
    (hreg : ∀ i, (A i).card = n / k ∧ IsAlmostRegular n k (A i)) :
    ∀ i, IsPerfectMatchingK k (A i) := by
  intro i
  have hdeg : ∀ x, pointDegree (A i) x = 1 := by
    intro x
    have h := (hreg i).2 x
    rw [(hreg i).1, ratio_eq_one n k (by omega) hkn, Nat.floor_one, Nat.ceil_one] at h
    exact h.elim id id
  refine ⟨fun e he => (mem_powersetCard.1 (hA.1 i he)).2, ?_, fun x => ?_⟩
  · intro e he f hf hef
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro x hxe hxf
    have hsub : ({e, f} : Finset (Finset X)) ⊆ (A i).filter (fun e => x ∈ e) := by
      intro g hg
      rcases mem_insert.1 hg with rfl | hg
      · exact mem_filter.2 ⟨he, hxe⟩
      · rw [mem_singleton.1 hg]; exact mem_filter.2 ⟨hf, hxf⟩
    have := card_le_card hsub
    rw [card_pair hef] at this
    have := hdeg x
    rw [pointDegree] at this
    omega
  · have h := hdeg x
    rw [pointDegree] at h
    obtain ⟨e, he⟩ := card_pos.1 (by omega : 0 < ((A i).filter (fun e => x ∈ e)).card)
    exact ⟨e, (mem_filter.1 he).1, (mem_filter.1 he).2⟩

/-- (E) `classical_Baranyai3_b` ← `complete_graph_one_factorisation` + `factorisation_congr`. -/
theorem cov_Baranyai3_b {V : Type*} [Fintype V] (n : ℕ) (hn : Even n)
    (hV : Fintype.card V = n) :
    ∃ M : Fin (n - 1) → (⊤ : SimpleGraph V).Subgraph,
      (∀ i, (M i).IsPerfectMatching) ∧
        ∀ e ∈ (⊤ : SimpleGraph V).edgeSet, ∃! i, e ∈ (M i).edgeSet := by
  classical
  obtain ⟨c, hc⟩ := Baranyai.factorisation_congr (Fintype.equivFinOfCardEq hV).symm
    (complete_graph_one_factorisation n hn)
  let M : Fin (n - 1) → (⊤ : SimpleGraph V).Subgraph := fun i =>
    { verts := Set.univ
      Adj := fun v w => ∃ S : {S : Finset V // S.card = 2}, c S = i ∧ S.1 = {v, w}
      adj_sub := by
        rintro v w ⟨S, -, hS⟩
        simp only [SimpleGraph.top_adj]
        rintro rfl
        have := S.2
        rw [hS, pair_eq_singleton, card_singleton] at this
        omega
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun v w ⟨S, h1, h2⟩ => ⟨S, h1, h2.trans (pair_comm v w)⟩⟩ }
  have hadj : ∀ i v w, (M i).Adj v w ↔
      ∃ S : {S : Finset V // S.card = 2}, c S = i ∧ S.1 = {v, w} := fun _ _ _ => Iff.rfl
  refine ⟨M, fun i => ⟨fun v _ => ?_, fun v => Set.mem_univ v⟩, fun e he => ?_⟩
  · obtain ⟨S, ⟨hSi, hvS⟩, hSu⟩ := hc i v
    obtain ⟨a, b, hab, hS⟩ := card_eq_two.1 S.2
    have : ∃ w, w ≠ v ∧ S.1 = {v, w} := by
      rw [hS] at hvS ⊢
      rcases mem_insert.1 hvS with rfl | h
      · exact ⟨b, hab.symm, rfl⟩
      · rw [mem_singleton.1 h]; exact ⟨a, hab, pair_comm a b⟩
    obtain ⟨w, hwv, hSw⟩ := this
    refine ⟨w, (hadj i v w).2 ⟨S, hSi, hSw⟩, fun w' hw' => ?_⟩
    obtain ⟨S', hS'i, hS'⟩ := (hadj i v w').1 hw'
    have hS'S : S' = S := hSu S' ⟨hS'i, by rw [hS']; exact mem_insert_self _ _⟩
    have hw'S : w' ∈ S.1 := by rw [← hS'S, hS']; simp
    rw [hSw] at hw'S
    rcases mem_insert.1 hw'S with h | h
    · subst h
      have := S'.2
      rw [hS', pair_eq_singleton, card_singleton] at this
      omega
    · exact mem_singleton.1 h
  · induction e using Sym2.ind with
    | _ v w =>
    have hvw : v ≠ w := by simpa using he
    have hcard : ({v, w} : Finset V).card = 2 := card_pair hvw
    refine ⟨c ⟨{v, w}, hcard⟩, ?_, fun j hj => ?_⟩
    · dsimp only
      rw [SimpleGraph.Subgraph.mem_edgeSet]
      exact ⟨⟨{v, w}, hcard⟩, rfl, rfl⟩
    · dsimp only at hj
      rw [SimpleGraph.Subgraph.mem_edgeSet] at hj
      obtain ⟨S, hSj, hS⟩ := hj
      rw [← hSj]
      exact congrArg c (Subtype.ext hS)

/-- (O, partial) `classical_Baranyai3_main` restricted to the divisible equal-size instance
`k ∣ n`, `t = C(n-1,k-1)`, `a_i = n/k` (the only instance the repository supports). -/
theorem cov_Baranyai3_main_part (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) (hdvd : k ∣ n)
    (hX : Fintype.card X = n) :
    ∃ A : Fin (Nat.choose (n - 1) (k - 1)) → Finset (Finset X),
      IsPartitionOfKSubsets k _ A ∧ ∀ i, (A i).card = (fun _ => n / k) i ∧
        IsAlmostRegular n k (A i) := by
  obtain ⟨A, h1, h2⟩ := cov_Baranyai3_a n k hk hkn hdvd hX
  exact ⟨A, h1, fun i => ⟨(h2 i).1, (h2 i).2.1⟩⟩

/-! ## Writer's statements (verbatim); proofs are the `cov_` theorems above -/

/-- Baranyai1, arithmetic part: the count `C(n-1,k-1) = C(n,k)·(k/n)` quoted in the statement,
written without division as `C(n-1,k-1)·n = C(n,k)·k` (for positive `n`, `k`).
(Not a well-formedness obligation: the main statements use `C(n-1,k-1)` directly.) -/
theorem classical_Baranyai1_b (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    Nat.choose (n - 1) (k - 1) * n = Nat.choose n k * k := by
  apply cov_Baranyai1_b <;> assumption

/-- Baranyai1 (divisible case, hypergraph form). If `0 < n`, `0 < k`, `k ∣ n`, the complete
`k`-uniform hypergraph on an `n`-set decomposes into `C(n-1,k-1)` perfect matchings, each
consisting of `n/k` pairwise disjoint `k`-subsets covering `X`. -/
theorem classical_Baranyai1_a (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k ∣ n)
    (hX : Fintype.card X = n) :
    ∃ M : Fin (Nat.choose (n - 1) (k - 1)) → Finset (Finset X),
      IsPartitionOfKSubsets k _ M ∧
        ∀ i, IsPerfectMatchingK k (M i) ∧ (M i).card = n / k := by
  apply cov_Baranyai1_a <;> assumption

/-- Baranyai2 (parallel-class form). The family of all `k`-subsets of the `n`-set `X`
can be partitioned into `C(n-1,k-1)` classes, each of which is a parallel class, i.e. the set
of blocks of a partition (`Finpartition`) of `X` into `n/k` blocks of size `k`.
-- AMBIGUOUS: `n = 0` is allowed by the classical wording ("finite set", `k ∣ n`); then
-- `C(n-1,k-1)` is read with truncated subtraction `C(0,k-1)`. Alternative: add `0 < n`. -/
theorem classical_Baranyai2_a (n k : ℕ) (hk : 0 < k) (hkn : k ∣ n)
    (hX : Fintype.card X = n) :
    ∃ P : Fin (Nat.choose (n - 1) (k - 1)) → Finpartition (univ : Finset X),
      IsPartitionOfKSubsets k _ (fun i => (P i).parts) ∧
        ∀ i, (∀ b ∈ (P i).parts, b.card = k) ∧ (P i).parts.card = n / k := by
  apply cov_Baranyai2_a <;> assumption

/-- Baranyai2, "equivalently" form: there are `C(n-1,k-1)` partitions of `X` into `k`-sets
such that every `k`-subset of `X` occurs as a block in exactly one of them.
-- AMBIGUOUS: same `n = 0` remark as `classical_Baranyai2_a`. -/
theorem classical_Baranyai2_b (n k : ℕ) (hk : 0 < k) (hkn : k ∣ n)
    (hX : Fintype.card X = n) :
    ∃ P : Fin (Nat.choose (n - 1) (k - 1)) → Finpartition (univ : Finset X),
      (∀ i, ∀ b ∈ (P i).parts, b.card = k) ∧
        ∀ s ∈ powersetCard k (univ : Finset X), ∃! i, s ∈ (P i).parts := by
  apply cov_Baranyai2_b <;> assumption

/-- Baranyai3 (general form, van Lint–Wilson Thm 38.1). For `0 < k ≤ n`, an `n`-set `X` and
nonnegative integers `a_1,…,a_t` summing to `C(n,k)`, the `k`-subsets of `X` can be
partitioned into collections `A_1,…,A_t` with `|A_i| = a_i`, each almost regular. -/
-- The writer's statement, kept verbatim as a `Prop` (its binders become `∀`); it is not
-- proved here (general `t`, `a_i` and `k ∤ n` are not formalised).
def classical_Baranyai3_main : Prop :=
  ∀ (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (hX : Fintype.card X = n) (t : ℕ) (a : Fin t → ℕ)
    (ha : ∑ i, a i = Nat.choose n k),
    ∃ A : Fin t → Finset (Finset X),
      IsPartitionOfKSubsets k t A ∧ ∀ i, (A i).card = a i ∧ IsAlmostRegular n k (A i)

/-- Baranyai3 (a). If `k ∣ n`, taking `t = C(n-1,k-1)` and all `a_i = n/k`, the partition of
Baranyai3 exists and each `A_i` is a partition of `X` (a perfect matching), recovering
Baranyai1/Baranyai2.
-- AMBIGUOUS: (a) could also be read as the bare implication "any almost-regular partition
-- with these parameters consists of perfect matchings"; we state existence together with
-- the conclusion, which subsumes Baranyai1. -/
theorem classical_Baranyai3_a (n k : ℕ) (hk : 0 < k) (hkn' : k ≤ n) (hkn : k ∣ n)
    (hX : Fintype.card X = n) :
    ∃ A : Fin (Nat.choose (n - 1) (k - 1)) → Finset (Finset X),
      IsPartitionOfKSubsets k _ A ∧
        ∀ i, (A i).card = n / k ∧ IsAlmostRegular n k (A i) ∧ IsPerfectMatchingK k (A i) := by
  apply cov_Baranyai3_a <;> assumption

/-- Baranyai3 (a), implication part: with `k ∣ n`, `t = C(n-1,k-1)`, `a_i = n/k`, any
partition of the `k`-subsets into almost-regular classes of size `n/k` consists of
partitions of `X`. -/
theorem classical_Baranyai3_a_implication (n k : ℕ) (hk : 0 < k) (hkn' : k ≤ n) (hkn : k ∣ n)
    (hX : Fintype.card X = n) (A : Fin (Nat.choose (n - 1) (k - 1)) → Finset (Finset X))
    (hA : IsPartitionOfKSubsets k _ A)
    (hreg : ∀ i, (A i).card = n / k ∧ IsAlmostRegular n k (A i)) :
    ∀ i, IsPerfectMatchingK k (A i) := by
  apply cov_Baranyai3_a_implication <;> assumption

/-- Baranyai3 (b) (Walecki / round-robin). If `n` is even, the edges of the complete graph
`K_n` can be partitioned into `n - 1` perfect matchings (a 1-factorization of `K_n`).
-- AMBIGUOUS: `n = 0` is permitted (then there are no edges and `n - 1 = 0` in `ℕ`);
-- alternative: require `0 < n`. -/
theorem classical_Baranyai3_b {V : Type*} [Fintype V] (n : ℕ) (hn : Even n)
    (hV : Fintype.card V = n) :
    ∃ M : Fin (n - 1) → (⊤ : SimpleGraph V).Subgraph,
      (∀ i, (M i).IsPerfectMatching) ∧
        ∀ e ∈ (⊤ : SimpleGraph V).edgeSet, ∃! i, e ∈ (M i).edgeSet := by
  apply cov_Baranyai3_b <;> assumption

end Baranyai.Classical

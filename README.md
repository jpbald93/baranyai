# Baranyai's theorem in Lean 4

A Lean 4 + Mathlib formalisation of **Baranyai's theorem** (1975): if `0 < k` and `k ∣ n`, the
`k`-subsets of an `n`-element set can be partitioned into `C(n-1, k-1)` perfect matchings
(classes of `n/k` pairwise disjoint `k`-subsets covering every vertex). The case `k = 2` is the
1-factorisation of the complete graph `K_n`, `n` even.

The proof is Baranyai's vertex-by-vertex induction. The integral step uses Hall's marriage
theorem from Mathlib, with Hall's condition derived by double counting from the fractional
assignment, so no max-flow integrality theorem is needed.

**Status:** all statements are proved with no `sorry`. `gate.sh` checks 31 named declarations.

## Main statements

| Lean name | File | Statement |
|---|---|---|
| `baranyai` | `Basic.lean` | colouring `c` of the `k`-subsets of `Fin n` with `C(n-1,k-1)` colours, every vertex in exactly one block of each colour |
| `baranyai'` | `Basic.lean` | the same, with the number of colours written as `C(n,k)·k/n` |
| `complete_graph_one_factorisation` | `Basic.lean` | `k = 2`: 1-factorisation of `K_n` into `n-1` perfect matchings |
| `Baranyai.exists_partition_of_inv` | `Basic.lean` | the final-stage invariant `Baranyai.Inv` yields the factorisation |
| `Baranyai.step` | `Basic.lean` | the induction step (Hall's theorem) |
| `Baranyai.baranyai_of_card` | `Transport.lean` | `baranyai` for any finite vertex type `α` with `card α = n` |
| `Baranyai.baranyai_finset` | `Transport.lean` | `baranyai` for the vertex set of a `Finset` |
| `Baranyai.factorisation_congr` | `Transport.lean` | factorisations transport along a bijection `α ≃ β` |
| `Baranyai.baranyai_partition` | `Partition.lean` | the colouring is a genuine partition: blocks of one colour are disjoint, colour classes are pairwise disjoint and cover all `k`-subsets, each class has `n/k` blocks, and the number of classes is `C(n,k)/(n/k)` |

`Transport.lean` and `Partition.lean` derive these from the statement of `baranyai`. They do
not reprove it.

## Verification

- `./gate.sh` builds the library and generates its own `#print axioms` queries for the 31
  named declarations: every public theorem and definition in the library, fully qualified. The
  queries come from the gate itself, not from a file in the repository. The gate fails if:
  - a source file contains `sorry`, `admit`, `native_decide`, `axiom`, `#eval`, `run_cmd`,
    `set_option`, `macro`/`elab`/`syntax`/`notation`, or `import Lean`;
  - the build fails;
  - a named declaration is missing, or has an extra report;
  - a named declaration depends on anything other than `propext`, `Classical.choice` and
    `Quot.sound`.

  On success it prints `PASS (31 declarations, standard axioms only)`.
- `bash tests/tamper.sh` plants six kinds of fake proof in scratch copies and checks that the
  gate rejects each one:
  1. a `sorry`;
  2. an axiom split across two lines;
  3. an `#eval` printing a fake axiom report;
  4. a custom macro;
  5. a weakened statement: `baranyai` with the hypothesis `k ∣ n` deleted, which is false
     for `n = 3`, `k = 2`;
  6. a genuine extra axiom with a long name, so that the report wraps over several lines.
- `lake env lean scratch/Satisfiable.lean` runs the satisfiability certificates. This file sits
  outside the library and is checked by the kernel. It contains:
  - explicit factorisations for `(n,k) = (4,2)` and `(6,3)` (10 classes), checked by `decide`
    and not derived from the theorem;
  - an explicit witness of the final-stage invariant `Baranyai.Inv` for `n = 4`, `k = 2`;
  - instances of the transported and partition forms on a `Finset ℕ`, on `Fin 2 × Fin 3` and
    on `Bool × Bool`.

  It shows that the hypotheses can be met together and that the conclusions are not vacuous.

`code/check_baranyai.py` builds factorisations independently by the same induction (in
Python) and verifies them. `scratch/Ax.lean` and `scratch/ax.out` are the `#print axioms` runs
recorded during development.

## Build

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh   # if Lean is not installed
lake exe cache get
lake build
./gate.sh
bash tests/tamper.sh
lake env lean scratch/Satisfiable.lean
```

Toolchain: Lean `v4.33.1`, Mathlib `v4.33.1` (revision pinned in `lake-manifest.json`).

## Note on how this was produced

The formal proofs, checking scripts and documentation were developed with the help of a
large-language-model AI assistant. The author directed the work, checked the formal statements
against their informal counterparts by hand, and is responsible for the result. The Lean kernel
checks every proof.

## License

Apache 2.0.

# A252864 — Stoll's recurrence, formalised in Lean 4

For the sequence [OEIS A252864](https://oeis.org/A252864) — which counts, generation by
generation, the nodes of the tree of golden-ratio representations, `r = (1 + sqrt 5) / 2` —
this repository contains a machine-checked proof that

```
a(n) = a(n-1) + a(n-3)    for all n >= 12
```

and that the threshold is sharp: `a(11) != a(10) + a(8)` (75 != 51 + 25).

This answers the remark of Michael Stoll at <https://mathoverflow.net/a/195264>
(question <https://mathoverflow.net/q/195207>), which is also recorded in the
Formula field of the OEIS entry.

## The statement, as formalised

The tree is defined exactly as in the OEIS entry: the root is `(0, 0)`, every node
`(j, k)` has the two children `(j, k+1)` and `(k, j+k)`, and a node enters the tree
only on its first occurrence — any pair that has already appeared, in an earlier
generation or earlier in the same generation, is discarded. `A n` is the number of
pairs in generation `n`.

Generations: `1, 1, 2, 3, 5, 8, 12, 18, 25, 35, 51, 75, 110, 161, ...` (OEIS numbers
from generation 1; the extra `A 0 = 1` here is the root, and indices agree for `n >= 1`).

The statement being proved is a single constant, not a statement quantified over
sequences:

```lean
def StollConjecture : Prop :=
  ∀ n : Nat, 12 ≤ n → A n = A (n - 1) + A (n - 3)
```

`TEZA.lean` is self-contained: it states the conjecture and defines everything the
statement depends on, and it imports nothing from the proof tree. `_BRAMA.lean` then
proves that constant, so the theorem's *type* is the frozen statement rather than a
paraphrase of it.

## Theorems to check

| theorem | what it says |
|---|---|
| `A252864.BRAMA.teza_z_drzewa` | the main result: `TEZA.StollConjecture` |
| `A252864.TEZA.A_matches_OEIS` | `A` agrees with the first 14 terms of the OEIS DATA field |
| `A252864.TEZA.threshold_tight` | the threshold is sharp: `A 11 ≠ A 10 + A 8` |

The last two are what pin `A` to A252864 rather than to some other sequence satisfying
the same recurrence; both are proved by the Lean *kernel* (`decide +kernel`), not by the
compiler, so neither depends on `Lean.ofReduceBool`.

## Building

Lean **4.34.0-rc2** (`leanprover/lean4:v4.34.0-rc2`). No Mathlib — the only import from
outside this directory is `Std.Data.HashSet`, which ships with the toolchain.

This project does not use `lake`. There is no `lakefile.lean` and no `lake-manifest.json`;
the modules are compiled directly, in dependency order, with `LEAN_PATH` pointing at the
source directory. To build from scratch:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
elan override set leanprover/lean4:v4.34.0-rc2
cd src
for m in $(cat ../build-order.txt); do
  echo "== $m"
  LEAN_PATH=. lean "$m.lean" -o "$m.olean" || exit 1
done
```

`build-order.txt` is a topological order of the 36 modules. The build produces `.olean`
files in `src/`; they are not part of the repository.

## Reading off the axioms

```sh
cd src
LEAN_PATH=. lean _BRAMA_audyt.lean
```

`_BRAMA_audyt.lean` proves nothing; it only prints what each theorem rests on. Read the
output as follows: `[propext, Classical.choice, Quot.sound]` is a clean proof;
an added `sorryAx` means there is a gap.  A remark on `native_decide`: in some Lean
versions it introduces `Lean.ofReduceBool`, but in the toolchain used here
(4.34.0-rc2) it introduces a *per-declaration* axiom named
`<declaration>_native.native_decide.ax_1_1`.  A reader who only looks for
`Lean.ofReduceBool` would therefore miss compiler-trusted steps.  The rule that
does not depend on the version: treat **any** axiom outside
`[propext, Classical.choice, Quot.sound]` as a red flag.

The file deliberately also prints theorems that *do* carry `sorryAx`. Block C is a
positive control on the audit itself — if the audit ever failed to show `sorryAx` there,
the audit would be worthless. Block D prints the older route to the same statement,
`teza_z_drzewa_stara_droga`, which still goes through an unfinished lemma and is kept as
a witness that the audit distinguishes a closed route from an open one. The main result
is `teza_z_drzewa`.

**`TEZA.stoll_conjecture` reports `[sorryAx]`, and this is deliberate.**  Despite the
name, it is not the result: it is the *frozen statement of the conjecture*, written
once with an empty proof so that the statement itself cannot drift while the proof is
being developed.  The same proposition, `TEZA.StollConjecture`, is what
`BRAMA.teza_z_drzewa` actually proves — with no `sorry` and no external library.
The link between the formal sequence and the OEIS data is `TEZA.A_matches_OEIS`,
which depends on no axioms at all.

### Output of that command

```
'A252864.TEZA.A_matches_OEIS' does not depend on any axioms
'A252864.TEZA.threshold_tight' does not depend on any axioms
'A252864.Final.stoll_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'A252864.BRAMA.teza_z_drzewa' depends on axioms: [propext, Classical.choice, Quot.sound]
'A252864.TEZA.stoll_conjecture' depends on axioms: [sorryAx]
'A252864.BRAMA.teza_z_drzewa_stara_droga' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'A252864.Seq.five_term' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'A252864.Seq.stoll' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## A note on naming

Identifiers, namespaces and comments are in Polish, since that was the working language
of the project. The mathematics is in the statements, which are given above in English.

## License

MIT, see `LICENSE`.

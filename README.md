# oeis-lean

Machine-checked proofs of OEIS conjectures in Lean 4.

Each directory is one sequence: the statement, the proof, and an audit file that
prints what the proof actually rests on. No external libraries are used — the
trusted base is the Lean kernel together with the three standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

| sequence | statement | status |
|---|---|---|
| [A252864](A252864/) | `a(n) = a(n-1) + a(n-3)` for `n ≥ 12`, threshold sharp | proved, kernel-checked |

## Verifying a proof yourself

Install the toolchain pinned in `lean-toolchain` (via [elan](https://github.com/leanprover/elan)),
then follow the README inside the sequence directory. A full rebuild of A252864 takes
about ten minutes on one core and needs no network access.

The claim to check is not that the files compile — it is what `#print axioms` reports
for the main theorem. Anything outside `[propext, Classical.choice, Quot.sound]`
means the proof leans on something more than the kernel.

## License

MIT, see `LICENSE`.

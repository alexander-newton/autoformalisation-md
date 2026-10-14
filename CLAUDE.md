# MechDesign: project instructions

A Lean 4 / Mathlib library formalising mechanism and information design (Myerson,
Doval–Skreta, Kolotilin persuasion duality). See `README.md` for contents.

## House style: write Lean the way Halmos writes mathematics

Apply this on **every** pass: new code, refactors and reviews. A proof that compiles but
ignores these rules is not finished.

1. **Name the concept the proof keeps circling.** If several proofs repeat the same
   inequality pattern, make it a `def`, prove a few short facts about it, and derive the
   theorems as corollaries. Example: `Myerson.Supports`: "IC iff `q` supports `U`".
2. **One identity per proof.** Find the single equation that does the work, isolate it as a
   lemma, and make the main proof "apply it, then compute pointwise". Example:
   `integral_primitive_mul`.
3. **Bundle the setting.** When the same parameters thread through every statement, put them
   in a `structure` so statements read `P.canonical θ b`. Put validity hypotheses in a `Prop`
   structure (`Play.Valid`).
4. **Name objects you build twice.** Example: `Persuasion.pure`.
5. **Name elementary facts by their meaning.** For example `IsDist.wavg_le` ("an average lies
   below any upper bound") and `nonpos_of_forall_lt`. Then the main proof is a one-line
   composition.
6. **Statements read like the paper.** Use economic names (`IC`, `IR`, `revenue`, `price`).
   Docstrings state the result in words, and module docs give the proof idea in two or three
   sentences.
7. **Comments mark proof steps, not tactics.** Write a comment line such as
   `-- push C downward, so λ ≥ 0` before each logical step. Don't narrate `simp` calls.
8. **Short over clever.** Prefer `calc`, `gcongr` and `linarith`/`nlinarith` to long `rw`
   chains, but never golf at the cost of readability. Avoid `show`/`change` gymnastics when
   a better-stated lemma removes the need.
9. **Hypotheses are honest and minimal.** Drop unused instances and hypotheses. The build
   must have no warnings. Don't silence linters except `linter.unusedSectionVars`.

## Review checklist

When reviewing or re-passing any file, check the following.
- Is there a repeated pattern that should become a definition or a lemma (rules 1, 4, 5)?
- Is any proof longer than about 25 lines? If so, what is the missing lemma?
- Do the statements match the paper's theorem, with no stronger hypotheses than needed?
- Run `lake build`: no errors, no warnings, no `sorry`.
- Run `#print axioms` on the main theorems: only `propext`, `Classical.choice` and
  `Quot.sound`.
- Is the README table updated when public names change?
- **Red-team the statements.** After any new main theorem, have a separate agent audit that
  each formal statement says what its docstring and the README claim. It should check that
  the hypotheses are satisfiable (exhibit an instance in Lean), that definitions mean what
  their names say, and that every restriction is disclosed under README "Scope". Fix or
  disclose every finding before calling the work done.

## Build notes

- Toolchain: Lean `v4.35.0`, Mathlib `v4.35.0`. Run `lake build`.
- In cloud sessions, `release.lean-lang.org` and `cache.mathlib.org` may be blocked. In that
  case, install Lean from the GitHub release tarball with `elan toolchain link`, then compile
  Mathlib from source (about an hour).

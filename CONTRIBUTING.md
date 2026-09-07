# Contributing

Contributions are welcome, whether that means reporting a problem, asking a
question, or submitting code.

## Reporting issues and asking questions

Please use the [GitHub issue tracker](https://github.com/mirajcs/IsoperimetricInequality/issues).
Helpful things to include:

- your Lean and Mathlib versions (`lean --version`, and the `rev` in [`lakefile.toml`](lakefile.toml));
- the exact command you ran and its full output;
- for a mathematical question, the lemma name and the goal state you are stuck on.

## Development setup

```bash
git clone https://github.com/mirajcs/IsoperimetricInequality.git
cd IsoperimetricInequality
lake exe cache get
lake build
```

`lake build` must finish with no errors and no `sorry` before a change is ready.

## Pull requests

1. Fork the repository and create a branch off `main`.
2. Keep changes focused; one topic per pull request.
3. Follow the surrounding style: Mathlib naming conventions, `theorem`/`lemma`
   names in `snake_case`, doc-strings on public declarations.
4. Do not introduce `sorry`, `admit`, or new axioms. Run `lake build` locally and
   make sure CI ([`lean_action_ci.yml`](.github/workflows/lean_action_ci.yml)) is green.
5. If you add or rename a public declaration, update the relevant table in
   [README.md](README.md).
6. Describe what you proved and how in the pull request text.

## Scope

This project formalizes the planar isoperimetric inequality and the real Fourier
analysis it needs. Natural extensions (the equality case, a convergence theorem
for the reparametrized curve, the rectifiable generalization) are listed under
"Current limitations" in the paper and are good starting points. Contributions
that would be better placed directly in Mathlib are encouraged to go there.

## License

By contributing you agree that your contributions are licensed under the
[MIT License](LICENSE).

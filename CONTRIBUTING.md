# Contributing

Use public, disposable test data only. Do not run the library or CLI with real
wallet seeds, private keys, or secret shares, and never include them in tests,
logs, issues, or pull requests. See [SECURITY.md](SECURITY.md) for reporting concerns.

Use the Lean version pinned in `lean-toolchain`. Before opening a pull request, run:

```sh
python3 scripts/check-whitespace.py
lake build
lake test
lake build Codex32Proofs Codex32Test.VectorProofs
lake env lean scripts/Audit.lean
bash scripts/test-cli.sh
```

The axiom audit checks imported project declarations for admissions, native proof
evaluation, and nonstandard axioms. Import new proof modules in `Codex32Proofs.lean`
so the build and audit cover them. Keep executable tests distinct from proofs.

Follow `.editorconfig`: UTF-8, LF endings, two-space indentation, no trailing
whitespace, and a final newline. The CI whitespace check enforces file hygiene;
it is not a Lean syntax formatter. The pinned Lake version has no `lake fmt` command.

Check specification changes against the [pinned BIP 93 snapshot](spec/REVISION.md).
Keep the vendored text unmodified, document interpretation choices, and state
the assumptions and scope of new theorems precisely.

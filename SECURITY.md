# Security

This is experimental software for research and testing only. Do not use it with real wallet seeds or to protect funds. See the README's [remaining assumptions and limits](README.md#remaining-assumptions-and-limits) for the scope of the proofs and known limitations.

The specification is pinned to bitcoin/bips commit
`55083d36ddebcd2a039135a2f4ee74917a5803d3`; the vendored document's SHA-256
and provenance are recorded in [spec/REVISION.md](spec/REVISION.md).
Before submitting changes, build the proofs with
`lake build Codex32Proofs Codex32Test.VectorProofs` and run
`lake env lean scripts/Audit.lean`. This audit rejects admissions, native proof
evaluation, and nonstandard axioms; it does not scan for secrets or establish
CLI/OS security. See [CONTRIBUTING.md](CONTRIBUTING.md) for all required checks.

To report a suspected security issue, [open a GitHub issue](https://github.com/stutxo/codex32_lean/issues/new).

Issues are public. Use public, disposable test data in reports; never include real wallet seeds, private keys, secret shares, or other sensitive information.

Please include:

- The affected commit or version.
- Steps to reproduce, ideally with a minimal example using public test data.
- Expected and actual behavior, and the potential impact.
- Relevant error output, Lean version, and operating system when applicable.

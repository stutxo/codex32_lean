# Codex32 in Lean 4

> [!WARNING]
> **Experimental software for research and testing only.**
> Do not use this library or its CLI with real wallet seeds or to protect funds.
> Use public, disposable test data only.
>
> The Lean proofs establish specific properties under stated assumptions;
> they do not establish production readiness or end-to-end security.

A minimal Lean library implementing [BIP 93](https://github.com/bitcoin/bips/blob/55083d36ddebcd2a039135a2f4ee74917a5803d3/bip-0093.mediawiki), with official vectors and a separate, growing collection of kernel-checked proofs. Uses Lean 4.34.0 and its bundled `Std`; no Mathlib, crypto library, or Lake package dependencies.

The original implementation, proofs, and project documentation are licensed under the [MIT License](LICENSE). The vendored BIP 93 specification and its test vectors retain their authors' [BSD-3-Clause license](spec/LICENSE).

For reporting security concerns, see [SECURITY.md](SECURITY.md).

## Library usage

```lean
import Codex32
open Codex32
```

Import `Codex32` to use the library; it imports neither proofs, tests, nor CLI modules. `Encoding.parse` validates the generic format; `Seed.parse` additionally restricts it to master-seed secret/share sizes. `Seed.decodeString` requires a secret at index `s`. APIs use `Except Codex32.Error` for invalid external input; callers can pattern-match cases such as `.invalidChecksum` or use `toString` for display.

`Seed.ofBytes` constructs a seed only at a supported length. `Identifier.parse` requires four Bech32 symbols. `Threshold.ofNat` accepts 0 or 2–9. `Seed.encode seed identifier threshold padding` returns a `Message`; `Seed.encodeString` additionally serializes it. Padding defaults to zero; its low required bits may be chosen arbitrarily. `Message` carries proof fields enforcing the zero-threshold/index rule and maximum payload size. Checksums are derived during serialization, avoiding stale stored checksum fields.

`Shares.initializeFresh threshold identifier payloads` takes exactly `k` random full-symbol payloads at a supported master-seed size. `Shares.initializeExisting secret payloads` takes `k−1` such payloads and returns an interpolation set including the encoded secret; it also accepts generic application payload sizes, as specified by “For an existing secret”. Initial indices are `a,c,d,e,f,g,h,j,k` as required. Use `Shares.derive initial target` for a fresh target, `Shares.interpolate` for any target, and `Shares.recover shares` for exactly `k` distinct non-secret shares with matching threshold, identifier, and length. There are 31 non-secret field indices.

`Shares.validate` returns a `Shares.ValidatedShareSet` carrying evidence of an exact nonzero threshold, matching metadata and payload lengths, and distinct indices. Retain this value when evaluating multiple targets: `checked.interpolate target` returns a `Message` directly, while `checked.derive target` and `checked.recover` check the operation-specific index restrictions. Payload indexing uses the stored length evidence. The list-based APIs remain available as convenience wrappers.

**The pure library requires caller-supplied randomness.** Every symbol of every initial random payload, including padding bits, must be independently uniform. Zero-padding random bytes does not meet this requirement. The CLI test harness supplies OS randomness for its integration checks; deterministic fixtures are public test data, not an entropy generator.

## Project layout

The project has three module roots: `Codex32` for the library, `Codex32Proofs` for its correctness proofs, and `Codex32Test` for fixtures, tests, and the CLI test harness.

```text
Codex32.lean                 # public library import
Codex32/                     # executable BIP 93 implementation
Codex32Proofs.lean           # optional proof collection import
Codex32Proofs/               # correctness theorems
Codex32Test.lean             # shared test fixtures and vector proof
Codex32Test/
  Main.lean                 # vector and regression test runner
  Vectors.lean              # official BIP 93 fixtures
  VectorProofs.lean         # kernel-checked official-vector recovery
  Cli/                      # test-only command-line harness
    Main.lean
    Input.lean
    Random.lean
    Tests.lean
scripts/                    # integration runner and axiom audit
spec/                       # pinned BIP revision and specification
lakefile.lean               # separate build targets
lean-toolchain              # pinned Lean version
```

Import `Codex32Proofs` when using the theorems. The library's `Codex32` import and default build do not include proofs or tests. The harness lives entirely under `Codex32Test` and has no separate library target. Each test runner keeps its own executable entry point.

| Module | Responsibility |
| --- | --- |
| `Codex32.Error` | Structured error cases and human-readable messages |
| `Codex32.Alphabet` | `Fin 32` symbols, case-insensitive Bech32 conversion, threshold and four-symbol identifier types |
| `Codex32.Checksum` | Arbitrary-precision regular/long polymod, construction, verification, length selection |
| `Codex32.Encoding` | Generic Codex32 `Message`, checked parsing and lowercase/uppercase serialization |
| `Codex32.Seed` | MSB-first bit conversion, arbitrary padding, supported seed lengths, seed encoding/decoding |
| `Codex32.Field` | GF(32) arithmetic modulo x⁵ + x³ + 1, Lagrange weights and scalar interpolation |
| `Codex32.Shares` | Validated share sets, initial generation, derivation, interpolation, exact-threshold recovery |
| `Codex32Proofs.GF1024` | Extension field GF(1024) and its laws, element orders and generator re-derivation (kernel `decide`), Vandermonde uniqueness, the `sparse_zero` BCH bound |
| `Codex32Proofs.Bch` | Bit-level bridge from polymod registers to polynomial remainders, telescoped recurrence, and the regular/long error-detection theorems |
| `Codex32Proofs.Initialization` | Admissible initialization produces validated sources; complete fresh/existing initialization through recovery |
| `Codex32Proofs.ParserSpec` | Independent declarative format and exact generic/master-seed parser acceptance, including uppercase |
| `Codex32Proofs.SecrecyAlgebra`, `Uniform`, `SecrecyPayload`, `Secrecy`, `FreshSecrecy` | Polynomial masks, finite uniform sampling, and perfect secrecy of complete observed shares through both initialization APIs |
| `Codex32Proofs.Poly`, `Burst`, `Counting` | GF(32) polynomial algebra with the monic-product support theorem, the register-to-remainder bridge, burst-erasure uniqueness, and exact valid-string counts |

## Proof coverage

Proofs began after the official vector suite passed. All included theorems are checked by Lean's kernel; there are no `sorry`s, custom axioms, or `native_decide` proofs. The automated audit checks every imported project declaration and permits only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` (some statements use fewer). Executable tests and proofs are distinct evidence.

| Invariant | Current proof coverage |
| --- | --- |
| Decode after encoding | `bits_roundtrip` for every byte list and padding value; `seed_roundtrip` and `seed_string_roundtrip` for every typed seed, identifier, threshold, and padding value; `parse_serialize` for every generic `Message` |
| Complete parser specification | `parse_iff_spec` and `seed_parse_iff_spec` characterize exactly which strings each executable parser accepts, against `Spec.Encoding` and `Spec.Seed`: printable ASCII, uniform case, literal prefix/header/alphabet, checksum equations and variant bounds, and application lengths. The specifications do not invoke the parsers or checksum constructors. Uppercase acceptance and `parse_serializeUpper`/`seed_string_upper_roundtrip` are proved |
| Checksum construction | `Checksum.verify_create` for every successful regular/long construction; `encoded_seed_checksum_valid` proves `Encoding.validChecksum (Seed.encodeString …) = true`; exact lengths, selection, and bounds also proved |
| Initialization through recovery | `initializeFresh_valid` and `initializeExisting_valid` prove initialization and source validation succeed for all admissible raw inputs. `initializeFresh_recover` and `initializeExisting_recover` connect these initializers to public recovery from every distinct threshold-sized non-secret output selection; the existing-secret result is the exact original message |
| Recovery of generated shares | `recover_generated_shares` proves the public `Shares.recover` function returns the source's secret evaluation from any threshold-sized, distinct, non-secret selection generated by a validated source; `recover_generated_existing_secret` returns a secret already present in that source exactly, including metadata and padding |
| Shamir secrecy | `initializeExisting_secrecy` proves that any two secrets with the same public metadata and payload length give identical distributions for observation lists of fewer-than-threshold non-secret indices, with duplicates allowed and counted toward the list-length bound. `initializeFresh_secrecy` proves equal joint counts for any two fresh secret payloads and every event on those observed messages. Both use the actual initialization/validation/interpolation pipeline with independently uniform full-symbol entropy, including padding |
| Reinterpolation | `Field.interpolate_reinterpolate` and `checked_reinterpolate_message` prove resampling at an equally sized distinct set of indices preserves interpolation at every target, for arbitrary field values and generic payload lengths |
| Interpolation at an existing index | `interpolate_at_existing` proves the checked message API behavior; `Field.interpolate_existing` independently proves the scalar Lagrange formula returns the existing value |
| Checksum error detection (BCH distance) | `GF1024.regular_detection` and `GF1024.long_detection`: any two equal-length valid strings within a checksum period that differ in at most eight symbols are identical — the BIP's "guarantees detection of any error changing at most 8 symbols" claim, proved rather than assumed. `verifyRegular_detects`/`verifyLong_detects` package the same claim for the executable verifiers |
| Checksum correction uniqueness | `GF1024.regular_substitutions_unique`/`long_substitutions_unique`: any two equal-length valid strings within distance four of a common received string are identical. If the original is within that radius, every valid correction within the radius is the original. `GF1024.regular_erasures_unique`/`long_erasures_unique`: two valid strings agreeing at every position outside an erasure set of at most eight positions are identical — at most one valid completion of an erased string exists |
| Burst-erasure uniqueness | `regular_burst_valid`/`long_burst_valid`: two equal-length valid strings agreeing outside a consecutive window of at most 13 (regular) or 15 (long) symbols are identical — the BIP's "up to 13/15 consecutive erasures" claim, proved. The register recurrence is shown to perform polynomial reduction modulo the generator (`regular_bridge`/`long_bridge`), so an equal residue makes the generator divide the difference polynomial; a burst-shaped difference is `xˢ·W` with `W` shorter than the generator, forcing `W = 0` via the monic-product support theorem in `Codex32Proofs.Poly` |
| Checksum counting (random-error probability) | `regular_valid_count`/`long_valid_count`: exactly `32^(n-13)` / `32^(n-15)` strings of length `n` have the checksum residue — every prefix determines its tail uniquely (existence by the constructor, uniqueness by the burst theorem). `regular_valid_fraction`/`long_valid_fraction`: valid strings are exactly one `32^13`-th / `32^15`-th of all strings, so a uniformly random string passes verification — and a uniformly random error goes undetected — with probability exactly `2^-65` / `2^-75`; `regular_failure_below_bip`/`long_failure_below_bip` confirm these are below the BIP's 3-in-10²⁰ / 3-in-10²³ bounds |
| Checksum design re-derivation | `GF1024.beta_pow_period`/`gamma_pow_period` prove the appendix's root elements have the exact orders 93 and 1023 (finite kernel computation, no proper divisor is a period); `regular_generator_rederived`/`long_generator_rederived` prove the products `∏(x + βⁱ)` and `∏(x + γʲ)` have exactly the printed GF(32) coefficients; `regular_consecutive_roots`/`long_consecutive_roots` confirm the eight consecutive powers needed for the BCH bound |
| Supporting invariants | Alphabet and threshold conversion round trips, supported payload lengths, bit reconstruction, field laws, polynomial degree bounds, and polynomial root/evaluation uniqueness |

The error-detection proof decomposes the claim into independently verified pieces: the extension field `GF(1024) = GF(32)[ζ]/(ζ² + ζ + 1)` with its laws (`GF1024.lean`), the multiplicative orders and generator polynomials re-derived from first principles (no checksum constant is trusted from the BIP), a Vandermonde/uniqueness argument (`vandermonde`), the BCH bound specialized to weight ≤ 8 at eight consecutive roots (`sparse_zero`), and a bridge showing each polymod register evaluates to `xⁿ·init + M + g·Q` at every `x : GF1024` (`telescope`/`telescope_long`), so equal-length valid strings agree at every root of `g`. The correction-uniqueness claims are short corollaries of the detection theorem: the substitution case chains two distance-4 bounds through the triangle inequality on differing-position sets, and the erasure case bounds the differing-position count by the erasure-set size, both via a shared nodup-subset counting lemma.

The recovery theorems cover every supported threshold (2–9), any order of recovery indices, and long shares. Initialization is included: admissible fresh inputs use a supported master-seed payload size; existing-secret inputs may use any generic payload size. Both helpers are proved to produce valid sources, and validation of every generated recovery set is also proved to succeed. Existing secrets are recovered exactly, including padding. The earlier `recover_generated_threshold_two_message` theorem also retains a direct create/derive/recover sequence, and the official vector 2 API result remains kernel-checked in `Codex32Test.VectorProofs`. The general proof collection does not import test fixtures.

The secrecy proof compares full distributions, including correlations between payload columns and shares. A polynomial mask changes the secret while vanishing at every observed index; adding its evaluations to the random payloads is an involution. `Uniform.allEntropy` enumerates every entropy matrix exactly once, with cardinality `32^(rows * columns)`. The mask permutes this sample space, so every event on the observed messages has the same count for either secret, with the same positive probability denominator. This covers fixed observation lists of non-secret indices whose total length is below the threshold, including repeated indices and initial random-share indices. Repeated indices count toward this length bound; no distinctness hypothesis is required. Threshold, identifier, payload length and selected indices are public; full symbol uniformity is an explicit randomness model, not a claim about an external random generator.

## Build and test

With Lean's `elan` installed, the pinned `lean-toolchain` selects the compiler:

```sh
lake build
lake test
lake build Codex32Proofs Codex32Test.VectorProofs
lake env lean scripts/Audit.lean
bash scripts/test-cli.sh
```

In the original workspace, the official toolchain was also downloaded locally:

```sh
export PATH="$PWD/.toolchain/bin:$PATH"
```

`lake build` builds only the pure library. `lake test` builds and runs the native test executable, failing on any mismatch. Proof checking is explicit and separate. The audit covers the general proofs and the official-vector proof, rejecting project declarations that depend on admissions, native proof evaluation, or nonstandard axioms; it is not a secret scanner. The CLI script builds the test harness and runs its stream, entropy-adapter, and integration tests. All five checks run in GitHub Actions.

### CLI test harness

The CLI is a test harness for exercising the library through text input and output. It is not a reference CLI or a supported wallet application. Use public, disposable fixtures when running it.

Build with `lake build codex32_test_cli`; the executable is `.lake/build/bin/codex32_test_cli`. It uses only Lean and its bundled libraries, with no custom native binding or additional build dependencies. `bash scripts/test-cli.sh` builds and exercises it automatically.

For a manual check using the public seed from BIP 93 vector 3:

```sh
printf '%s\n' ffeeddccbbaa99887766554433221100 |
  .lake/build/bin/codex32_test_cli encode cash 3 |
  .lake/build/bin/codex32_test_cli decode
```

The output is the original hexadecimal fixture. `--help` describes the four test commands: `encode`, `decode`, `split`, and `recover`. Test inputs are piped or redirected through stdin; interactive terminal entry is rejected, reads are bounded, and LF/CRLF endings are accepted. Validation and entropy failures produce no partial share output.

`split` emits shares in Bech32 field-value order (`q,p,z,r,y,…`), skipping the secret index `s`. This order is a harness convention. Initial random shares use `a,c,d,…` as required by BIP 93; when an output index matches one of them, that original share is included unchanged and counts toward `COUNT`.

On Linux and macOS, the harness reads `/dev/urandom` for its split tests and maps each byte to one uniform five-bit symbol, including random-share padding bits. The host's OS random generator must already be initialized. Unsupported hosts and entropy read failures abort without a fallback. An external entropy source remains future work; the library already accepts caller-supplied random payloads. Integration tests run on Linux.

### Vector coverage

All Codex32 portions of test vectors 1–8 and all invalid examples pass:

- 34 distinct valid strings: 26 secret encodings and 8 shares, preserving all official padding variants.
- All 55 invalid strings, including checksum, variant, length, threshold, prefix, and case failures.
- Exact expected seed bytes, serialization, and checksum symbols.
- Fresh/existing-secret generation and every official derived share.
- All three pairs from vector 2 and all ten three-share subsets from vector 3.

The library suite currently reports **36,294 checks**. Additional tests cover every supported seed size and threshold, all 31 share indices, replaced-share recovery, GF(32) identities, interpolation, structured errors, rejected metadata mismatches, generic existing-secret payloads, and checksum boundaries through expanded length 1023. Oversized ASCII and UTF-8 inputs exercise rejection before character conversion.

The CLI test harness has **113 integration checks** covering official encodings/recovery, all supported seed sizes, long shares at thresholds 2–9 with every threshold-sized subset of `k+1` outputs, all 31 indices, and malformed/oversized input. Adapter tests cover bounded consumption, short reads, entropy EOF and read failures, and the uniform byte-to-symbol mapping.

The BIP's example `xprv` strings are retained as fixture metadata. Computing BIP 32 extended private keys requires HMAC-SHA512 and curve/key serialization outside BIP 93; these downstream values are **not tested** here. The Codex32 layer is tested through the exact master-seed bytes those examples supply.

## Specification revision

Implemented the official specification fetched on **2026-09-18**, at bitcoin/bips commit `55083d36ddebcd2a039135a2f4ee74917a5803d3`. The last change to BIP 93 itself is `5117f5831bcbf0485949e5951d2954b792eded28` (2026-08-26).

This revision permits master seeds of **16, 20, 24, 28, 32, or 64 bytes**. It selects regular/long checksums using the expanded codeword length, including five values for the `ms` HRP. Earlier BIP revisions accepted other seed sizes. The exact upstream text and its hash are in [`spec/`](spec/REVISION.md).

## Specification boundaries and decisions

- **Generic vs. master-seed lengths:** “codex32” defines a generic format; “Master seed format” and the inline `ms32_decode` impose application sizes. Separate parsing APIs preserve both meanings. Generic payloads can contain 0–997 symbols; master-seed payloads contain 26, 32, 39, 45, 52, or 103. For example, a valid 69-symbol payload serializes to 91 characters and is accepted by `Encoding.parse`, but rejected by `Seed.parse` and the BIP's application-specific `ms32_decode`. The reference `ms32_encode` and `ms32_decode` are therefore not unrestricted generic-format inverses.
- **Existing-index interpolation:** “Generating Shares” requires a fresh target. The optimized `bech32_lagrange` in “Recovering Secret” yields zero weights at an existing target because it multiplies by zero and uses `INV[0] = 0`. `Field.lagrange` uses the standard product excluding the current index, extending evaluation to existing indices. `Shares.interpolate` returns the validated existing message directly. `Shares.derive` enforces the BIP's fresh-target condition. This extension is explicit, not behavior attributed to the reference snippet.
- **Arbitrary padding:** “Master seed format” permits nonzero discarded bits. Decoding retains every complete byte and discards at most four bits. Re-encoding bytes with default zero padding need not reproduce the original text or derived shares. Parsed `Message`s preserve the full payload, so serialization and share recovery preserve padding.
- **Random-share padding:** Arbitrary padding of a supplied secret does not permit fixed padding in the random input shares. For example, encoding 16 random bytes with zero padding produces a final symbol whose low two bits are fixed; it is not a uniform GF(32) symbol. Both initializers' secrecy guarantees require independent uniform symbols across all random payloads, including padding. A supplied existing secret may still use zero or any other permitted padding.
- **Checksum helper bounds:** The inline long-only verifier checks the upper bound; `Checksum.verifyLong` follows it. It does not enforce the minimum length for selecting the long variant. For example, appending a long checksum to the body `0qqqqs` followed by 26 `q` symbols produces 47 data symbols (52 expanded values): the long-only verifier accepts, while `Checksum.verify` rejects. Use `Checksum.verify` for the required automatic selection, which also rejects expanded lengths 94, 95, and greater than 1023. The checked constructor rejects oversized codewords, although the raw Python creation helper has no explicit maximum check.
- **Low-level checksum constructors:** `Checksum.createRegular` and `Checksum.createLong` remain public primitives. Their callers choose the variant and enforce its bounds. Prefer `Checksum.create` or `Encoding.serialize` for automatic selection.
- **Parser input bound:** The maximum printed string is 1,021 ASCII characters: the `ms1` prefix plus at most 1,018 data symbols. `Encoding.parse` rejects larger UTF-8 byte sizes before allocating character lists or normalizing case. Non-ASCII input within this bound is rejected separately.
- **Zero inversion:** `Field.inv 0 = 0` follows the BIP table; it is not a multiplicative inverse. Validated share operations require distinct indices and avoid zero denominators.
- **Error correction:** Invalid checksums are rejected. Optional correction suggestions from “Error Correction” are not implemented; the BIP does not specify an algorithm, and correction is outside this minimal encoder/decoder. No correction is applied implicitly.
- **Identifiers:** The BIP deliberately does not specify identifier selection. Callers choose them; the implementation checks syntax only.
- **Reference-code equivalence:** The BIP's helper interpolates every position of a complete data part, including its checksum. This library interpolates payloads, constructs the header, and regenerates the checksum when serializing. Official-vector interoperability is tested, but a general theorem equating these full results remains unproved. Likewise, the algebraic equivalence of the optimized BIP weights and our standard Lagrange product for pairwise-distinct source indices and a fresh target has not been formalized directly.
- **Reference probability typo:** The pinned BIP rationale prints `1 - 2^65`, evidently missing the negative exponent in `1 - 2^-65`. Correcting that expression is an editorial change, not a proof of the random-error probability claims.

[Issue #1](https://github.com/stutxo/codex32_lean/issues/1) tracks these reference-helper clarifications, reproducible examples, and the remaining equivalence proof work. The vendored BIP snapshot is retained unmodified.

## Remaining assumptions and limits

Uniform, independent entropy and appropriate identifier selection remain environmental/caller obligations. The test harness trusts the host OS random source; its initialization and entropy quality are not proved. Checksum validity does not authenticate a share or detect a deliberately forged set. GF arithmetic uses variable-time `Nat` operations and immutable lists; constant-time execution and secure memory erasure are not provided. The BCH code's guaranteed 8-symbol error detection at periods 93 and 1023 is proved (`regular_detection`/`long_detection`), as are uniqueness of correction within four substitutions or eight erasures, uniqueness of completion within 13/15 consecutive erasures (`regular_burst_valid`/`long_burst_valid`), and the exact random-error failure probabilities `2^-65`/`2^-75` (`regular_valid_fraction`/`long_valid_fraction`). No correction algorithm is implemented or verified. Shamir secrecy is proved under the stated uniform-symbol model. Side-channel resistance, CLI/OS correctness, and downstream wallet correctness are not established by these proofs. The declarative parser specification has been reviewed against the pinned BIP; that interpretation of the prose remains a human review boundary.

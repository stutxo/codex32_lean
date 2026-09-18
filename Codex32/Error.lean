import Std

namespace Codex32

/-- Stable machine-readable failures. Human-readable wording is kept in one place. -/
inductive Error where
  | invalidCharacter | invalidThreshold | invalidIdentifierLength
  | payloadTooLong | codewordTooLong | zeroThresholdIndex
  | nonAscii | mixedCase | invalidPrefix | invalidLength | incompleteHeader | invalidChecksum
  | incompletePayload | unsupportedSeedLength | unsupportedPayloadLength | expectedSecret
  | invalidShareThreshold | emptyShareSet | wrongShareCount
  | mismatchedThreshold | mismatchedIdentifier | mismatchedLength | duplicateIndex
  | targetAlreadyPresent | secretInRecovery | wrongEntropyCount | entropyRequired
  deriving Repr, DecidableEq, BEq

def Error.toString : Error → String
  | .invalidCharacter => "invalid Bech32 character"
  | .invalidThreshold => "threshold must be 0 or between 2 and 9"
  | .invalidIdentifierLength => "identifier must contain exactly four Bech32 characters"
  | .payloadTooLong => "Codex32 payload exceeds 997 symbols"
  | .codewordTooLong => "Codex32 string exceeds 1021 ASCII characters (1018 data symbols)"
  | .zeroThresholdIndex => "threshold 0 requires the secret index s"
  | .nonAscii => "Codex32 requires printable ASCII"
  | .mixedCase => "mixed case Codex32 string"
  | .invalidPrefix => "expected ms1 prefix"
  | .invalidLength => "invalid expanded Codex32 length"
  | .incompleteHeader => "incomplete Codex32 header"
  | .invalidChecksum => "invalid Codex32 checksum"
  | .incompletePayload => "more than four incomplete payload bits"
  | .unsupportedSeedLength => "master seed must contain 16, 20, 24, 28, 32, or 64 bytes"
  | .unsupportedPayloadLength => "unsupported master-seed payload length"
  | .expectedSecret => "a secret with index s is required"
  | .invalidShareThreshold => "sharing requires a threshold from 2 through 9"
  | .emptyShareSet => "the share set is empty; exactly the threshold number of strings is required"
  | .wrongShareCount => "the number of strings must equal the threshold exactly"
  | .mismatchedThreshold => "share thresholds differ"
  | .mismatchedIdentifier => "share identifiers differ"
  | .mismatchedLength => "payload lengths differ"
  | .duplicateIndex => "share indices must be distinct"
  | .targetAlreadyPresent => "derivation requires a fresh index"
  | .secretInRecovery => "recovery inputs must be shares, not secrets"
  | .wrongEntropyCount => "incorrect number of random payloads for the threshold"
  | .entropyRequired => "random payloads are required"

instance : ToString Error := ⟨Error.toString⟩

end Codex32

import Codex32.Seed
import Codex32.Shares
import Codex32Test.Vectors

/-! Executable tests, deliberately separate from the formal proofs. -/
namespace Codex32.Tests

abbrev TestM := StateT Nat (Except String)

local instance [BEq α] : BEq (Except Error α) where
  beq a b := match a, b with
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _, _ => false

private def check (label : String) (condition : Bool) : TestM Unit := do
  if !condition then throw label
  modify (· + 1)

private def checkEq [BEq α] [Repr α] (label : String) (actual expected : α) : TestM Unit :=
  check s!"{label}: expected {repr expected}, got {repr actual}" (actual == expected)

private def require (label : String) (result : Except Error α) : TestM α :=
  match result with
  | .ok value => pure value
  | .error error => throw s!"{label}: {error}"

private def rejected (result : Except Error α) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

private def nibble (c : Char) : Nat := "0123456789abcdef".toList.idxOf c

private def fromHex (hex : String) : List UInt8 :=
  let cs := hex.toList
  (List.range (cs.length / 2)).map fun i =>
    UInt8.ofNat (16 * nibble cs[2*i]! + nibble cs[2*i+1]!)

private def toHex (bytes : List UInt8) : String :=
  let cs := "0123456789abcdef".toList
  String.ofList (bytes.flatMap fun b => [cs[b.toNat / 16]!, cs[b.toNat % 16]!])

private def testAlphabet : TestM Unit := do
  for n in List.range 32 do
    let value := Symbol.ofNat n
    checkEq "alphabet round trip" (Alphabet.decode (Alphabet.encode value)) (some value)
    checkEq "uppercase alphabet round trip"
      (Alphabet.decode (Alphabet.encode value).toUpper) (some value)
  for c in "bio1!?é \n".toList do
    checkEq s!"non-Bech32 character {c}" (Alphabet.decode c) none
  for n in List.range 12 do
    checkEq s!"threshold {n}" (rejected (Threshold.ofNat n)) (!(n == 0 || (2 ≤ n && n ≤ 9)))
  check "short identifier rejected" (rejected (Identifier.parse "abc"))
  check "long identifier rejected" (rejected (Identifier.parse "abcde"))
  check "invalid identifier rejected" (rejected (Identifier.parse "b???"))

private def testOfficialVectors : TestM Unit := do
  checkEq "official valid fixture count" Vectors.validStrings.length 34
  checkEq "official secret fixture count" Vectors.secrets.length 26
  checkEq "official invalid fixture count" Vectors.invalid.length 55
  for encoded in Vectors.validStrings do
    let message ← require "official generic parse" (Encoding.parse encoded)
    let _ ← require "official master-seed parse" (Seed.parse encoded)
    checkEq "official serialization" (Encoding.serialize message) encoded.toLower
    let data ← require "official alphabet" (Alphabet.decodeList (String.ofList (encoded.toLower.toList.drop 3)))
    check "official checksum verification" (Checksum.verify data)
    let checksumLength := if encoded.length = 127 then 15 else 13
    let body := data.take (data.length - checksumLength)
    let checksum ← require "official checksum construction" (Checksum.create body)
    checkEq "official checksum exact value" (body ++ checksum) data
    let _ ← require "case conversion" (Seed.parse encoded.toUpper)
    pure ()
  for vector in Vectors.secrets do
    let message ← require vector.label (Seed.parse vector.encoded)
    let seed ← require vector.label (Seed.decode message)
    checkEq s!"{vector.label} decoded seed" (toHex seed.bytes) vector.hex
    let expected ← require "fixture seed length" (Seed.ofBytes (fromHex vector.hex))
    let encoded := Seed.encode expected message.identifier message.threshold (Symbol.ofNat vector.padding)
    checkEq s!"{vector.label} encoded seed with prescribed padding"
      (Encoding.serialize encoded) vector.encoded.toLower
    let decoded ← require "seed round trip" (Seed.decode encoded)
    checkEq "seed round trip bytes" decoded.bytes expected.bytes
  for vector in Vectors.invalid do
    check s!"official invalid ({vector.category}): {vector.encoded}" (rejected (Seed.parse vector.encoded))
    if vector.category != "improper length" then
      check s!"generic invalid ({vector.category})" (rejected (Encoding.parse vector.encoded))
  for encoded in Vectors.validShares do
    check "a share alone cannot be decoded as a secret" (rejected (Seed.decodeString encoded))

private def testOfficialShares : TestM Unit := do
  let a ← require "vector 2 a" (Seed.parse Vectors.vector2a)
  let c ← require "vector 2 c" (Seed.parse Vectors.vector2c)
  let d ← require "derive vector 2 d" (Shares.derive [a, c] (Alphabet.decode 'd').get!)
  checkEq "vector 2 derived d" (Encoding.serialize d) Vectors.vector2d.toLower
  for pair in [[a, c], [a, d], [c, d]] do
    let secret ← require "vector 2 recovery" (Shares.recover pair)
    checkEq "vector 2 recovered secret" (Encoding.serialize secret) Vectors.vector2s.toLower
  let fresh ← require "vector 2 fresh shares" (Shares.initializeFresh a.threshold a.identifier [a.payload, c.payload])
  checkEq "fresh initializer reproduces vector 2"
    (fresh.map Encoding.serialize) [Vectors.vector2a.toLower, Vectors.vector2c.toLower]
  let secret ← require "vector 3 secret" (Seed.parse Vectors.vector3s)
  let a ← require "vector 3 a" (Seed.parse Vectors.vector3a)
  let c ← require "vector 3 c" (Seed.parse Vectors.vector3c)
  let initial ← require "vector 3 existing shares" (Shares.initializeExisting secret [a.payload, c.payload])
  checkEq "existing initializer reproduces vector 3"
    (initial.map Encoding.serialize) [Vectors.vector3s, Vectors.vector3a, Vectors.vector3c]
  for (index, expected) in [('d', Vectors.vector3d), ('e', Vectors.vector3e), ('f', Vectors.vector3f)] do
    let share ← require "vector 3 derivation" (Shares.derive initial (Alphabet.decode index).get!)
    checkEq s!"vector 3 derived {index}" (Encoding.serialize share) expected
  let shares ← require "vector 3 shares" ([Vectors.vector3a, Vectors.vector3c,
    Vectors.vector3d, Vectors.vector3e, Vectors.vector3f].mapM Seed.parse)
  -- All ten unordered threshold subsets, as required by the vector's prose.
  for i in List.range 5 do
    for j in List.range 5 do
      for k in List.range 5 do
        if i < j && j < k then
          let recovered ← require "vector 3 subset recovery"
            (Shares.recover [shares[i]?.getD a, shares[j]?.getD a, shares[k]?.getD a])
          checkEq "vector 3 all threshold subsets" (Encoding.serialize recovered) Vectors.vector3s
  for share in initial do
    let interpolated ← require "existing-index interpolation" (Shares.interpolate initial share.index)
    checkEq "existing-index identity" (Encoding.serialize interpolated) (Encoding.serialize share)
    check "derive requires a fresh index" (rejected (Shares.derive initial share.index))

private def testChecksumBoundaries : TestM Unit := do
  for (length, expected) in [(88, some 13), (89, none), (90, none),
      (91, some 15), (1018, some 15), (1019, none)] do
    checkEq s!"checksum selection length {length}" (Checksum.checksumLength length) expected
  for (length, expected) in [(0, 13), (75, 13), (76, 15), (1003, 15)] do
    for symbol in [Symbol.ofNat 0, Symbol.ofNat 31] do
      let data := List.replicate length symbol
      let checksum ← require "checksum boundary creation" (Checksum.create data)
      checkEq "checksum boundary size" checksum.length expected
      check "checksum boundary verification" (Checksum.verify (data ++ checksum))
  check "checksum creation over maximum" (rejected (Checksum.create (List.replicate 1004 0)))
  for length in [76, 77] do
    let data := List.replicate length (Symbol.ofNat 17)
    check "forbidden expanded length rejects even correct regular residue"
      (!(Checksum.verify (data ++ Checksum.createRegular data)))
  for length in [73, 74, 75] do
    let data := List.replicate length (Symbol.ofNat 6)
    check "wrong or forbidden variant rejected" (!(Checksum.verify (data ++ Checksum.createLong data)))

private def testField : TestM Unit := do
  let elements := (List.range 32).map Symbol.ofNat
  for a in elements do
    checkEq "field addition cancellation" (Field.add a a) 0
    checkEq "field multiplicative identity" (Field.mul a 1) a
    checkEq "field zero product" (Field.mul a 0) 0
    if a != 0 then checkEq "field inverse" (Field.mul a (Field.inv a)) 1
    for b in elements do
      checkEq "field multiplication commutes" (Field.mul a b) (Field.mul b a)
      for c in elements do
        checkEq "field multiplication distributes"
          (Field.mul a (Field.add b c)) (Field.add (Field.mul a b) (Field.mul a c))
  -- Independently chosen degree-two polynomial, evaluated at all field points.
  let polynomial := fun x => Field.add 7 (Field.add (Field.mul 11 x) (Field.mul 19 (Field.mul x x)))
  let points := ([0, 1, 31] : List Symbol).map fun x => (x, polynomial x)
  for x in elements do
    checkEq "quadratic interpolation across all field points" (Field.interpolate points x) (polynomial x)

private def testGeneration : TestM Unit := do
  let identifier ← require "generation identifier" (Identifier.parse "seed")
  let indices := ((List.range 32).map Symbol.ofNat).filter (· != 16)
  for size in [16, 20, 24, 28, 32, 64] do
    let bytes := (List.range size).map fun i => UInt8.ofNat (i * 197 + size)
    let seed ← require "generated test seed" (Seed.ofBytes bytes)
    for k in List.range 8 do
      let threshold ← require "generated test threshold" (Threshold.ofNat (k + 2))
      let secret := Seed.encode seed identifier threshold 31
      let payloads := (List.range (k+1)).map fun row =>
        (List.range secret.payload.length).map fun column =>
          Symbol.ofNat (row * 19 + column * 7 + column * column)
      let initial ← require "existing initialization matrix" (Shares.initializeExisting secret payloads)
      let shares ← require "all 31 distributable share indices"
        (indices.mapM (Shares.interpolate initial))
      checkEq "all share indices generated" shares.length 31
      for share in shares do
        check "generated share checksum" (Encoding.validChecksum (Encoding.serialize share))
      for subset in [shares.take (k+2), shares.reverse.take (k+2)] do
        let recovered ← require "generated threshold subset recovery" (Shares.recover subset)
        checkEq "generated full secret, including padding"
          (Encoding.serialize recovered) (Encoding.serialize secret)
        let decoded ← require "generated recovered seed" (Seed.decode recovered)
        checkEq "generated secret bytes" decoded.bytes bytes
      let freshPayloads := payloads ++ [secret.payload]
      let fresh ← require "fresh initialization matrix"
        (Shares.initializeFresh threshold identifier freshPayloads)
      let recovered ← require "fresh initial recovery" (Shares.recover fresh)
      let extra ← require "fresh extra share" (Shares.derive fresh 0)
      let changedSubset := extra :: fresh.drop 1
      let recoveredAgain ← require "fresh replaced-share recovery" (Shares.recover changedSubset)
      checkEq "fresh recovery independent of chosen shares"
        (Encoding.serialize recoveredAgain) (Encoding.serialize recovered)

private def testValidation : TestM Unit := do
  let a ← require "validation a" (Seed.parse Vectors.vector2a)
  let c ← require "validation c" (Seed.parse Vectors.vector2c)
  let d ← require "validation d" (Seed.parse Vectors.vector2d)
  let secret ← require "validation secret" (Seed.parse Vectors.vector2s)
  let identifier ← require "other identifier" (Identifier.parse "test")
  let threshold ← require "other threshold" (Threshold.ofNat 3)
  let wrongThreshold ← require "changed threshold"
    (Message.create threshold c.identifier c.index c.payload)
  let wrongIdentifier ← require "changed identifier"
    (Message.create c.threshold identifier c.index c.payload)
  let wrongLength ← require "changed length"
    (Message.create c.threshold c.identifier c.index (List.replicate 32 0))
  for (label, set) in [("empty", []), ("too few", [a]), ("too many", [a,c,d]),
      ("duplicate index", [a,a]), ("threshold mismatch", [a,wrongThreshold]),
      ("identifier mismatch", [a,wrongIdentifier]), ("length mismatch", [a,wrongLength]),
      ("secret as a share", [secret,c])] do
    check s!"recovery rejects {label}" (rejected (Shares.recover set))
  for (label, payloads) in [("too few", [a.payload]),
      ("too many", [a.payload, a.payload, a.payload]),
      ("unequal lengths", [a.payload, List.replicate 32 0]),
      ("unsupported length", [List.replicate 27 0, List.replicate 27 0])] do
    check s!"fresh generation rejects {label}"
      (rejected (Shares.initializeFresh a.threshold a.identifier payloads))
  check "fresh generation rejects threshold zero"
    (rejected (Shares.initializeFresh .unshared a.identifier []))
  check "existing generation rejects a share"
    (rejected (Shares.initializeExisting a [c.payload]))
  check "existing generation rejects wrong entropy count"
    (rejected (Shares.initializeExisting secret []))
  check "existing generation rejects wrong entropy length"
    (rejected (Shares.initializeExisting secret [List.replicate 32 0]))
  let unshared ← require "unshared test secret"
    (Message.create .unshared identifier 16 a.payload)
  check "interpolation rejects threshold zero" (rejected (Shares.interpolate [unshared, unshared] 0))
  check "existing generation rejects threshold zero"
    (rejected (Shares.initializeExisting unshared []))
  check "zero threshold cannot create a share"
    (rejected (Message.create .unshared identifier 0 a.payload))
  for size in List.range 67 do
    checkEq s!"supported seed size {size}"
      (!(rejected (Seed.ofBytes (List.replicate size 0))))
      ([16, 20, 24, 28, 32, 64].contains size)
  for length in [0, 26, 27, 69, 70, 71, 997] do
    let message ← require "generic length construction"
      (Message.create .unshared identifier 16 (List.replicate length 31))
    let encoded := Encoding.serialize message
    let parsed ← require "generic length parsing" (Encoding.parse encoded)
    checkEq "generic length round trip" parsed.payload message.payload
    checkEq "application restricts generic sizes" (!(rejected (Seed.parse encoded))) (length == 26)
  check "generic over-maximum payload rejected"
    (rejected (Message.create .unshared identifier 16 (List.replicate 998 0)))
  -- Existing secrets use application-specific payloads (BIP "For an existing secret").
  for length in [0, 3, 69, 70, 997] do
    let genericSecret ← require "generic secret"
      (Message.create a.threshold identifier 16 (List.replicate length 31))
    let initial ← require "generic existing-secret generation"
      (Shares.initializeExisting genericSecret [List.replicate length 9])
    let extra ← require "generic derived share" (Shares.derive initial 24)
    let recovered ← require "generic recovery" (Shares.recover (initial.drop 1 ++ [extra]))
    checkEq "generic existing-secret payload recovery" recovered.payload genericSecret.payload
  for s in ["", "ms1", "ms10", " ms1", "ms1\n", "ms1é", "ms1\u007f",
      "ms1b", "ms1i", "ms1o", "ms11"] do
    check "malformed generic text rejected" (rejected (Encoding.parse s))
  for length in [1, 3, 6] do
    check "excess incomplete payload bits rejected"
      (rejected (Bits.decode (List.replicate length 0)))

private def testInputBoundsAndErrors : TestM Unit := do
  let id ← require "boundary identifier" (Identifier.parse "test")
  -- All three final valid printed lengths must survive the early byte-size guard.
  for length in [995, 996, 997] do
    let message ← require "maximum length message"
      (Message.create .unshared id 16 (List.replicate length 31))
    let encoded := Encoding.serialize message
    checkEq "printed versus data length" encoded.utf8ByteSize (length + 24)
    checkEq "maximum lengths still parse" (Encoding.parse encoded) (.ok message)
    checkEq "maximum uppercase lengths still parse" (Encoding.parse encoded.toUpper) (.ok message)
  let huge := String.ofList (List.replicate (2 * 1024 * 1024) 'x')
  checkEq "oversized input rejected before syntax processing"
    (Encoding.parse huge) (.error .codewordTooLong)
  checkEq "oversized identifier rejected before decoding"
    (Identifier.parse huge) (.error .invalidIdentifierLength)
  checkEq "first invalid printed length"
    (Encoding.parse (String.ofList (List.replicate 1022 'q'))) (.error .codewordTooLong)
  checkEq "UTF-8 size guard precedes character conversion"
    (Encoding.parse (String.ofList (List.replicate 511 'é'))) (.error .codewordTooLong)
  checkEq "short non-ASCII input has typed character error"
    (Encoding.parse "ms1é") (.error .nonAscii)
  checkEq "typed prefix error" (Encoding.parse "xs1") (.error .invalidPrefix)
  checkEq "typed checksum error"
    (Encoding.parse "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxve740yyge2ghq") (.error .invalidChecksum)
  checkEq "typed threshold error" (Threshold.ofNat 1) (.error .invalidThreshold)
  let a ← require "typed share errors" (Seed.parse Vectors.vector2a)
  checkEq "empty share set error" (Shares.recover []) (.error .emptyShareSet)
  checkEq "singleton count error" (Shares.recover [a]) (.error .wrongShareCount)
  checkEq "duplicate indices error" (Shares.recover [a,a]) (.error .duplicateIndex)

private def run : TestM Unit := do
  testAlphabet
  testOfficialVectors
  testOfficialShares
  testChecksumBoundaries
  testField
  testGeneration
  testValidation
  testInputBoundsAndErrors

end Codex32.Tests

def main : IO Unit := do
  match Codex32.Tests.run.run 0 with
  | .ok (_, count) => IO.println s!"PASS: {count} checks; all 34 valid and 55 invalid official BIP 93 strings."
  | .error error => throw (IO.userError s!"FAIL: {error}")

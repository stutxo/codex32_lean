import Codex32.Shares
import Codex32Test.Vectors

/-! Official-vector regression proofs checked by the Lean kernel. -/

namespace Codex32.Proofs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A complete official-vector recovery through the public parser, share
validator, interpolation, and serializer, checked by the Lean kernel. -/
theorem official_vector_two_recovery :
    (do
      let a ← Encoding.parse Vectors.vector2a
      let c ← Encoding.parse Vectors.vector2c
      let secret ← Shares.recover [a, c]
      pure (Encoding.serialize secret) : Except Error String).toOption =
      some Vectors.vector2s.toLower := by
  decide +kernel

end Codex32.Proofs

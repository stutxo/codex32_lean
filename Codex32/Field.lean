import Codex32.Alphabet

/-! GF(32) in the polynomial basis from BIP 93, "Recovering Secret".
The reducing polynomial is x^5 + x^3 + 1 (binary 101001 = 41).
These functions operate on five-bit symbols; no external arithmetic library is used.
-/

namespace Codex32.Field

def add (a b : Symbol) : Symbol := Symbol.ofNat (a.val ^^^ b.val)

private def mulLoop : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, result => result
  | n + 1, a, b, result =>
    let result := if b &&& 1 == 1 then result ^^^ a else result
    let doubled := a <<< 1
    let a := if doubled ≥ 32 then doubled ^^^ 41 else doubled
    mulLoop n a (b >>> 1) result

def mul (a b : Symbol) : Symbol := Symbol.ofNat (mulLoop 5 a.val b.val 0)

private def inverseTable : Array Nat := #[
  0, 1, 20, 24, 10, 8, 12, 29, 5, 11, 4, 9, 6, 28, 26, 31,
  22, 18, 17, 23, 2, 25, 16, 19, 3, 21, 14, 30, 13, 7, 27, 15]

/-- The BIP's inverse table is totalized with `inv 0 = 0`. This value is not
a multiplicative inverse; callers requiring division must exclude zero. -/
def inv (a : Symbol) : Symbol := Symbol.ofNat (inverseTable[a.val]?.getD 0)

/-- Division is totalized with `div a 0 = 0`, matching the inverse table. -/
def div (a b : Symbol) : Symbol := mul a (inv b)

/-- Lagrange basis weights. For pairwise distinct indices, these are
`∏ j ≠ i, (x + j) / (i + j)`. Characteristic two makes addition and
subtraction identical. At an existing index the weights are one-hot.

BIP 93's optimized inline formula has a removable singularity at existing
indices and evaluates to zero there. The BIP only calls it with fresh indices;
this standard product agrees there and defines the usual existing-index
extension. Repeated indices must be rejected by callers (see `Shares`). -/
def lagrange (indices : List Symbol) (target : Symbol) : List Symbol :=
  indices.map fun i =>
    indices.foldl (fun product j =>
      if i == j then product
      else mul product (div (add target j) (add i j))) 1

/-- Scalar interpolation; distinct indices are a precondition for its
interpretation as the unique polynomial of degree less than the point count. -/
def interpolate (points : List (Symbol × Symbol)) (target : Symbol) : Symbol :=
  ((lagrange (points.map Prod.fst) target).zip points).foldl
    (fun sum (weight, point) => add sum (mul weight point.2)) 0

end Codex32.Field

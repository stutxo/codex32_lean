import Codex32Proofs.Field

/-!
The extension field `GF(1024) = GF(32)[ζ]/(ζ² + ζ + 1)` from the BIP 93
appendix, the multiplicative orders of the two checksum root elements, and a
re-derivation of both printed generating polynomials. The irreducibility of
`ζ² + ζ + 1` over GF(32) and all finite order/divisor calculations are checked
by the kernel's `decide`; no native evaluation is used anywhere.
-/

namespace Codex32

/-- Element `a + b·ζ` of GF(1024), where `ζ² = ζ + 1`. -/
structure GF1024 where
  a : Symbol
  b : Symbol
  deriving DecidableEq, Repr

namespace GF1024

def zero : GF1024 := ⟨0, 0⟩
def one : GF1024 := ⟨1, 0⟩
def embed (x : Symbol) : GF1024 := ⟨x, 0⟩

def add (x y : GF1024) : GF1024 := ⟨Field.add x.a y.a, Field.add x.b y.b⟩

def mul (x y : GF1024) : GF1024 :=
  ⟨Field.add (Field.mul x.a y.a) (Field.mul x.b y.b),
   Field.add (Field.add (Field.mul x.a y.b) (Field.mul x.b y.a)) (Field.mul x.b y.b)⟩

def pow (x : GF1024) : Nat → GF1024
  | 0 => one
  | n + 1 => mul (pow x n) x

instance : Std.Associative (α := Symbol) Field.add := ⟨Field.add_assoc⟩
instance : Std.Commutative (α := Symbol) Field.add := ⟨Field.add_comm⟩

theorem ext {x y : GF1024} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; cases ha; cases hb; rfl

@[simp] theorem add_zero (x : GF1024) : add x zero = x := by
  cases x; apply ext <;> simp [add, zero, Field.add_zero]

@[simp] theorem zero_add (x : GF1024) : add zero x = x := by
  cases x; apply ext <;> simp [add, zero, Field.zero_add]

theorem add_comm (x y : GF1024) : add x y = add y x := by
  cases x; cases y; apply ext <;> simp [add, Field.add_comm]

theorem add_assoc (x y z : GF1024) : add (add x y) z = add x (add y z) := by
  cases x; cases y; cases z; apply ext <;> simp [add, Field.add_assoc]

instance : Std.Associative (α := GF1024) GF1024.add := ⟨GF1024.add_assoc⟩
instance : Std.Commutative (α := GF1024) GF1024.add := ⟨GF1024.add_comm⟩

@[simp] theorem add_self (x : GF1024) : add x x = zero := by
  cases x; apply ext <;> simp [add, zero, Field.add_self]

theorem add_eq_zero (x y : GF1024) : add x y = zero ↔ x = y := by
  constructor
  · intro h
    have h1 := congrArg GF1024.a h
    have h2 := congrArg GF1024.b h
    simp only [add, zero] at h1 h2
    exact ext ((Field.add_eq_zero _ _).mp h1) ((Field.add_eq_zero _ _).mp h2)
  · rintro rfl; exact add_self _

theorem add_left_comm (x y z : GF1024) : add x (add y z) = add y (add x z) := by
  rw [← add_assoc, add_comm x y, add_assoc]

theorem add_pair (a b c d : GF1024) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  rw [add_assoc, add_left_comm b c, ← add_assoc]

theorem add_cancel_left (a b : GF1024) : add a (add a b) = b := by
  rw [← add_assoc, add_self, zero_add]

theorem mul_comm (x y : GF1024) : mul x y = mul y x := by
  cases x with
  | mk xa xb =>
  cases y with
  | mk ya yb =>
  apply ext
  · show Field.add (Field.mul xa ya) (Field.mul xb yb) = Field.add (Field.mul ya xa) (Field.mul yb xb)
    rw [Field.mul_comm xa ya, Field.mul_comm xb yb]
  · show Field.add (Field.add (Field.mul xa yb) (Field.mul xb ya)) (Field.mul xb yb) =
      Field.add (Field.add (Field.mul ya xb) (Field.mul yb xa)) (Field.mul yb xb)
    rw [Field.mul_comm xa yb, Field.mul_comm xb ya, Field.mul_comm xb yb]
    ac_rfl

theorem mul_assoc (x y z : GF1024) : mul (mul x y) z = mul x (mul y z) := by
  cases x; cases y; cases z
  apply ext
  · simp only [mul, Field.mul_add, Field.add_mul, Field.mul_assoc]
    ac_rfl
  · simp only [mul, Field.mul_add, Field.add_mul, Field.mul_assoc]
    ac_rfl

@[simp] theorem one_mul (x : GF1024) : mul one x = x := by
  cases x; apply ext <;> simp [mul, one, Field.add_zero]

@[simp] theorem mul_one (x : GF1024) : mul x one = x := by
  cases x; apply ext <;> simp [mul, one, Field.mul_one, Field.mul_zero, Field.add_zero]

@[simp] theorem zero_mul (x : GF1024) : mul zero x = zero := by
  cases x; apply ext <;> simp [mul, zero]

@[simp] theorem mul_zero (x : GF1024) : mul x zero = zero := by
  cases x; apply ext <;> simp [mul, zero, Field.mul_zero]

theorem mul_add (x y z : GF1024) : mul x (add y z) = add (mul x y) (mul x z) := by
  cases x; cases y; cases z
  apply ext
  · simp only [mul, add, Field.mul_add]
    ac_rfl
  · simp only [mul, add, Field.mul_add]
    ac_rfl

theorem add_mul (x y z : GF1024) : mul (add x y) z = add (mul x z) (mul y z) := by
  rw [mul_comm, mul_add, mul_comm x z, mul_comm y z]

theorem mul_left_comm (x y z : GF1024) : mul x (mul y z) = mul y (mul x z) := by
  rw [← mul_assoc, mul_comm x y, mul_assoc]

/-- `ζ² + ζ + 1` has no root in GF(32); checked exhaustively by the kernel. -/
theorem zeta_irreducible : ∀ a : Symbol,
    Field.add (Field.add (Field.mul a a) a) 1 ≠ 0 := by
  decide +kernel

/-- The norm `a² + ab + b²` of a nonzero element is nonzero. -/
theorem norm_nonzero (x : GF1024) (h : x ≠ zero) :
    Field.add (Field.add (Field.mul x.a x.a) (Field.mul x.a x.b)) (Field.mul x.b x.b) ≠ 0 := by
  cases x with
  | mk a b =>
    dsimp only
    intro hn
    by_cases hb : b = 0
    · subst b
      simp only [Field.mul_zero, Field.add_zero] at hn
      have ha : a ≠ 0 := by
        intro hz; subst a; exact h rfl
      rcases (Field.mul_eq_zero _ _).mp hn with h1 | h1 <;> exact ha h1
    · have hs : Field.mul (Field.add (Field.add (Field.mul a a) (Field.mul a b)) (Field.mul b b))
          (Field.mul (Field.inv b) (Field.inv b)) = 0 := by
        rw [hn, Field.zero_mul]
      have hexpand : Field.mul (Field.add (Field.add (Field.mul a a) (Field.mul a b)) (Field.mul b b))
          (Field.mul (Field.inv b) (Field.inv b)) =
          Field.add (Field.add (Field.mul (Field.mul a (Field.inv b)) (Field.mul a (Field.inv b)))
            (Field.mul a (Field.inv b))) 1 := by
        have hbinv : Field.mul b (Field.inv b) = 1 := Field.mul_inv b hb
        calc Field.mul (Field.add (Field.add (Field.mul a a) (Field.mul a b)) (Field.mul b b)) (Field.mul (Field.inv b) (Field.inv b))
          _ = Field.add (Field.add (Field.mul (Field.mul a a) (Field.mul (Field.inv b) (Field.inv b)))
              (Field.mul (Field.mul a b) (Field.mul (Field.inv b) (Field.inv b))))
              (Field.mul (Field.mul b b) (Field.mul (Field.inv b) (Field.inv b))) := by
            simp only [Field.add_mul]
          _ = Field.add (Field.add (Field.mul (Field.mul a (Field.inv b)) (Field.mul a (Field.inv b)))
              (Field.mul a (Field.inv b))) 1 := by
            rw [show Field.mul (Field.mul a a) (Field.mul (Field.inv b) (Field.inv b)) =
                Field.mul (Field.mul a (Field.inv b)) (Field.mul a (Field.inv b)) by
              rw [Field.mul_assoc, ← Field.mul_assoc a (Field.inv b) (Field.inv b),
                Field.mul_left_comm a (Field.mul a (Field.inv b)) (Field.inv b)]]
            rw [show Field.mul (Field.mul a b) (Field.mul (Field.inv b) (Field.inv b)) =
                Field.mul a (Field.inv b) by
              rw [Field.mul_assoc, Field.mul_left_comm b (Field.inv b) (Field.inv b),
                ← Field.mul_assoc, hbinv, Field.mul_one]]
            rw [show Field.mul (Field.mul b b) (Field.mul (Field.inv b) (Field.inv b)) = 1 by
              rw [Field.mul_assoc, Field.mul_left_comm b (Field.inv b) (Field.inv b),
                ← Field.mul_assoc, hbinv, Field.mul_one]]
      rw [hexpand] at hs
      exact zeta_irreducible (Field.mul a (Field.inv b)) hs

/-- The field inverse, via the conjugate `a + b + b·ζ` over the norm. -/
def inv (x : GF1024) : GF1024 :=
  let n := Field.add (Field.add (Field.mul x.a x.a) (Field.mul x.a x.b)) (Field.mul x.b x.b)
  ⟨Field.mul (Field.add x.a x.b) (Field.inv n), Field.mul x.b (Field.inv n)⟩

theorem mul_inv (x : GF1024) (h : x ≠ zero) : mul x (inv x) = one := by
  cases x with
  | mk a b =>
    have hn : Field.add (Field.add (Field.mul a a) (Field.mul a b)) (Field.mul b b) ≠ 0 :=
      norm_nonzero ⟨a, b⟩ h
    have hmul : Field.mul (Field.add (Field.add (Field.mul a a) (Field.mul a b)) (Field.mul b b))
        (Field.inv (Field.add (Field.add (Field.mul a a) (Field.mul a b)) (Field.mul b b))) = 1 :=
      Field.mul_inv _ hn
    dsimp only [inv]
    apply ext
    · show Field.add (Field.mul a (Field.mul (Field.add a b) (Field.inv _)))
        (Field.mul b (Field.mul b (Field.inv _))) = 1
      rw [← Field.mul_assoc, ← Field.mul_assoc, ← Field.add_mul, Field.mul_add a a b, hmul]
    · show Field.add (Field.add (Field.mul a (Field.mul b (Field.inv _)))
        (Field.mul b (Field.mul (Field.add a b) (Field.inv _)))) (Field.mul b (Field.mul b (Field.inv _))) = 0
      rw [← Field.mul_assoc, ← Field.mul_assoc, ← Field.mul_assoc, ← Field.add_mul, ← Field.add_mul,
        Field.mul_add b a b, Field.mul_comm a b,
        show Field.add (Field.add (Field.mul b a) (Field.add (Field.mul b a) (Field.mul b b)))
          (Field.mul b b) = 0 by
          rw [← Field.add_assoc, Field.add_self, Field.zero_add, Field.add_self],
        Field.zero_mul]

theorem mul_eq_zero (x y : GF1024) : mul x y = zero ↔ x = zero ∨ y = zero := by
  constructor
  · intro hxy
    by_cases hx : x = zero
    · exact Or.inl hx
    · right
      have h1 : mul (inv x) (mul x y) = mul (inv x) zero := congrArg (mul (inv x)) hxy
      rw [mul_zero, ← mul_assoc, mul_comm (inv x) x, mul_inv x hx, one_mul] at h1
      exact h1
  · rintro (rfl | rfl) <;> simp

theorem mul_left_cancel (u v w : GF1024) (hu : u ≠ zero) (h : mul u v = mul u w) : v = w := by
  have h1 : mul (inv u) (mul u v) = mul (inv u) (mul u w) := congrArg (mul (inv u)) h
  rw [← mul_assoc, ← mul_assoc, mul_comm (inv u) u, mul_inv u hu, one_mul, one_mul] at h1
  exact h1

@[simp] theorem embed_zero : embed 0 = zero := rfl
@[simp] theorem embed_one : embed 1 = one := rfl

theorem embed_add (x y : Symbol) : embed (Field.add x y) = add (embed x) (embed y) := by
  apply ext <;> simp [embed, add, Field.add_zero]

theorem embed_mul (x y : Symbol) : embed (Field.mul x y) = mul (embed x) (embed y) := by
  apply ext <;> simp [embed, mul, Field.mul_zero, Field.add_zero, Field.add_self]

theorem embed_inj (x y : Symbol) (h : embed x = embed y) : x = y := congrArg GF1024.a h

@[simp] theorem pow_zero (x : GF1024) : pow x 0 = one := rfl
@[simp] theorem pow_succ (x : GF1024) (n : Nat) : pow x (n + 1) = mul (pow x n) x := rfl

theorem one_pow (n : Nat) : pow one n = one := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ, ih, one_mul]

theorem pow_add (x : GF1024) (m n : Nat) : pow x (m + n) = mul (pow x m) (pow x n) := by
  induction n with
  | zero => simp [pow_zero, mul_one]
  | succ n ih => rw [Nat.add_succ, pow_succ, pow_succ, ih, mul_assoc]

theorem pow_mul (x : GF1024) (m n : Nat) : pow x (m * n) = pow (pow x m) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, pow_add, ih, pow_succ]

theorem mul_pow (x y : GF1024) (n : Nat) : mul (pow x n) (pow y n) = pow (mul x y) n := by
  have step : ∀ a b x y : GF1024, mul (mul a x) (mul b y) = mul (mul a b) (mul x y) := by
    intro a b x y
    rw [mul_assoc, mul_left_comm x b y, ← mul_assoc]
  induction n with
  | zero => simp [pow_zero, mul_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, pow_succ, ← ih, step]

theorem pow_nonzero (x : GF1024) (hx : x ≠ zero) (n : Nat) : pow x n ≠ zero := by
  induction n with
  | zero => simp [pow_zero, one, zero]
  | succ n ih =>
    simp only [pow_succ]
    intro hz
    rcases (mul_eq_zero _ _).mp hz with h1 | h1
    · exact ih h1
    · exact hx h1

end GF1024

end Codex32

namespace Codex32

namespace GF1024

/-- `β := G·ζ`, the root element of the regular checksum's generating polynomial. -/
def beta : GF1024 := ⟨0, 8⟩

/-- `γ := E + X·ζ`, the root element of the long checksum's generating polynomial. -/
def gamma : GF1024 := ⟨25, 6⟩

theorem beta_ne_zero : beta ≠ zero := by decide +kernel
theorem gamma_ne_zero : gamma ≠ zero := by decide +kernel

/-- `β⁹³ = 1`, and no proper divisor of 93 is a period of `β`: the order of `β`
is exactly 93. Both sides are finite kernel calculations. -/
theorem beta_pow_period : pow beta 93 = one := by decide +kernel

theorem beta_proper_divisor : ∀ d : Nat, d < 93 → d ∣ 93 → pow beta d ≠ one := by
  decide +kernel

/-- `γ¹⁰²³ = 1`, and no proper divisor of 1023 is a period of `γ`. -/
theorem gamma_pow_period : pow gamma 1023 = one := by decide +kernel

theorem gamma_proper_divisor : ∀ d : Nat, d < 1023 → d ∣ 1023 → pow gamma d ≠ one := by
  decide +kernel

/-- If `eᴺ = 1` and no proper divisor of `N` is a period, then `eᵏ = 1` with
`k < N` forces `k = 0`. Euclidean descent; no gcd machinery required. -/
theorem pow_eq_one_of_lt (e : GF1024) (N : Nat) (_hN1 : 0 < N) (hN : pow e N = one)
    (hdiv : ∀ d : Nat, d < N → d ∣ N → pow e d ≠ one) :
    ∀ k : Nat, k < N → pow e k = one → k = 0 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hkN hk
    by_cases hk0 : k = 0
    · exact hk0
    · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hmod : pow e (N % k) = one := by
        have h1 : N = k * (N / k) + N % k := (Nat.div_add_mod N k).symm
        rw [h1, pow_add, pow_mul, hk, one_pow, one_mul] at hN
        exact hN
      have hlt : N % k < k := Nat.mod_lt _ hpos
      have hzero : N % k = 0 := ih (N % k) hlt (by omega) hmod
      have hdvd : k ∣ N := Nat.dvd_of_mod_eq_zero hzero
      exact absurd hk (hdiv k hkN hdvd)

/-- Powers of an element of exact order `N` are injective below `N`. -/
theorem pow_inj (e : GF1024) (N : Nat) (hN1 : 0 < N) (hN : pow e N = one)
    (hdiv : ∀ d : Nat, d < N → d ∣ N → pow e d ≠ one) (he : e ≠ zero)
    {a b : Nat} (ha : a < N) (hb : b < N) (h : pow e a = pow e b) : a = b := by
  have hmin := pow_eq_one_of_lt e N hN1 hN hdiv
  rcases Nat.le_total a b with hab | hab
  · have h1 : pow e (b - a) = one := by
      have h2 : mul (pow e a) (pow e (b - a)) = mul (pow e a) one := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hab, h]
      exact mul_left_cancel _ _ _ (pow_nonzero e he a) h2
    have := hmin (b - a) (by omega) h1
    omega
  · have h1 : pow e (a - b) = one := by
      have h2 : mul (pow e b) (pow e (a - b)) = mul (pow e b) one := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hab, h]
      exact mul_left_cancel _ _ _ (pow_nonzero e he b) h2
    have := hmin (a - b) (by omega) h1
    omega

/-- Multiply a trailing-first polynomial by `x + r`. -/
def pMulLin (p : List GF1024) (r : GF1024) : List GF1024 :=
  (zero :: p).zipWith add (p.map (fun c => mul c r) ++ [zero])

/-- The regular generating polynomial's root exponents, from the BIP appendix. -/
def regularRoots : List Nat := [17, 20, 46, 49, 52, 77, 78, 79, 80, 81, 82, 83, 84]

/-- The long generating polynomial's root exponents, from the BIP appendix. -/
def longRoots : List Nat :=
  [32, 64, 96, 895, 927, 959, 991, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026]

/-- The printed regular generating polynomial, trailing-first, degree 13. -/
def regularGenerator : List Symbol := [16, 16, 24, 27, 31, 25, 25, 25, 0, 8, 17, 27, 25, 1]

/-- The printed long generating polynomial, trailing-first, degree 15. -/
def longGenerator : List Symbol := [23, 4, 22, 5, 6, 21, 23, 6, 21, 25, 9, 26, 25, 10, 15, 1]

/-- Re-derivation: the product `∏ (x + βⁱ)` over the appendix's exponent set has
exactly the printed GF(32) coefficients. Finite kernel calculation. -/
theorem regular_generator_rederived :
    (regularRoots.map (pow beta)).foldl pMulLin [one] = regularGenerator.map embed := by
  decide +kernel

/-- Re-derivation of the long generating polynomial `∏ (x + γʲ)`. -/
theorem long_generator_rederived :
    (longRoots.map (pow gamma)).foldl pMulLin [one] = longGenerator.map embed := by
  decide +kernel

/-- The regular root set contains eight consecutive powers, `β⁷⁷ … β⁸⁴`. -/
theorem regular_consecutive_roots : ∀ i ∈ List.range' 77 8, i ∈ regularRoots := by
  decide +kernel

/-- The long root set contains eight consecutive powers, `γ¹⁰¹⁹ … γ¹⁰²⁶`. -/
theorem long_consecutive_roots : ∀ i ∈ List.range' 1019 8, i ∈ longRoots := by
  decide +kernel

/-- Evaluate a GF(1024)-coefficient polynomial (trailing-first) at a point. -/
def evalG (x : GF1024) (p : List GF1024) : GF1024 :=
  p.foldr (fun c acc => add c (mul x acc)) zero

/-- Evaluate a GF(32)-coefficient polynomial (trailing-first) at a GF(1024) point. -/
def evalF (x : GF1024) (p : List Symbol) : GF1024 :=
  p.foldr (fun c acc => add (embed c) (mul x acc)) zero

@[simp] theorem evalG_nil (x : GF1024) : evalG x [] = zero := rfl
@[simp] theorem evalF_nil (x : GF1024) : evalF x [] = zero := rfl

theorem evalG_cons (x : GF1024) (c : GF1024) (p : List GF1024) :
    evalG x (c :: p) = add c (mul x (evalG x p)) := rfl

theorem evalF_cons (x : GF1024) (c : Symbol) (p : List Symbol) :
    evalF x (c :: p) = add (embed c) (mul x (evalF x p)) := rfl

theorem evalG_map_embed (x : GF1024) (p : List Symbol) :
    evalG x (p.map embed) = evalF x p := by
  induction p with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, evalG_cons, evalF_cons, ih]

theorem evalG_append (x : GF1024) (p q : List GF1024) :
    evalG x (p ++ q) = add (evalG x p) (mul (pow x p.length) (evalG x q)) := by
  induction p with
  | nil => simp [evalG, pow_zero, one_mul]
  | cons c cs ih =>
    simp only [List.cons_append, evalG_cons, ih, List.length_cons, pow_succ]
    rw [mul_add, mul_left_comm x (pow x cs.length) (evalG x q), mul_assoc, add_assoc]

theorem evalG_zipAdd (x : GF1024) (p q : List GF1024) (h : p.length = q.length) :
    evalG x (p.zipWith add q) = add (evalG x p) (evalG x q) := by
  induction p generalizing q with
  | nil => cases q with
    | nil => simp [evalG]
    | cons => simp at h
  | cons c cs ih =>
    cases q with
    | nil => simp at h
    | cons d ds =>
      simp only [List.zipWith_cons_cons, evalG_cons, List.length_cons] at *
      rw [ih ds (by omega), mul_add]
      ac_rfl

theorem evalG_map_scalar (x : GF1024) (p : List GF1024) (r : GF1024) :
    evalG x (p.map (fun c => mul c r)) = mul (evalG x p) r := by
  induction p with
  | nil => simp [evalG]
  | cons c cs ih =>
    simp only [List.map_cons, evalG_cons, ih, add_mul, mul_assoc]

theorem evalG_pMulLin (x : GF1024) (p : List GF1024) (r : GF1024) :
    evalG x (pMulLin p r) = mul (evalG x p) (add x r) := by
  have hlen : (zero :: p).length = (p.map (fun c => mul c r) ++ [zero]).length := by
    simp
  rw [pMulLin, evalG_zipAdd x _ _ hlen, evalG_cons, zero_add, evalG_append, List.length_map]
  rw [show evalG x [zero] = zero by simp [evalG_cons, evalG_nil, mul_zero]]
  rw [mul_zero, add_zero, evalG_map_scalar, mul_add, mul_comm (evalG x p) x]

theorem evalG_foldl_pMulLin (x : GF1024) (roots acc : List GF1024) :
    evalG x (roots.foldl pMulLin acc) =
      roots.foldl (fun ev r => mul ev (add x r)) (evalG x acc) := by
  induction roots generalizing acc with
  | nil => rfl
  | cons r rs ih => simp only [List.foldl_cons, ih, evalG_pMulLin]

theorem foldl_zero_factor (x : GF1024) (l : List GF1024) :
    l.foldl (fun ev r => mul ev (add x r)) zero = zero := by
  induction l with
  | nil => rfl
  | cons r rs ih => simp only [List.foldl_cons, zero_mul, ih]

theorem evalG_roots_product_zero (x : GF1024) (roots : List GF1024) (h : x ∈ roots) :
    evalG x (roots.foldl pMulLin [one]) = zero := by
  rw [evalG_foldl_pMulLin]
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem h
  rw [List.foldl_append]
  simp only [List.foldl_cons, add_self, mul_zero]
  exact foldl_zero_factor x l₂

/-- Vandermonde helper: the power-weighted sum over paired lists. -/
def vsum : List GF1024 → List GF1024 → Nat → GF1024
  | [], _, _ => zero
  | _ :: _, [], _ => zero
  | y :: ys, α :: αs, i => add (mul y (pow α i)) (vsum ys αs i)

theorem vsum_cons (y : GF1024) (ys : List GF1024) (α : GF1024) (αs : List GF1024) (i : Nat) :
    vsum (y :: ys) (α :: αs) i = add (mul y (pow α i)) (vsum ys αs i) := rfl

theorem vsum_zero (ys αs : List GF1024) (h : ∀ yj ∈ ys, yj = zero) (i : Nat) :
    vsum ys αs i = zero := by
  induction ys generalizing αs with
  | nil => rfl
  | cons y ys ih =>
    cases αs with
    | nil => rfl
    | cons α αs =>
      rw [vsum_cons, h y (by simp), zero_mul, zero_add]
      exact ih αs (fun yj hj => h yj (by simp [hj]))

/-- The tail elimination step: multiplying equation `i` by `a` and adding it
to equation `i + 1` shifts the weight list. -/
theorem vsum_elim_tail (ys : List GF1024) (a : GF1024) (αs : List GF1024) (i : Nat) :
    add (vsum ys αs (i + 1)) (mul a (vsum ys αs i)) =
      vsum (ys.zipWith (fun yj αj => mul yj (add αj a)) αs) αs i := by
  induction ys generalizing αs with
  | nil => cases αs with
    | nil => simp [vsum, mul_zero]
    | cons α αs => simp [vsum, mul_zero]
  | cons y ys ih =>
    cases αs with
    | nil => simp [vsum, mul_zero]
    | cons α αs =>
      rw [vsum_cons, vsum_cons, mul_add]
      have hterm : mul (mul y (add α a)) (pow α i) =
          add (mul y (pow α (i + 1))) (mul a (mul y (pow α i))) := by
        rw [mul_assoc, add_mul, mul_add, pow_succ, mul_left_comm y a (pow α i),
          mul_comm α (pow α i)]
      rw [add_pair, ← hterm, ih αs]
      rfl

/-- The elimination step: multiplying equation `i` by `a` and adding it to
equation `i + 1` eliminates the head term. -/
theorem vsum_elim (b : GF1024) (ys : List GF1024) (a : GF1024) (αs : List GF1024) (i : Nat) :
    add (vsum (b :: ys) (a :: αs) (i + 1)) (mul a (vsum (b :: ys) (a :: αs) i)) =
      vsum (ys.zipWith (fun yj αj => mul yj (add αj a)) αs) αs i := by
  have hhead : add (mul b (pow a (i + 1))) (mul a (mul b (pow a i))) = zero := by
    rw [pow_succ, ← mul_assoc, mul_comm a (mul b (pow a i)), add_self]
  rw [vsum_cons, vsum_cons, mul_add, add_pair, hhead, zero_add]
  exact vsum_elim_tail ys a αs i

theorem mem_zip_of_mem_left (yj : GF1024) (ys αs : List GF1024) (hlen : ys.length = αs.length)
    (h : yj ∈ ys) : ∃ αj ∈ αs, (yj, αj) ∈ ys.zip αs := by
  induction ys generalizing αs with
  | nil => cases h
  | cons y ys ih =>
    cases αs with
    | nil => simp at hlen
    | cons α αs =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨α, by simp, by simp [List.zip_cons_cons]⟩
      · have hlen' : ys.length = αs.length := by
          simp only [List.length_cons] at hlen; omega
        obtain ⟨αj, hαj, hpair⟩ := ih αs hlen' h'
        exact ⟨αj, List.mem_cons.mpr (Or.inr hαj), List.mem_cons.mpr (Or.inr hpair)⟩

theorem mem_zipWith (f : GF1024 → GF1024 → GF1024) (p : GF1024 × GF1024)
    (l₁ l₂ : List GF1024) (h : p ∈ l₁.zip l₂) : f p.1 p.2 ∈ l₁.zipWith f l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases h
  | cons x xs ih =>
    cases l₂ with
    | nil => cases h
    | cons y ys =>
      rw [List.zip_cons_cons] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_cons.mpr (Or.inl (by simp))
      · rw [List.zipWith_cons_cons]
        exact List.mem_cons.mpr (Or.inr (ih ys h'))

/-- Vandermonde: a zero-sum of powers at distinct points forces all weights to
vanish. This is the BCH bound's linear-algebra core. -/
theorem vandermonde (α y : List GF1024) (nodup : α.Nodup) (hlen : α.length = y.length)
    (h : ∀ i < α.length, vsum y α i = zero) : ∀ yj ∈ y, yj = zero := by
  have main : ∀ (n : Nat) (α y : List GF1024), α.length = n → α.Nodup →
      α.length = y.length → (∀ i < α.length, vsum y α i = zero) →
      ∀ yj ∈ y, yj = zero := by
    intro n
    induction n with
    | zero =>
      intro α y hαlen nodup hlen h yj hj
      cases α with
      | nil =>
        have hy : y = [] := by
          cases y with
          | nil => rfl
          | cons => simp at hlen
        subst hy; cases hj
      | cons => simp at hαlen
    | succ n ih =>
      intro α y hαlen nodup hlen h yj hj
      cases α with
      | nil => simp at hαlen
      | cons a αs =>
        cases y with
        | nil => simp at hlen
        | cons b ys =>
          have hnodup := List.nodup_cons.mp nodup
          have hlen' : αs.length = ys.length := by
            simp only [List.length_cons] at hlen; omega
          have htail : ∀ i < αs.length,
              vsum (ys.zipWith (fun yj αj => mul yj (add αj a)) αs) αs i = zero := by
            intro i hi
            have h1 := h (i + 1) (by simp only [List.length_cons]; omega)
            have h2 := h i (by simp only [List.length_cons]; omega)
            rw [← vsum_elim b ys a αs i, h1, h2, mul_zero, add_zero]
          have hys : ∀ yj ∈ ys.zipWith (fun yj αj => mul yj (add αj a)) αs, yj = zero := by
            apply ih αs (ys.zipWith (fun yj αj => mul yj (add αj a)) αs)
            · simp only [List.length_cons] at hαlen; omega
            · exact hnodup.2
            · rw [List.length_zipWith, hlen', Nat.min_self]
            · exact htail
          have hyzero : ∀ yj ∈ ys, yj = zero := by
            intro yj hj
            obtain ⟨αj, hαj, hpair⟩ := mem_zip_of_mem_left yj ys αs hlen'.symm hj
            have hz := hys (mul yj (add αj a)) (mem_zipWith _ (yj, αj) ys αs hpair)
            rcases (mul_eq_zero _ _).mp hz with h1 | h1
            · exact h1
            · have hne : add αj a ≠ zero := by
                intro hz2
                exact hnodup.1 ((add_eq_zero αj a).mp hz2 ▸ hαj)
              exact absurd h1 hne
          have hb : b = zero := by
            have h0 := h 0 (by simp only [List.length_cons]; omega)
            rw [vsum_cons, pow_zero, mul_one, vsum_zero ys αs hyzero, add_zero] at h0
            exact h0
          rcases List.mem_cons.mp hj with rfl | hj'
          · exact hb
          · exact hyzero yj hj'
  intro yj hj
  exact main α.length α y rfl nodup hlen h yj hj
/-- Indices of a `zipIdx` list, as a shifted range. -/
theorem zipIdx_map_snd (l : List Symbol) (n : Nat) :
    (l.zipIdx n).map Prod.snd = (List.range l.length).map (n + ·) := by
  induction l generalizing n with
  | nil => rfl
  | cons c cs ih =>
    have hcons : (List.range (cs.length + 1)).map (n + ·) =
        n :: (List.range cs.length).map (n + 1 + ·) := by
      have hf : (fun x => n + x) ∘ Nat.succ = (fun x => n + 1 + x) := by
        funext x
        simp only [Function.comp_def]
        omega
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, hf, Nat.add_zero]
    simp only [List.zipIdx, List.map_cons, ih, List.length_cons, hcons]

/-- Membership in `zipIdx` from an index lookup. -/
theorem mem_zipIdx_of_getElem (l : List Symbol) (i : Nat) (h : i < l.length) (n : Nat) :
    (l[i]'h, n + i) ∈ l.zipIdx n := by
  induction l generalizing i n with
  | nil => simp at h
  | cons c cs ih =>
    cases i with
    | zero => simp [List.zipIdx]
    | succ i =>
      have h' : i < cs.length := by simp at h; omega
      have hmem := ih i h' (n + 1)
      simp only [List.zipIdx, List.mem_cons]
      right
      have hidx : n + (i + 1) = n + 1 + i := by omega
      rw [hidx]
      exact hmem

/-- Filtering a `zipIdx` list by a value predicate keeps the same count as
filtering the value list. -/
theorem zipIdx_filter_length (l : List Symbol) (n : Nat) (q : Symbol → Bool) :
    ((l.zipIdx n).filter (fun p => q p.1)).length = (l.filter q).length := by
  induction l generalizing n with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.zipIdx, List.filter_cons]
    by_cases hqc : q c = true
    · simp only [hqc, reduceIte, List.length_cons, ih]
    · have hqc2 : q c = false := by simp [hqc]
      simp only [hqc2, Bool.false_eq_true, reduceIte, ih]

/-- A shifted range has no duplicates. -/
theorem nodup_map_add_range (m n : Nat) : ((List.range m).map (n + ·)).Nodup := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨ih n, by simp, ?_⟩
    intro a ha b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_singleton] at hb
    rw [hb]
    have hi' : i < m := List.mem_range.mp hi
    intro hcon
    have : n + i = n + m := hcon
    omega

/-- A map is nodup when the mapped function is injective on the list's elements
and the indices are already distinct. -/
theorem nodup_map_inj_on (l : List (Symbol × Nat)) (f : Symbol × Nat → GF1024)
    (hinj : ∀ p ∈ l, ∀ q ∈ l, f p = f q → p = q) (hsnd : (l.map Prod.snd).Nodup) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    have hsnd' := List.nodup_cons.mp hsnd
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro hmem
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
      have hpq : p = q := hinj p (by simp) q (by simp [hq]) hqe.symm
      have hm : p.2 ∈ ps.map Prod.snd := List.mem_map.mpr ⟨q, hq, (congrArg Prod.snd hpq).symm⟩
      exact hsnd'.1 hm
    · exact ih (fun p hp q hq => hinj p (by simp [hp]) q (by simp [hq])) hsnd'.2

/-- Power-weighted sum over (coefficient, exponent) pairs. -/
def vsumT : List (Symbol × Nat) → GF1024 → GF1024
  | [], _ => zero
  | (c, j) :: ts, x => add (mul (embed c) (pow x j)) (vsumT ts x)

theorem vsumT_cons (c : Symbol) (j : Nat) (ts : List (Symbol × Nat)) (x : GF1024) :
    vsumT ((c, j) :: ts) x = add (mul (embed c) (pow x j)) (vsumT ts x) := rfl

/-- The polynomial evaluation of a trailing-first coefficient list equals the
power-weighted sum over its indexed coefficients. -/
theorem vsumT_zipIdx (l : List Symbol) (x : GF1024) (s : Nat) :
    vsumT (l.zipIdx s) x = mul (pow x s) (evalF x l) := by
  induction l generalizing s with
  | nil => simp [vsumT, evalF, mul_zero]
  | cons c cs ih =>
    simp only [List.zipIdx, vsumT, evalF_cons, ih]
    rw [pow_succ, mul_add, mul_comm (pow x s) (embed c), mul_assoc]

/-- Zero coefficients never contribute to the weighted sum. -/
theorem vsumT_filter (ts : List (Symbol × Nat)) (x : GF1024) :
    vsumT (ts.filter (fun p => p.1 ≠ 0)) x = vsumT ts x := by
  induction ts with
  | nil => rfl
  | cons p ts ih =>
    cases p with
    | mk c j =>
      rw [List.filter_cons]
      split
      · rw [vsumT_cons, vsumT_cons, ih]
      · rename_i h
        have h1 : c = 0 := by
          simp at h
          exact h
        subst c
        rw [vsumT_cons, embed_zero, zero_mul, zero_add]
        exact ih

/-- At a power of `ω`, the weighted sum is a Vandermonde sum over the embedded
powers. -/
theorem vsumT_eq_vsum (ts : List (Symbol × Nat)) (ω : GF1024) (start i : Nat) :
    vsumT ts (pow ω (start + i)) =
      vsum (ts.map (fun p => mul (embed p.1) (pow ω (start * p.2))))
        (ts.map (fun p => pow ω p.2)) i := by
  induction ts with
  | nil => rfl
  | cons p ts ih =>
    cases p with
    | mk c j =>
      simp only [List.map_cons, vsumT_cons, vsum_cons, ih]
      rw [← pow_mul, Nat.add_mul, pow_add, Nat.mul_comm i j, pow_mul ω j i, mul_assoc]

/-- The BCH bound: a polynomial of degree below `N` with at most eight nonzero
coefficients that vanishes at eight consecutive powers of an order-`N` element
is zero everywhere. Instantiated with `β`/`γ` and the checksum periods below. -/
theorem sparse_zero (coeffs : List Symbol) (ω : GF1024) (N start : Nat)
    (hω : ω ≠ zero)
    (hinj : ∀ a b : Nat, a < N → b < N → pow ω a = pow ω b → a = b)
    (hwt : (coeffs.filter (· ≠ 0)).length ≤ 8)
    (hdeg : coeffs.length ≤ N)
    (hvan : ∀ i < 8, evalF (pow ω (start + i)) coeffs = zero) :
    ∀ c ∈ coeffs, c = 0 := by
  intro c hc
  by_cases hc0 : c = 0
  · exact hc0
  · exfalso
    obtain ⟨j, hj, hjc⟩ := List.mem_iff_getElem.mp hc
    have hmem : (c, j) ∈ coeffs.zipIdx := by
      have h1 := mem_zipIdx_of_getElem coeffs j hj 0
      simp only [Nat.zero_add] at h1
      rw [← hjc]
      exact h1
    have hT : (c, j) ∈ coeffs.zipIdx.filter (fun p => p.1 ≠ 0) :=
      List.mem_filter.mpr ⟨hmem, by simp [hc0]⟩
    generalize hTdef : coeffs.zipIdx.filter (fun p => p.1 ≠ 0) = T
    have hTlen : T.length ≤ 8 := by
      rw [← hTdef, zipIdx_filter_length coeffs 0 (fun c => decide (c ≠ 0))]; exact hwt
    have heq : ∀ i < (T.map (fun p => pow ω p.2)).length,
        vsum (T.map (fun p => mul (embed p.1) (pow ω (start * p.2))))
          (T.map (fun p => pow ω p.2)) i = zero := by
      intro i hi
      have hi' : i < T.length := by simpa only [List.length_map] using hi
      have hi8 : i < 8 := by omega
      rw [← vsumT_eq_vsum, ← hTdef, vsumT_filter, vsumT_zipIdx]
      simp only [pow_zero, one_mul]
      exact hvan i hi8
    have hnodup : (T.map (fun p => pow ω p.2)).Nodup := by
      have hsnd : (T.map Prod.snd).Nodup := by
        have hnodup1 : ((coeffs.zipIdx).map Prod.snd).Nodup := by
          rw [zipIdx_map_snd]
          exact nodup_map_add_range coeffs.length 0
        have hsub : List.Sublist (T.map Prod.snd) ((coeffs.zipIdx).map Prod.snd) := by
          rw [← hTdef]
          exact List.Sublist.map Prod.snd List.filter_sublist
        exact List.Sublist.nodup hsub hnodup1
      apply nodup_map_inj_on T (fun p => pow ω p.2) _ hsnd
      intro p hp q hq hpq
      have hpb := (List.mem_filter.mp (hTdef ▸ hp)).1
      have hqb := (List.mem_filter.mp (hTdef ▸ hq)).1
      have hp2 := List.mem_zipIdx hpb
      have hq2 := List.mem_zipIdx hqb
      have hpe : p.2 = q.2 := hinj p.2 q.2 (by omega) (by omega) hpq
      have h1 : p.1 = q.1 := by
        have e1 : p.1 = coeffs[p.2 - 0]'(by omega) := hp2.2.2
        have e2 : q.1 = coeffs[q.2 - 0]'(by omega) := hq2.2.2
        rw [e1, e2]
        congr 1
      exact Prod.ext h1 hpe
    have hlen : (T.map (fun p => pow ω p.2)).length =
        (T.map (fun p => mul (embed p.1) (pow ω (start * p.2)))).length := by
      simp
    have hall := vandermonde _ _ hnodup hlen heq
    have hy : mul (embed c) (pow ω (start * j)) ∈
        T.map (fun p => mul (embed p.1) (pow ω (start * p.2))) :=
      List.mem_map.mpr ⟨(c, j), hTdef ▸ hT, rfl⟩
    have hz := hall _ hy
    rcases (mul_eq_zero _ _).mp hz with h1 | h1
    · exact hc0 (embed_inj c 0 h1)
    · exact absurd h1 (pow_nonzero ω hω _)

end GF1024

end Codex32

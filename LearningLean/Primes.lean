-- goals:
-- define prime numbers, prove enough basic theorems
-- to show the numbers 0,...,p-1 for p prime are a field

def prime (p : Nat) :=
  (p ≠ 0) ∧ (p ≠ 1) ∧
  ∀ x : Nat, (x ∣ p) → (x = 1) ∨ (x = p)

-- TODO: show that this is equivalent to prime
def prime' (p : Nat) :=
  (p ≠ 0) ∧ (p ≠ 1) ∧
  ∀ a b : Nat, (p ∣ a*b) → (p ∣ a) ∨ (p ∣ b)

structure Prime where
  val : Nat
  prime : prime val

namespace Prime
  instance coeToNat : CoeOut Prime Nat :=
    ⟨fun v => v.val⟩

  -- lemma: primes are > 1
  -- TODO can we simplify this?
  theorem gt_1 (p : Prime) : p.val > 1 := by
    have ne_0 : p.val ≠ 0 := p.prime.left
    have ne_1 : p.val ≠ 1 := p.prime.right.left
    have le_1 : 1 ≤ p.val := Nat.pos_of_ne_zero ne_0 |> Nat.succ_le_of_lt
    cases (Nat.lt_or_eq_of_le le_1) with
    | inl lt_1 => assumption
    | inr eq_1 => exact absurd (Eq.symm eq_1) ne_1
end Prime

structure Field (p : Prime) where
  val : Nat
  less : val < p.val

namespace Field
  variable {p : Prime} (x y z : Field p) (m n : Nat)

  -- taking a number mod p produces something < p
  theorem mod_smaller (x : Nat) : x % p < p :=
    have gt_zero : p.val > 0 :=
        (p.prime.left : p.val ≠ 0)
        |> Nat.pos_of_ne_zero
    show x % p < p from Nat.mod_lt x gt_zero

  /--
  create a field element from a Nat, taking the number mod p.
  -/
  def create (x : Nat) : Field p :=
    mk (x % p) (mod_smaller x)

  instance ofNat : OfNat (Field p) n where
    ofNat := create n

  instance coeToNat : CoeOut (Field p) Nat :=
    ⟨fun v => v.val⟩

  /--
  a simple proof strategy for algebraic identities in the field is to lift them to Nat,
  i.e. `x + y = y + x` for all Fields holds because `(x + y) % p = (y + x) % p` for all Nats.

  to execute that strategy, we always start with `ext; simp;`:
    1. `ext` reduces to an identity on the values `(x + y).val = (y + x).val`
    2. `simp` is equipped with lemmas that expand field ops, like `(x + y).val = (x.val + y.val) % p`
    3. we end up with something like `(x.val + y.val) % p = (y.val + x.val) % p` which is just `Nat.add_comm`
  -/
  @[ext] theorem ext {x y : Field p} (h : (x : Nat) = y) : x = y :=
    -- proof taken from Fin.ext
    match x, y, h with
    | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

  -- constants
  def zero : Field p := 0
  def one : Field p := 1

  @[simp] theorem zero_val : (0 : Field p).val = 0 := rfl
  @[simp] theorem one_val : (1 : Field p).val = 1 := Nat.mod_eq_of_lt (Prime.gt_1 p)
  @[simp] theorem one_mod : 1 % p.val = 1 := Nat.mod_eq_of_lt (Prime.gt_1 p)

  -- create preserves field elements

  -- helpers for ext; simp
  @[simp] theorem create_val : (@create p n).val = n % p := rfl
  @[simp] theorem mod_noop : x.val % p = x.val := Nat.mod_eq_of_lt x.less

  theorem create_eq : x = create x.val := by ext; simp

  -- addition

  instance : Add (Field p) where
    add x y := x.val + y.val |> create

  -- simp expands addition
  @[simp] theorem add_val : (x + y).val = (x.val + y.val) % p := by rfl

  -- create preserves addition
  theorem create_add : create n + create m = @create p (n + m) := by ext; simp

  -- addition: neutral element
  theorem add_zero : x + 0 = x := by ext; simp
  theorem zero_add : 0 + x = x := by ext; simp

  -- addition: commutative
  theorem add_comm : x + y = y + x := by
    ext; simp; rw [Nat.add_comm]

  -- addition: associative
  theorem add_assoc : x + y + z = x + (y + z) := by
    ext; simp; rw [Nat.add_assoc]

  -- additive inverse

  instance : Neg (Field p) where
    neg x := p - x.val |> create

  instance : Sub (Field p) where
    sub x y := x.val + (p - y.val) |> create

  @[simp] theorem neg_val : (-x).val = (p - x.val) % p := rfl
  @[simp] theorem sub_val : (x - y).val = (x.val + (p - y.val)) % p := rfl

  -- helper facts for simp: x < p, x ≤ p
  @[simp] theorem lt_p : x.val < p := x.less
  @[simp] theorem le_p : x.val ≤ p := x.less |> Nat.le_of_lt

  theorem neg_add : -x + x = 0 := by ext; simp
  theorem add_neg : x + (-x) = 0 := by ext; simp
  theorem add_sub : x - x = 0 := by ext; simp
  theorem sub_def : x - y = x + (-y) := by ext; simp
  theorem neg_zero : -(0 : Field p) = 0 := by ext; simp

  -- multiplication

  instance : Mul (Field p) where
    mul x y := x.val * y.val |> create

  @[simp] theorem mul_val : (x * y).val = (x.val * y.val) % p := by rfl

  -- help simp pull out mod p (for addition this already works)
  @[simp] theorem mod_mul_right : (n * (m % p)) % p = (n * m) % p := by
    rw [Nat.mul_mod]; rw [Nat.mod_mod]; rw [Nat.mul_mod n]

  @[simp] theorem mod_mul_left : ((n % p) * m) % p = (n * m) % p := by
    rw [Nat.mul_mod]; rw [Nat.mod_mod]; rw [Nat.mul_mod n]

  -- create preserves multiplication
  theorem create_mul : create n * create m = @create p (n * m) := by ext; simp

  -- multiplication: neutral element
  theorem mul_one : x * 1 = x := by ext; simp
  theorem one_mul : 1 * x = x := by ext; simp

  -- multiplication by zero
  theorem zero_mul : 0 * x = 0 := by ext; simp
  theorem mul_zero : x * 0 = 0 := by ext; simp

  -- multiplication: commutative
  theorem mul_comm : x * y = y * x := by
    ext; simp; rw [Nat.mul_comm]

  -- multiplication: associative
  theorem mul_assoc : x * y * z = x * (y * z) := by
    ext; simp; rw [Nat.mul_assoc]

  -- multiplication: distributive
  theorem left_distrib : x * (y + z) = x * y + x * z := by
    ext; simp; rw [Nat.left_distrib]

  theorem right_distrib : (x + y) * z = x * z + y * z := by
    ext; simp; rw [Nat.right_distrib]

  -- exponentiation

  instance : NatPow (Field p) where
    -- TODO inefficient algorithm -- do we actually care?
    pow x n := x.val ^ n |> create

  @[simp] theorem pow_val : (x ^ n).val = (x.val ^ n) % p := by rfl

  theorem pow_zero : x^0 = 1 := by ext; simp
  theorem pow_one : x^1 = x := by ext; simp
  theorem square : x^2 = x * x := by ext; simp; rw [Nat.pow_two]
  theorem pow_add : x^(m + n) = x^m * x^n := by ext; simp; rw [Nat.pow_add]
  theorem cube : x^3 = x * x * x := by rw [pow_add x 2 1, square, pow_one]
end Field

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

structure Field (p : Prime) where
  val : Nat
  less : val < p.val

namespace Field
  variable {p : Prime} (x y z : Field p)

  -- taking a number mod p produces something < p
  theorem mod_smaller (x : Nat) : x % p.val < p.val :=
    have gt_zero : p.val > 0 :=
        (p.prime.left : p.val ≠ 0)
        |> Nat.pos_of_ne_zero
    show x % p.val < p.val from Nat.mod_lt x gt_zero

  -- create field element from a Nat
  def create (x : Nat) : Field p :=
    mk (x % p.val) (mod_smaller x)

  instance : OfNat (Field p) n where
    ofNat := create n

  -- constants
  def zero : Field p := 0
  def one : Field p := 1

  -- create preserves field elements
  theorem create_eq (x : Field p) : x = create x.val := by
    rw [Field.mk.injEq]
    exact calc
    x.val = x.val % p.val := by rw [Nat.mod_eq_of_lt x.less]
    _     = (create x.val).val := rfl

  -- addition

  instance : Add (Field p) where
    add x y := x.val + y.val |> create

  -- create preserves addition
  theorem create_add {p : Prime} (x y : Nat) : create x + create y = @create p (x + y)  := by
    rw [Field.mk.injEq]
    exact calc
      (create x + create y).val
      _ = (x % p.val + y % p.val) % p.val := rfl
      _ = (x + y) % p.val := by rw [← Nat.add_mod]
      _ = (create (x + y)).val := rfl

  -- addition: neutral element
  theorem add_zero : x + 0 = x := by
    rw [Field.mk.injEq]
    exact calc
      (x + 0).val
      _ = x.val % p.val := rfl
      _ = x.val := Nat.mod_eq_of_lt x.less

  -- addition: commutative
  theorem add_comm : x + y = y + x := by
    rw [Field.mk.injEq]
    exact calc
      (x + y).val
      _ = (x.val + y.val) % p.val := rfl
      _ = (y.val + x.val) % p.val := by rw [Nat.add_comm]
      _ = (y + x).val := rfl

  -- addition: associative
  theorem add_assoc : x + y + z = x + (y + z) := by
    rw [create_eq x, create_eq y, create_eq z]
    simp [create_add]
    rw [Nat.add_assoc]

  -- additive inverse

  instance : Neg (Field p) where
    neg x := p.val - x.val |> create

  theorem neg_add : -x + x = 0 := by
    let xv := x.val
    rw [Field.mk.injEq]
    exact calc
      (-x + x).val
      _ = ((-x).val + xv) % p.val := rfl
      _ = ((p.val - xv) % p.val + xv) % p.val := rfl
      _ = (p.val - xv + xv) % p.val := by rw [Nat.mod_add_mod]
      _ = p.val % p.val := by
        have h : xv ≤ p.val := x.less |> Nat.le_of_lt
        rw [Nat.sub_add_cancel h]
      _ = 0 := by rw [Nat.mod_self]
      _ = zero.val := rfl
end Field


-- lemma: primes are > 1
-- TODO can we simplify this?
theorem prime_gt_one (p : Prime) : p.val > 1 := by
  have ne_0 : p.val ≠ 0 := p.prime.left
  have ne_1 : p.val ≠ 1 := p.prime.right.left
  have le_1 : 1 ≤ p.val := Nat.pos_of_ne_zero ne_0 |> Nat.succ_le_of_lt
  cases (Nat.lt_or_eq_of_le le_1) with
  | inl lt_1 => assumption
  | inr eq_1 => exact absurd (Eq.symm eq_1) ne_1

namespace Field
  variable {p : Prime} (x y z : Field p)

  -- multiplication

  instance : Mul (Field p) where
    mul x y := x.val * y.val |> create

  -- create preserves multiplication
  theorem create_mul {p : Prime} (x y : Nat) : create x * create y = @create p (x * y)  := by
    rw [Field.mk.injEq]
    exact calc
      (create x * create y).val
      _ = ((x % p.val) * (y % p.val)) % p.val := rfl
      _ = (x * y) % p.val := by rw [← Nat.mul_mod]
      _ = (create (x * y)).val := rfl

  -- multiplication: neutral element
  theorem mul_one : x * 1 = x := by
    rw [← one]
    rw [create_eq x, create_eq one]
    rw [create_mul]
    -- create (x.val * one.val) = create x.val
    have h : one.val = 1 := Nat.mod_eq_of_lt (prime_gt_one p)
    simp [h]

  -- multiplication: commutative
  theorem mul_comm : x * y = y * x := by
    rw [create_eq x, create_eq y]
    simp [create_mul]
    rw [Nat.mul_comm]

  -- multiplication: associative
  theorem mul_assoc : x * y * z = x * (y * z) := by
    rw [create_eq x, create_eq y, create_eq z]
    simp [create_mul]
    rw [Nat.mul_assoc]
end Field

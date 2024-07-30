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
  variable {p : Prime} (x : Field p)

  -- taking a number mod p produces something < p
  theorem mod_smaller (x : Nat) : x % p.val < p.val :=
    have gt_zero : p.val > 0 :=
        (p.prime.left : p.val ≠ 0)
        |> Nat.ne_zero_iff_zero_lt.mp
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
  theorem add_comm (x y : Field p) : x + y = y + x := by
    rw [Field.mk.injEq]
    exact calc
      (x + y).val
      _ = (x.val + y.val) % p.val := rfl
      _ = (y.val + x.val) % p.val := by rw [Nat.add_comm]
      _ = (y + x).val := rfl

  -- addition: associative
  theorem add_assoc (x y z : Field p) : x + y + z = x + (y + z) := by
    rw [create_eq x, create_eq y, create_eq z]
    repeat rw [create_add]
    rw [Nat.add_assoc]

  -- additive inverse

  instance : Neg (Field p) where
    neg x := p.val - x.val |> create

  theorem neg_add {p : Prime} (x : Field p) : -x + x = 0 := by
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

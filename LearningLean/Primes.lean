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

  -- constants
  def zero : Field p := create 0
  def one : Field p := create 1

  -- create preserves field elements
  theorem create_eq (x : Field p) : create x.val = x := by
    rw [Field.mk.injEq]
    exact calc
      (create x.val).val
      _ = x.val % p.val := rfl
      _ = x.val := Nat.mod_eq_of_lt x.less

  -- addition

  instance : Add (Field p) where
    add x y := x.val + y.val |> create

  -- create preserves addition
  theorem create_add {p : Prime} (x y : Nat) : @create p (x + y) = create x + create y := by
    rw [Field.mk.injEq]
    exact calc
      (create (x + y)).val
      _ = (x + y) % p.val := rfl
      _ = (x % p.val + y % p.val) % p.val := by rw [Nat.add_mod]
      _ = (create x + create y).val := rfl

  -- addition: neutral element
  theorem add_zero : x + zero = x := by
    rw [Field.mk.injEq]
    exact calc
      (x + zero).val
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
  theorem add_assoc (x y z : Field p) : x + y + z = x + (y + z) := calc
    x + y + z
    _ = create x.val + create y.val + create z.val := by simp [create_eq]
    _ = create (x.val + y.val + z.val) := by simp [create_add]
    _ = create (x.val + (y.val + z.val)) := by rw [Nat.add_assoc]
    _ = create x.val + (create y.val + create z.val) := by simp [create_add]
    _ = x + (y + z) := by simp [create_eq]
end Field

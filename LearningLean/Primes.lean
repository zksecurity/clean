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

  -- addition
  instance : Add (Field p) where
    add x y := x.val + y.val |> create

  -- addition: neutral element

  def zero : Field p := create 0

  theorem neutral : x + zero = x := sorry

end Field

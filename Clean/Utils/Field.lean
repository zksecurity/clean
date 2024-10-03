import Mathlib.Data.ZMod.Basic

-- main field definition
def F p := ZMod p
instance (p : ℕ) [Fact p.Prime]: Field (F p) := ZMod.instField p
instance (p : ℕ) [Fact p.Prime] : Fintype (F p) := ZMod.fintype p


namespace FieldUtils

theorem p_neq_zero (p: ℕ) [p_is_prime: Fact p.Prime] : p ≠ 0 :=
  Nat.Prime.ne_zero p_is_prime.elim

end FieldUtils

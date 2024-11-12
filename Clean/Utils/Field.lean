import Mathlib.Data.ZMod.Basic

-- main field definition
def F p := ZMod p
instance (p : ℕ) [Fact p.Prime]: Field (F p) := ZMod.instField p
instance (p : ℕ) [Fact p.Prime] : Fintype (F p) := ZMod.fintype p
instance (p : ℕ) [Fact p.Prime] : Inhabited (F p) := ⟨0⟩
instance (p : ℕ) : CommRing (F p) := ZMod.commRing p
instance (p : ℕ) [Fact p.Prime] : IsDomain (F p) := ZMod.instIsDomain p
instance (p : ℕ) : DecidableEq (F p) := ZMod.decidableEq p

namespace FieldUtils
variable {p : ℕ} [p_prime: Fact p.Prime]


theorem p_neq_zero : p ≠ 0 :=
  Nat.Prime.ne_zero p_prime.elim

theorem sum_do_not_wrap_around (x y: F p) :
  x.val + y.val < p -> (x + y).val = x.val + y.val := by
  intro h
  have sum_eq_over_naturals : (x.val + y.val) % p = x.val + y.val
    := (Nat.mod_eq_iff_lt p_neq_zero).mpr h
  rw [ZMod.val_add, sum_eq_over_naturals]

theorem byte_sum_do_not_wrap (x y: F p) [p_large_enough: Fact (p > 512)]:
  x.val < 256 -> y.val < 256 -> (x + y).val = x.val + y.val := by
  intros hx hy
  have sum_lt_512 : x.val + y.val < 512 := Nat.add_lt_add hx hy
  have sum_lt_p : x.val + y.val < p := Nat.lt_trans sum_lt_512 p_large_enough.elim
  apply sum_do_not_wrap_around x y sum_lt_p

theorem byte_plus_256_do_not_wrap (x: F p) [p_large_enough: Fact (p > 512)]:
  x.val < 256 -> (x + 256).val = x.val + 256 := by
  intro hx
  have val_256_lt_p : 256 < p := Nat.lt_trans (by norm_num) p_large_enough.elim
  have mod_256_is_256 : 256 % p = 256 := (Nat.mod_eq_iff_lt (FieldUtils.p_neq_zero)).mpr val_256_lt_p
  have val_256_is_256 : (256 : F p).val = 256 % p := ZMod.val_natCast _
  have out_plus_256_lt_512 : x.val + 256 < 512 := Nat.add_lt_add_right hx 256
  have out_plus_256_lt_p : x.val + 256 < p := Nat.lt_trans out_plus_256_lt_512 p_large_enough.elim
  rw [← mod_256_is_256, ←val_256_is_256] at out_plus_256_lt_p
  have thm := sum_do_not_wrap_around x 256 out_plus_256_lt_p
  rw [val_256_is_256, mod_256_is_256] at thm
  apply thm

theorem val_lt_p (x: ℕ) : (x < p) -> (x : F p).val = x := by
  intro x_lt_p
  have x_mod_is_x : x % p = x := (Nat.mod_eq_iff_lt (FieldUtils.p_neq_zero)).mpr x_lt_p
  rw [ZMod.val_natCast x]
  assumption


end FieldUtils

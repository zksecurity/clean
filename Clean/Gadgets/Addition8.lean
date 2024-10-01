import Clean.GenericConstraint
import Clean.Expression
import Clean.Gadgets.Boolean
import Clean.Gadgets.ByteLookup
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

namespace Addition8
open Expression
variable {p : ℕ} [p_is_prime: Fact p.Prime] [p_large_enough: Fact (p > 512)]
instance : CommRing (F p) := ZMod.commRing p

def circuit (N M : ℕ+) (x y out carry : Expression (F p)) : GenericConstraint p N M :=
  GenericConstraint.mk
    [
      x + y - out - carry * (const 256)
    ]
    [
      ByteLookup.lookup N M x,
      ByteLookup.lookup N M y,
      ByteLookup.lookup N M out,
    ]
    [
      Boolean.circuit N M carry
    ]

def spec (N M : ℕ+) (x y out carry: Expression (F p)) : Inputs N M (F p) -> Prop :=
  (fun env =>
      have x := x.eval env;
      have y := y.eval env;
      have out := out.eval env;
      have _carry := carry.eval env;
      out.val = (x.val + y.val) % 256)

theorem equiv_mod_256_zero_carry_fw (x y out : F p):
    x.val < 256 -> y.val < 256 -> out.val < 256 ->
    (x + y - out = 0 -> out.val = (x.val + y.val) % 256) := by
  intros hx hy hout
  let sum_lt_512 : x.val + y.val < 512 := Nat.add_lt_add hx hy
  let p_neq_zero : p ≠ 0 := Nat.Prime.ne_zero p_is_prime.elim
  let sum_lt_p : x.val + y.val < p := Nat.lt_trans sum_lt_512 p_large_enough.elim
  let sum_eq_over_naturals : (x.val + y.val) % p = x.val + y.val
    := (Nat.mod_eq_iff_lt p_neq_zero).mpr sum_lt_p
  intro h
  rw [sub_eq_zero] at h
  apply_fun ZMod.val at h
  rw [ZMod.val_add, sum_eq_over_naturals] at h
  have asd := hout
  rw [←h] at asd
  rw [Nat.mod_eq_of_lt asd]
  apply Eq.symm
  assumption


theorem equiv (N M : ℕ+) (x y out carry: Expression (F p)) :
  (∀ X,
    (forallList (fullLookupSet (circuit N M x y out carry)) (fun lookup => lookup.prop X))
    -> (
      (forallList (fullConstraintSet (circuit N M x y out carry)) (fun constraint => constraint.eval X = 0))
      ↔
      spec N M x y out carry X
    )
  ) := by

  intro X
  simp [forallList, ByteLookup.lookup]
  let equivBoolean := Boolean.equiv N M carry X
  simp [forallList, Boolean.spec] at equivBoolean
  rw [equivBoolean, spec]

  simp [eval]
  set x := x.eval X
  set y := y.eval X
  set out := out.eval X
  set carry := carry.eval X

  intro hx_byte
  intro hy_byte
  intro hout_byte

  constructor
  · intro h
    rcases (And.right h) with zero_carry | one_carry
    · rw [zero_carry] at h
      simp [ZMod.val_add] at h
      rw [←sub_eq_add_neg] at h
      exact equiv_mod_256_zero_carry_fw x y out hx_byte hy_byte hout_byte h
    · sorry
  · sorry
end Addition8

import Clean.GenericConstraint
import Clean.Expression
import Clean.Gadgets.Boolean
import Clean.Gadgets.ByteLookup
import Clean.Utils.Field
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

/-
  8-bit addition constraint gadget: the output `out` must be the sum of the
  inputs `x` and `y` modulo 256, and the carry `carry` must be the quotient
  of the sum of `x` and `y` divided by 256.
-/
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
      have carry := carry.eval env;
      (out.val = (x.val + y.val) % 256) ∧ carry.val = (x.val + y.val) / 256)


/-
  First part of the soundness direction: case of zero carry
-/
theorem equiv_mod_256_zero_carry_fw (x y out : F p):
    x.val < 256 -> y.val < 256 -> out.val < 256 ->
    (x + y - out = 0 -> (out.val = (x.val + y.val) % 256 ∧ (x.val + y.val) / 256 = 0)) := by
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
  have x_plus_y_less_256 := hout
  rw [←h] at x_plus_y_less_256
  apply And.intro
  · rw [Nat.mod_eq_of_lt x_plus_y_less_256]
    apply Eq.symm
    assumption
  · apply Nat.div_eq_of_lt; assumption

/-
  Second part of the soundness direction: case of one carry
  TODO: this is very messy because dealing with % 256 over a general field, even if
  we have the p > 512 assumption, is not trivial.
  We should probably refactor using a general theorem about lifting operations to F p that
  holds if the field is large enough (i.e., if there is no wrapping around).
-/
theorem equiv_mod_256_one_carry_fw (x y out : F p):
    x.val < 256 -> y.val < 256 -> out.val < 256 ->
    x + y - out - 256 = 0 -> (out.val = (x.val + y.val) % 256 ∧ (x.val + y.val) / 256 = 1) := by
  intros hx hy hout
  have sum_lt_512 : x.val + y.val < 512 := Nat.add_lt_add hx hy
  have sum_lt_p : x.val + y.val < p := Nat.lt_trans sum_lt_512 p_large_enough.elim
  have sum_eq_over_naturals : (x.val + y.val) % p = x.val + y.val
    := (Nat.mod_eq_iff_lt (FieldUtils.p_neq_zero p)).mpr sum_lt_p
  have val_256_lt_p : 256 < p := Nat.lt_trans (by norm_num) p_large_enough.elim
  have mod_256_is_256 : 256 % p = 256 := (Nat.mod_eq_iff_lt (FieldUtils.p_neq_zero p)).mpr val_256_lt_p
  have val_256_is_256 : (256 : F p).val = 256 % p := ZMod.val_natCast _
  have out_plus_256_lt_512 : out.val + 256 < 512 := Nat.add_lt_add_right hout 256
  have out_plus_256_lt_p : out.val + 256 < p := Nat.lt_trans out_plus_256_lt_512 p_large_enough.elim

  intro h
  rw [sub_eq_zero] at h
  have h := eq_add_of_sub_eq h
  rw [add_comm 256] at h
  have h' : (x + y).val ≥ (256 : F p).val := by
    apply_fun ZMod.val at h
    rw [ZMod.val_add out] at h
    rw [val_256_is_256, mod_256_is_256] at h
    rw [(Nat.mod_eq_iff_lt (FieldUtils.p_neq_zero p)).mpr out_plus_256_lt_p] at h
    have h2 : out.val + 256 >= 256 := by simp
    rw [←h] at h2
    rw [val_256_is_256, mod_256_is_256]
    assumption
  have h := Eq.symm (eq_sub_of_add_eq (Eq.symm h))
  apply_fun ZMod.val at h
  rw [ZMod.val_sub h'] at h
  rw [ZMod.val_add, sum_eq_over_naturals] at h
  rw [val_256_is_256, mod_256_is_256] at h

  -- finally, now the statement is over ℕ
  set x := x.val
  set y := y.val
  set out := out.val
  apply And.intro
  · rw [ZMod.val_add, sum_eq_over_naturals, val_256_is_256, mod_256_is_256] at h'
    have sub_mod := Nat.mod_eq_sub_mod h'
    rw [sub_mod]
    rw [←h] at hout
    rw [Nat.mod_eq_of_lt hout, h]
  · rw [ZMod.val_add, sum_eq_over_naturals, val_256_is_256, mod_256_is_256] at h'
    rw [Nat.div_eq_of_lt_le]
    · rw [←Nat.one_mul 256] at h'; assumption
    · simp; assumption


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
      have thm := equiv_mod_256_zero_carry_fw x y out hx_byte hy_byte hout_byte h
      apply_fun ZMod.val at zero_carry
      rw [ZMod.val_zero] at zero_carry
      rw [← thm.right] at zero_carry
      apply And.intro
      · exact thm.left
      · exact zero_carry
    · rw [one_carry] at h
      simp [ZMod.val_add] at h
      rw [←sub_eq_add_neg, ←sub_eq_add_neg (x + y)] at h
      have thm := equiv_mod_256_one_carry_fw x y out hx_byte hy_byte hout_byte h
      apply_fun ZMod.val at one_carry
      rw [ZMod.val_one] at one_carry
      rw [← thm.right] at one_carry
      apply And.intro
      · exact thm.left
      · exact one_carry
  · intro h
    have carry? := Nat.lt_or_ge (x.val + y.val) 256
    rcases carry? with sum_lt_256 | sum_ge_256
    · sorry
    · sorry


instance (N M : ℕ+) (x y out carry : Expression (F p)) : Constraint N M p :=
{
  circuit := circuit N M x y out carry,
  spec := spec N M x y out carry,
  equiv := equiv N M x y out carry
}

end Addition8

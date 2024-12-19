import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.GadgetsNew.ByteLookup


section
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Circuit

structure U32 (T: Type) where
  x0 : T
  x1 : T
  x2 : T
  x3 : T

namespace U32

def witness (compute : Unit → U32 (F p)) := do
  let val := compute ()
  let x0 ←  witness_var (fun _ => val.x0)
  let x1 ←  witness_var (fun _ => val.x1)
  let x2 ←  witness_var (fun _ => val.x2)
  let x3 ←  witness_var (fun _ => val.x3)

  ByteLookup.byte_lookup x0
  ByteLookup.byte_lookup x1
  ByteLookup.byte_lookup x2
  ByteLookup.byte_lookup x3

  return U32.mk x0 x1 x2 x3


-- TODO: refactor those definition elsewhere
def less_than_p [p_pos: Fact (p ≠ 0)] (x: F p) : x.val < p := by
  rcases p
  · have : 0 ≠ 0 := p_pos.elim; tauto
  · exact x.is_lt

def mod (x: F p) (c: ℕ+) (lt: c < p) : F p :=
  FieldUtils.nat_to_field (x.val % c) (by linarith [Nat.mod_lt x.val c.pos, lt])

def mod_256 (x: F p) : F p :=
  mod x 256 (by linarith [p_large_enough.elim])

def floordiv [Fact (p ≠ 0)] (x: F p) (c: ℕ+) : F p :=
  FieldUtils.nat_to_field (x.val / c) (by linarith [Nat.div_le_self x.val c, less_than_p x])



def is_normalized (x: U32 (F p)) :=
  x.x0.val < 256 ∧ x.x1.val < 256 ∧ x.x2.val < 256 ∧ x.x3.val < 256

def value (x: U32 (F p)) :=
  x.x0.val + x.x1.val * 256 + x.x2.val * 256^2 + x.x3.val * 256^3

def decompose_nat (x: ℕ) : U32 (F p) :=
  let x0 := mod x 256 (by linarith [p_large_enough.elim])
  let x1 := mod (floordiv x 256) 256 (by linarith [p_large_enough.elim])
  let x2 := mod (floordiv x 256^2) 256 (by linarith [p_large_enough.elim])
  let x3 := mod (floordiv x 256^3) 256 (by linarith [p_large_enough.elim])
  ⟨ x0, x1, x2, x3 ⟩

def wrapping_add (x y: U32 (F p)) : U32 (F p) :=
  let val_x := x.value
  let val_y := y.value
  let val_out := (val_x + val_y) % 2^32
  U32.decompose_nat val_out


lemma wrapping_add_correct (x y z: U32 (F p)) :
    x.wrapping_add y = z ↔ z.value = (x.value + y.value) % 2^32 := by
  sorry

end U32
end

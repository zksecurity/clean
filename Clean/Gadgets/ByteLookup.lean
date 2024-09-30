import Clean.GenericConstraint
import Clean.Expression
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

/-
  Byte lookup constraint gadget: the input x must be a byte value, i.e. x < 256
-/
namespace ByteLookup
open Expression
variable {p : ℕ} [Fact p.Prime]

def lookup (N M : ℕ+) (x : Expression (F p)) : LookupArgument p N M :=
  {
    -- NOTE: is this correct? Not for a general prime p I think
    prop := fun env => (x.eval env).val < 256
  }

end ByteLookup

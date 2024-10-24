import Clean.GenericConstraint
import Clean.Expression
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

/-
  Byte lookup constraint gadget: the input x must be a byte value, i.e. x < 256
-/
namespace ByteLookup
open Expression
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

def lookup (N : ℕ+) (M : ℕ) (x : Expression N M (F p)) : LookupArgument p N M :=
{
  prop := fun env => (env.eval x).val < 256
}

end ByteLookup

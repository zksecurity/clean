import Mathlib.Data.ZMod.Basic

theorem prime_1009 : Nat.Prime 1009 := by
  -- isn't there a more efficient way to prove primalitity?
  set_option maxRecDepth 900 in decide

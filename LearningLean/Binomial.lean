/--
Goals: Define binomial coefficients and prove:
- the reductions (Bin n k+1) -> (Bin n k) and (Bin n+1 k) -> (Bin n k)
- the binomial theorem
-/

def Bin : Nat → Nat → Nat := fun
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => Bin n (k + 1) + Bin n k

namespace Bin

variable (n k : Nat)

theorem zero : Bin n 0 = 1 := by cases n <;> rfl

theorem greater : ∀ n k, n < k → Bin n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    -- write k as _ + 1 to apply Bin definition `0, _ + 1 => 0`
    let ⟨ _, (k_succ : k = _ + 1) ⟩ :=
      Nat.ne_zero_iff_zero_lt.mpr hk |> Nat.exists_eq_succ_of_ne_zero
    rw [k_succ]
    rfl

  | succ n greater_n =>
    intro k (hk : n + 1 < k)
    -- write k as _ + 1 to apply recursive Bin definition for `n + 1, _ + 1`
    let ⟨ km1, (k_succ : k = km1 + 1) ⟩ :=
      Nat.zero_lt_of_lt hk |> Nat.ne_zero_iff_zero_lt.mpr |> Nat.exists_eq_succ_of_ne_zero
    rw [k_succ]
    -- now simp expands the goal to `Bin n (km1 + 1) + Bin n km1 = 0`, which is true by the IH
    simp [Bin]
    have hk' : n + 1 < km1 + 1 := k_succ ▸ hk
    have h : n < km1 := Nat.lt_of_succ_lt_succ hk'
    have h' : n < km1 + 1 := Nat.lt_of_succ_lt hk'
    simp [greater_n, h, h']


theorem same : Bin n n = 1 := by
  induction n with
  | zero => rfl
  | succ n same_n =>
    -- `Bin (n + 1) (n + 1) = Bin n (n + 1) + Bin n n = 0 + 1` by `greater` and `same n`
    simp [Bin, greater n (n+1), same_n]


theorem k_reduction : ∀ n k, Bin n (k+1) = n/(k+1) * Bin n k := by
  sorry

theorem n_reduction (n k : Nat) : Bin (n+1) k = (n+1)/(n-k+1) * Bin n k := by
  sorry

end Bin

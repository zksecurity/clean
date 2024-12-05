import Clean.GenericConstraint
import Clean.Expression
import Clean.Gadgets.Boolean
import Clean.Gadgets.ByteLookup
import Clean.Utils.Field
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Gadgets.Addition8
import Clean.Gadgets.Addition8Full

/-
  32-bit addition gadget
-/
namespace Addition32
open Expression
variable {p : ℕ} [p_is_prime: Fact p.Prime] [p_large_enough: Fact (p > 512)]

def Limbs4 (N : ℕ+) (M p: ℕ) :=
  Expression N M (F p)
  × Expression N M (F p)
  × Expression N M (F p)
  × Expression N M (F p)

def Limbs4.get (N : ℕ+) (M p: ℕ) (x : Limbs4 N M p) : ℕ -> Expression N M (F p)
  | 0 => x.fst
  | 1 => x.snd.fst
  | 2 => x.snd.snd.fst
  | 3 => x.snd.snd.snd
  | _ => 0

def Limbs4.value (N : ℕ+) (M p: ℕ) (x : Limbs4 N M p) (trace: TraceOfLength N M (F p)) : ℕ :=
  (trace.eval (x.get 0)).val +
  256 * (trace.eval (x.get 1)).val +
  256^2 * (trace.eval (x.get 2)).val +
  256^3 * (trace.eval (x.get 3)).val

def circuit (N : ℕ+) (M : ℕ) (x y out carries : Limbs4 N M p) : ConstraintGadget p N M :=
  ⟨
    [],
    [],
    [
      /-
        he circuit is composed of one half-adder and three full-adders
        The carries are shared between the full-adders
      -/
      Addition8.circuit N M (x.get 0) (y.get 0) (out.get 0) (carries.get 0),
      Addition8Full.circuit N M (x.get 1) (y.get 1) (out.get 1) (carries.get 0) (carries.get 1),
      Addition8Full.circuit N M (x.get 2) (y.get 2) (out.get 2) (carries.get 1) (carries.get 2),
      Addition8Full.circuit N M (x.get 3) (y.get 3) (out.get 3) (carries.get 2) (carries.get 3)
    ]
  ⟩

def spec (N : ℕ+) (M : ℕ) (x y out _carries : Limbs4 N M p) : TraceOfLength N M (F p) -> Prop :=
  (fun trace =>
      have x := x.value trace
      have y := y.value trace
      have out := out.value trace

      -- the output is correct
      (out = (x + y) % 2^32)

      -- TODO: add all the other props that are necessary for completeness
      )

def soundness (N : ℕ+) (M : ℕ) (x0 x1 x2 x3 y0 y1 y2 y3 out0 out1 out2 out3 c0 c1 c2 c3 : ℕ)
    (h : out0 = (x0 + y0) % 256
    ∧ c0 = (x0 + y0) / 256
    ∧ out1 = (c0 + x1 + y1) % 256
    ∧ c1 = (c0 + x1 + y1) / 256
    ∧ out2 = (c1 + x2 + y2) % 256
    ∧ c2 = (c1 + x2 + y2) / 256
    ∧ out3 = (c2 + x3 + y3) % 256
    ∧ c3 = (c2 + x3 + y3) / 256)

    : out0 + 256 * out1 + 256^2 * out2 + 256^3 * out3 =
      (
        (x0 + 256 * x1 + 256^2 * x2 + 256^3 * x3)
        + (y0 + 256 * y1 + 256^2 * y2 + 256^3 * y3)
      ) % 2^32
  := by
  sorry

theorem equiv (N : ℕ+) (M : ℕ) (x y out carries : Limbs4 N M p) :
  (∀ X,
    (forallList (fullLookupSet (circuit N M x y out carries)) (fun lookup => lookup.prop X))
    -> (
      (forallList (fullConstraintSet (circuit N M x y out carries)) (fun constraint => X.eval constraint = 0))
      ↔
      spec N M x y out carries X
    )
  ) := by
  intro X


  -- TODO: ideally this whole block would be a tactic, this just
  -- substitutes all the constraints of the sub gadgets into the corresponding spec
  rw [fullConstraintSetGroupedEquivalence, circuit]
  simp [ByteLookup.lookup, fullConstraintSetGrouped, forallList, fullConstraintSetGrouped.foldl]

  intros hx0 hy0 hout0 hx1 hy1 hout1 hx2 hy2 hout2 hx3 hy3 hout3

  let equivAdd0 := Addition8.equiv N M (x.get 0) (y.get 0) (out.get 0) (carries.get 0) X
  simp [forallList, ByteLookup.lookup, Addition8.spec] at equivAdd0
  specialize equivAdd0 hx0 hy0 hout0
  rw [equivAdd0]

  let equivAdd1 := Addition8Full.equiv N M (x.get 1) (y.get 1) (out.get 1) (carries.get 0) (carries.get 1) X
  simp [forallList, ByteLookup.lookup, Addition8Full.spec] at equivAdd1
  specialize equivAdd1 hx1 hy1 hout1
  rw [equivAdd1]

  let equivAdd2 := Addition8Full.equiv N M (x.get 2) (y.get 2) (out.get 2) (carries.get 1) (carries.get 2) X
  simp [forallList, ByteLookup.lookup, Addition8Full.spec] at equivAdd2
  specialize equivAdd2 hx2 hy2 hout2
  rw [equivAdd2]

  let equivAdd3 := Addition8Full.equiv N M (x.get 3) (y.get 3) (out.get 3) (carries.get 2) (carries.get 3) X
  simp [forallList, ByteLookup.lookup, Addition8Full.spec] at equivAdd3
  specialize equivAdd3 hx3 hy3 hout3
  rw [equivAdd3]

  -- expand the spec
  rw [spec]
  simp [Limbs4.value]

  -- simplify a bit the statement
  set x0 := ZMod.val (X.eval (x.get 0))
  set x1 := ZMod.val (X.eval (x.get 1))
  set x2 := ZMod.val (X.eval (x.get 2))
  set x3 := ZMod.val (X.eval (x.get 3))
  set y0 := ZMod.val (X.eval (y.get 0))
  set y1 := ZMod.val (X.eval (y.get 1))
  set y2 := ZMod.val (X.eval (y.get 2))
  set y3 := ZMod.val (X.eval (y.get 3))
  set out0 := ZMod.val (X.eval (out.get 0))
  set out1 := ZMod.val (X.eval (out.get 1))
  set out2 := ZMod.val (X.eval (out.get 2))
  set out3 := ZMod.val (X.eval (out.get 3))
  set c0 := ZMod.val (X.eval (carries.get 0))
  set c1 := ZMod.val (X.eval (carries.get 1))
  set c2 := ZMod.val (X.eval (carries.get 2))
  set c3 := ZMod.val (X.eval (carries.get 3))

  -- at this point the entire statement is lifted and is about limbs
  -- and carries over ℕ, so we have to prove the actual relation
  constructor
  -- soundness
  · intro h
    have s := soundness N M x0 x1 x2 x3 y0 y1 y2 y3 out0 out1 out2 out3 c0 c1 c2 c3 (by sorry)
    simp at s
    exact s

  -- completeness
  · sorry


instance (N M : ℕ+) (x y out carries : Limbs4 N M p) : Constraint N M p :=
{
  circuit := circuit N M x y out carries,
  spec := spec N M x y out carries,
  equiv := equiv N M x y out carries
}

end Addition32

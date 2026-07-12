import Mathlib.Tactic

namespace LambdaEnv

inductive Trm (V : Type u) where
  | var  : V → Trm V
  | lam  : V → Trm V → Trm V
  | app  : Trm V → Trm V → Trm V
  | id   : Trm V
  | ext  : Trm V → V → Trm V → Trm V
  | comp : Trm V → Trm V → Trm V
  deriving Repr, DecidableEq

namespace Trm

/-- Isabelle `term_length`. -/
def length : Trm V → Nat
  | var _ => 1
  | lam _ M => 2 * length M
  | app M N => length M + length N + 1
  | id => 1
  | ext M _ N => length M + length N + 1
  | comp M N => length M * (length N + 1)

@[simp] theorem length_var (x : V) : length (.var x) = 1 := rfl
@[simp] theorem length_lam (x : V) (M : Trm V) :
    length (.lam x M) = 2 * length M := rfl
@[simp] theorem length_app (M N : Trm V) :
    length (.app M N) = length M + length N + 1 := rfl
@[simp] theorem length_id : length (.id : Trm V) = 1 := rfl
@[simp] theorem length_ext (M : Trm V) (x : V) (N : Trm V) :
    length (.ext M x N) = length M + length N + 1 := rfl
@[simp] theorem length_comp (M N : Trm V) :
    length (.comp M N) = length M * (length N + 1) := rfl

theorem length_pos (M : Trm V) : 0 < length M := by
  induction M with
  | var x => simp [length]
  | lam x M ih =>
      simpa [length] using Nat.mul_pos (by norm_num : 0 < 2) ih
  | app M N ihM ihN =>
      simp [length]
  | id => simp [length]
  | ext M x N ihM ihN =>
      simp [length]
  | comp M N ihM ihN =>
      simpa [length] using Nat.mul_pos ihM (Nat.succ_pos (length N))

theorem length_right_lt_comp (A B : Trm V) :
    length B < length (.comp A B) := by
  dsimp [length]
  have hA : 1 ≤ length A := Nat.succ_le_iff.mpr (length_pos A)
  calc
    length B < 1 * (length B + 1) := by simp
    _ ≤ length A * (length B + 1) := Nat.mul_le_mul_right _ hA

theorem add_mul_right_lt_mono {a b c : Nat} (h : a < b) :
    a + a * c < b + b * c := by
  nlinarith [Nat.zero_le c]

theorem add_mul_left_lt_mono {a b c : Nat} (ha : 0 < a) (hbc : b < c) :
    a + a * b < a + a * c := by
  nlinarith

theorem length_comp_sub_left_ext (U1 : Trm V) (x : V) (U2 V' : Trm V) :
    length (.comp U1 V') < length (.comp (.ext U1 x U2) V') := by
  dsimp [length]
  nlinarith [length_pos U2, length_pos V']

theorem length_comp_sub_right_ext (U1 : Trm V) (x : V) (U2 V' : Trm V) :
    length (.comp U2 V') < length (.comp (.ext U1 x U2) V') := by
  dsimp [length]
  nlinarith [length_pos U1, length_pos V']

theorem length_comp_sub_left_app (U1 U2 V' : Trm V) :
    length (.comp U1 V') < length (.comp (.app U1 U2) V') := by
  dsimp [length]
  nlinarith [length_pos U2, length_pos V']

theorem length_comp_sub_right_app (U1 U2 V' : Trm V) :
    length (.comp U2 V') < length (.comp (.app U1 U2) V') := by
  dsimp [length]
  nlinarith [length_pos U1, length_pos V']

theorem length_comp_sub_lamcomp_arg (x : V) (U W V' : Trm V) :
    length (.comp W V') < length (.comp (.comp (.lam x U) W) V') := by
  dsimp [length]
  have hFactor : 1 ≤ 2 * length U := by
    nlinarith [length_pos U]
  have hinner : length W < (2 * length U) * (length W + 1) := by
    calc
      length W < 1 * (length W + 1) := by simp
      _ ≤ (2 * length U) * (length W + 1) := Nat.mul_le_mul_right _ hFactor
  exact Nat.mul_lt_mul_of_pos_right hinner (Nat.succ_pos _)

theorem length_comp_sub_varcomp_arg (x : V) (W V' : Trm V) :
    length (.comp W V') < length (.comp (.comp (.var x) W) V') := by
  simp [length]

example (x : V) : length (.var x) = 1 := by simp

example (M N : Trm V) : length (.app M N) = length M + length N + 1 := by
  simp

end Trm

end LambdaEnv

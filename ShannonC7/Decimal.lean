import ShannonC7.CycleC7

/-!
# Exact Integer-Power Decimal Bridge for Shannon Capacity

This module provides a zero-rounding, pure-kernel bridge from exact natural-number power
inequalities `num ^ d ≤ den ^ d * N` to real lower bounds `(num : ℝ) / (den : ℝ) ≤ shannonCapacity G`.
For large exponents (`d > 256`), call sites can wrap `nat_pow_le_of_ble rfl` with
`set_option exponentiation.threshold 4096 in` to verify multi-thousand-digit bounds in
milliseconds inside Lean's C++ kernel with zero warnings and zero `native_decide`.
-/

namespace ShannonC7

/-- Pure real-analysis bridge: `num ^ d ≤ den ^ d * N` implies `num / den ≤ N ^ (1 / d)`.
Handles all edge cases (`num = 0`, `N = 0`) cleanly via `Real.le_rpow_inv_iff_of_pos`. -/
theorem le_rpow_of_nat_pow {d N num den : ℕ} (hd : 0 < d) (hden : 0 < den)
    (hpow : num ^ d ≤ den ^ d * N) :
    (num : ℝ) / (den : ℝ) ≤ (N : ℝ) ^ (1 / (d : ℝ)) := by
  have hden_pos : (0 : ℝ) < (den : ℝ) := Nat.cast_pos.mpr hden
  rw [one_div,
    Real.le_rpow_inv_iff_of_pos (div_nonneg (Nat.cast_nonneg num) hden_pos.le)
      (Nat.cast_nonneg N) (Nat.cast_pos.mpr hd),
    Real.rpow_natCast, div_pow, div_le_iff₀ (pow_pos hden_pos d), mul_comm]
  exact_mod_cast hpow

/-- Contract theorem (`PROJECT.md § 4.3`): exact integer-power lower bound on `shannonCapacity G`
via `strongPow G d`. -/
theorem le_shannonCapacity_of_nat_pow {V : Type*} [Fintype V] {G : SimpleGraph V}
    {d N num den : ℕ} (hd : 0 < d) (hden : 0 < den)
    (hN : N ≤ (strongPow G d).indepNum) (hpow : num ^ d ≤ den ^ d * N) :
    (num : ℝ) / (den : ℝ) ≤ shannonCapacity G :=
  calc (num : ℝ) / (den : ℝ)
      ≤ (N : ℝ) ^ (1 / (d : ℝ)) := le_rpow_of_nat_pow hd hden hpow
    _ ≤ ((strongPow G d).indepNum : ℝ) ^ (1 / (d : ℝ)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg N) (Nat.cast_le.mpr hN) (by positivity)
    _ ≤ shannonCapacity G := le_csSup (shannonSet_bddAbove G) ⟨d, hd, rfl⟩

/-- Companion theorem taking `N ≤ (strongPowPi G d).indepNum`. -/
theorem le_shannonCapacity_of_nat_pow_pi {V : Type*} [Fintype V] {G : SimpleGraph V}
    {d N num den : ℕ} (hd : 0 < d) (hden : 0 < den)
    (hN : N ≤ (strongPowPi G d).indepNum) (hpow : num ^ d ≤ den ^ d * N) :
    (num : ℝ) / (den : ℝ) ≤ shannonCapacity G :=
  le_shannonCapacity_of_nat_pow hd hden (by rwa [strongPow_indepNum_eq_pi]) hpow

/-- Companion theorem bridging `strongPow C7 d` directly to `SimpleGraph.cycleGraph 7`. -/
theorem le_shannonCapacity_cycleGraph7_of_nat_pow
    {d N num den : ℕ} (hd : 0 < d) (hden : 0 < den)
    (hN : N ≤ (strongPow C7 d).indepNum) (hpow : num ^ d ≤ den ^ d * N) :
    (num : ℝ) / (den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) := by
  rw [← shannonCapacity_c7_eq_cycleGraph]
  exact le_shannonCapacity_of_nat_pow hd hden hN hpow

/-- Kernel-friendly helper turning a definitional `Nat.ble` check (`rfl`) into
`num ^ d ≤ den ^ d * N`. For `d > 256`, wrap the call site in
`set_option exponentiation.threshold 4096 in` (or higher if needed) to suppress the
elaborator's default `256` exponent warning while keeping pure GMP kernel reduction. -/
theorem nat_pow_le_of_ble {num den d N : ℕ}
    (h : Nat.ble (num ^ d) (den ^ d * N) = true) :
    num ^ d ≤ den ^ d * N :=
  Nat.le_of_ble_eq_true h

end ShannonC7

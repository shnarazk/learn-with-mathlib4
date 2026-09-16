module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Bits
public import Mathlib.Tactic
public import Basic.Finset

theorem gt_zero_bits_length : ∀ n > 0, n.bits.length > 0 := by
  intro n n_gt_0
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases n0 : n = 0
    · grind
    · by_cases n_even : Even n
      · have : n = 2 * (n / 2) := by grind
        rw [this]
        replace this : (2 * (n / 2)).bits = false :: (n / 2).bits := by
          exact Nat.bit0_bits (n / 2) (by grind)
        simp [this]
      · have : n = 2 * (n / 2) + 1 := by grind
        rw [this]
        replace this : (2 * (n / 2) + 1).bits = true :: (n / 2).bits := by
          exact Nat.bit1_bits (n / 2)
        simp

theorem bits_eq_null_zero : ∀ n : ℕ, n.bits = [] → n = 0 := by
  intro n bits_null
  by_cases n0 : n = 0
  · simp [n0]
  · have : n.bits.length > 0 := by exact gt_zero_bits_length n (by grind)
    replace this : ¬n.bits.length = 0 := by grind
    replace bits_null : n.bits.length = 0 := by
      exact List.eq_nil_iff_length_eq_zero.mp bits_null
    contradiction

@[simp]
theorem congrBits (n : Nat) : ∀ m : ℕ, n = m → n.bits = m.bits := by
  intro m p
  exact List.reverse_inj.mp (congrArg List.reverse (congrArg Nat.bits p))

theorem congrBitsEq (n : Nat) : ∀ m : ℕ, n.bits = m.bits → n = m := by
  intro m p
  induction n using Nat.strongRecOn generalizing m with
  | ind n ih =>
    by_cases n_eq_0 : n = 0
    · simp [n_eq_0] at *
      rw [← Nat.zero_bits] at p
      have m0 : m = 0 := by exact base1 m p
      grind
    · by_cases q : Even n
      · have n2 : n = (n / 2) * 2 := by grind
        rw [n2] at p
        have n_ne_1 : ¬n = 1 := by grind
        replace p : false :: (n / 2).bits = m.bits := by
          have : ((n / 2) * 2).bits = false :: (n / 2).bits := by
            rw [mul_comm]
            exact Nat.bit0_bits (n / 2) (by grind)
          simp [← p, this]
        by_cases q' : Even m
        · have m2 : m = (m / 2) * 2 := by grind
          rw [m2] at p
          replace p : false :: (n / 2).bits = false :: (m / 2).bits := by
            done
            sorry
          replace p : (n / 2).bits = (m / 2).bits := by grind
          replace ih := ih (n / 2) (by sorry) (m / 2) p
          grind
        · have p' : m.bits = true :: (m / 2).bits := by
            have : m = 2 * (m / 2) + 1 := by grind
            rw (occs := .pos [1]) [this]
            refine Nat.bit1_bits (m / 2)
          rw [p'] at p
          simp at p
      · done

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

theorem bits_eq_nil_zero : ∀ n : ℕ, n.bits = [] → n = 0 := by
  intro n bits_nil
  by_cases n0 : n = 0
  · simp [n0]
  · have : n.bits.length > 0 := by exact gt_zero_bits_length n (by grind)
    replace this : ¬n.bits.length = 0 := by grind
    replace bits_nil : n.bits.length = 0 := by
      exact List.eq_nil_iff_length_eq_zero.mp bits_nil
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
      have m0 : m = 0 := by exact bits_eq_nil_zero m p
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
            have s : (2 * (m / 2)).bits = false :: (m / 2).bits := by
              have m_ge_2 : m ≥ 2 := by
                by_cases m_eq_0 : m = 0
                · simp [m_eq_0] at p
                · by_cases m_eq_1 : m = 1
                  · simp [m_eq_1] at q'
                  · have : m ≥ 2 := by grind
                    grind
              exact Nat.bit0_bits (m / 2) (by grind)
            rw (occs := .pos [1]) [mul_comm] at s
            simp [s] at p
            grind
          replace p : (n / 2).bits = (m / 2).bits := by grind
          replace ih := ih (n / 2) (by grind) (m / 2) p
          grind
        · have p' : m.bits = true :: (m / 2).bits := by
            have : m = 2 * (m / 2) + 1 := by grind
            rw (occs := .pos [1]) [this]
            refine Nat.bit1_bits (m / 2)
          rw [p'] at p
          simp at p
      · have n2 : n = (n / 2) * 2 + 1 := by grind
        rw [n2] at p
        replace p : true :: (n / 2).bits = m.bits := by
          have : ((n / 2) * 2 + 1).bits = true :: (n / 2).bits := by
            rw [mul_comm]
            refine Nat.bit1_bits (n / 2)
          simp [this] at p
          exact p
        by_cases q' : Even m
        · have p' : m.bits = false :: (m / 2).bits := by
            have : m = 2 * (m / 2) := by grind
            rw (occs := .pos [1]) [this]
            refine Nat.bit0_bits (m / 2) ?_
            · by_cases m_eq_0 : m = 0
              · simp [m_eq_0] at *
              · grind
          simp [p'] at p
        · have m2 : m = (m / 2) * 2 + 1 := by grind
          rw [m2] at p
          have : (2 * (m / 2) + 1).bits = true :: (m / 2).bits := by
            refine Nat.bit1_bits (m / 2)
          rw [mul_comm] at this
          simp [this] at p
          replace ih := ih (n / 2) (by grind) (m / 2) p
          grind

#guard (0 : Nat).bits == []
#guard (1 : Nat).bits == [true]
#guard (2 : Nat).bits == [false, true]

/-! Nat.bits is not bijective.
Because `[false]` is not in the image.
-/
public theorem bits_is_injective : Function.Injective Nat.bits := by
  rw [Function.Injective]
  exact fun ⦃a₁ a₂⦄ a ↦ congrBitsEq a₁ a₂ a

public theorem bit0_eq_false_iff_even {n : ℕ} (h : n > 0) :
    (∃ l : List Bool, n.bits = false :: l) ↔ Even n := by
  constructor
  · intro cons_false
    by_contra
    have nbits_ne_nil : n.bits ≠ [] := by
      by_contra
      have : n = 0 := by exact bits_eq_nil_zero n this
      replace h : ¬n = 0 := by exact Nat.ne_zero_iff_zero_lt.mpr h
      grind
    replace head_eq_false : n.bits.head nbits_ne_nil = false := by
      grind
    have head_eq_true : n.bits.head nbits_ne_nil = true := by
      replace even : n = 2 * (n / 2) + 1 := by grind
      have : n.bits = true :: (n / 2).bits := by
        rw (occs := .pos [1]) [even]
        refine Nat.bit1_bits (n / 2)
      replace this : n.bits.head nbits_ne_nil = true := by grind
      exact this
    grind
  · intro even
    have : n.bits = false :: (n / 2).bits := by
      have : n = 2 * (n / 2) := by grind
      rw (occs := .pos [1]) [this]
      exact Nat.bit0_bits (n / 2) (by grind)
    grind

module

public import Mathlib.Data.Finset.Basic
public meta import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic

open BigOperators
open Nat

section Playground

open Finset -- for `range`

variable (n : ℕ)

#guard ∑ i < 5, i + 100 = 110
#guard Finset.range 5 = Finset.range 4 ⊔ Finset.mk {4} (by simp)
#guard Finset.range 1 = Finset.range 0 ⊔ {0}
#guard (Finset.range 1) = {0}
#guard (Finset.range 0 ⊔ {0}) = {0}

example : Finset.range 5 = Finset.range 4 ⊔ Finset.mk {4} (by simp) := by rfl
example : Finset.mk {4} (by simp) = { 4 } := by rfl
example : Finset.range 5 = Finset.range 4 ⊔ {4} := by rfl
example : ∑ i ∈ range 5, i = ∑ i ∈ (Finset.range 4 ⊔ {4}), i := by rfl
example : ∑ i ∈ (Finset.range 4 ⊔ {4}), i =
    ∑ i ∈ Finset.range 4, i + ∑ i ∈ {4}, i := by
  rfl

/-- rangeを再帰的に定義する -/
lemma range_add_one_eq_sup_self : Finset.range (n + 1) = Finset.range n ⊔ {n} := by
  refine Finset.ext_iff.mpr ?_
  intro k
  constructor
  · intro kn1
    by_cases kn : k ∈ range n
    · rw [sup_eq_union] ; exact mem_union_left {n} kn
    · simp [range] at kn
      simp [range] at kn1
      rcases kn1 with a|b
      · simp ; left ; exact a
      · contrapose! b ; exact kn
  · intro H
    simp at H
    simp
    rcases H with A | B
    · exact Nat.le_of_eq A
    · exact le_of_succ_le B

end Playground

/-!
色々なところで必要になるので、ここで ∑ に関する基本変換ルールを証明しておく。
-/

@[grind =, simp]
public theorem sum_of_range_eq_sum_of_lt  {α : Type*} [AddCommMonoid α] :
    ∀ f : ℕ -> α, ∀ n : ℕ, (∑ i ∈ Finset.range n, f i = ∑ i < n, f i) := by
  intro f n
  induction n with
  | zero => rfl
  | succ i ih =>
    rw [Finset.sum_range_succ_comm, ih]
    exact Eq.symm (Finset.sum_Iio_add_zero_comm i f)

namespace Fibonacchi

/-- 多重再帰定義による Fibonacci -/
def fib (n : ℕ) : ℕ :=
  match n with
  | zero => 0
  | succ zero => 1
  | succ (succ n₂) => fib (n₂ + 1) + fib n₂

#guard fib 0 = 0
#guard fib 1 = 1
#guard fib 2 = 1
#guard fib 3 = 2
#guard fib 4 = 3
#guard fib 5 = 5

/-- これは単に定義を展開しただけ -/
lemma fib_is_fib (n : ℕ) : fib (succ (succ n)) = fib (succ n) + fib n := by
  rw [fib]

end Fibonacchi

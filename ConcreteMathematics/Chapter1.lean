module

public import Mathlib.Tactic

/-!
# 1章 再帰問題
-/

/-!
## 1.1 The Tower of Hanoi
-/
section Section1

/-- 最初に再帰により枚数`n`に対する手数を与える。 -/
@[grind =]
def t (n : ℕ) : ℕ :=
  match n with
  | 0    => 0
  | n'+1 => 2 * t n' + 1

#guard t 4 = 15
#guard t 6 = 63

/-- `t`を再帰を使わずに _closed form_ として表現 -/
@[simp]
theorem Equation1_2 : ∀ n : ℕ, t n = 2 ^ n - 1 := by
  intro n
  induction n with
  | zero       => rfl
  | succ n' ih => grind

/-! 新たな関数を導入してより簡潔に表現する -/

@[simp]
def U (n : ℕ) : ℕ := t n + 1

/-- `Equation1_2`の別表現 -/
theorem Equation1_2' : ∀ n : ℕ, U n = 2 ^ n := by
  intro n
  simp
  grind

end Section1

/-!
## 1.2 Lines in the plane
-/
section Section2

end Section2

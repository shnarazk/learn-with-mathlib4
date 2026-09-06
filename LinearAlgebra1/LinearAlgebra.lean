module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-!
線形代数の基礎
- Field(体): 加法と乗法を持ち、以下を満たすもの
    - 加法についての閉包, 単位元、逆元
    - 乗法における単位減、逆元
    - 加法と乗法の結合法則、交換法則、分配法則、
- AddCommGroup(加法交換群, 加法群):
    - 加法に関する群(閉包、結合法則、単位減、逆元)である
    - 交換法則を満たす(= アーベル群, Abelian group)
    - 単位元、逆元
- Module K V (加群): 環K, アーベル群Vに対して
    - K • V → V が以下を満たす: Rに関する分配法則、Vに関する分配法則と結合法則, Rの単位元は(•)の単位元
    ※ 環に乗法単位元、乗法逆元、乗法交換法則を加えたものが体
-/

-- 齋藤正彦、線形代数入門、東京大学出版会が手元にあるので、合わせてみたい　--

/-!
- AddZeroClass V:
- DistribSMul K V:
-/
example (a : K) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_add a u v

open Matrix

/- ベクトルは添字からの関数である! -/
#check ![(3 : ℝ), 2, 2] --  (![(0 : ℤ), 1] + ![1, 2])
#check (!![1, 2; 3, 4] *ᵥ ![1, 1])

section RnAsLS1

variable {n : ℕ}

/-- ℝⁿ が線型空間であることを証明するのは簡単 -/
noncomputable example : Field ℝ := inferInstance
noncomputable example : AddCommGroup (Fin n → ℝ) := inferInstance
noncomputable example : Module ℝ (Fin n → ℝ) := inferInstance

section sec_1_1

/-- 結合法則 -/
example (a b c : Fin n → ℝ) : (a + b) + c = a + (b + c) := by
  exact add_assoc a b c

/-- 交換法則 -/
example (a b : Fin n → ℝ) : a + b = b + a := by
  exact add_comm a b

/-- ゼロ元 -/
example (a : Fin n → ℝ) : a + 0 = a := by
  exact add_zero a

end sec_1_1

section sec_1_2

/-- 右からの分配法則 -/
example (c : ℝ) (a b : Fin n → ℝ) : c • (a + b) = c • a + c • b := by
  exact smul_add c a b

/-- 左からの分配法則 -/
example (c d : ℝ) (a : Fin n → ℝ) : (c + d) • a = c • a + d • a := by
  exact add_smul c d a

/-- 結合法則 -/
example (c d : ℝ) (a : Fin n → ℝ) : (c * d) • a = c • (d • a) := by
  exact mul_smul c d a

end sec_1_2

section sec_1_3

/-
ユークリッド空間が想定されていたようだ。
-/

example (a : EuclideanSpace ℝ (Fin 2)) : ‖a‖ = ((a 0)^2 + (a 1)^2).sqrt := by
  have zle (x y : ℝ) : 0 ≤ x^2 + y^2 := add_nonneg (sq_nonneg x) (sq_nonneg y)
  have (x : ℝ) (h: 0 ≤ x) : x ^ (2 : ℝ)⁻¹ = √x := by
    have h₁ (a b : ℝ): a = b → x ^ a = x ^ b := congrArg (HPow.hPow x)
    rw [h₁ 2⁻¹ (1/2), Eq.symm (Real.sqrt_eq_rpow x)]
    simp
  have h : ‖a‖ = dist a 0 := Eq.symm (dist_zero_right a)
  simp [h, dist]
  rw [this (a 0 ^ 2 + a 1 ^ 2) (zle (a 0) (a 1))]

end sec_1_3

end RnAsLS1

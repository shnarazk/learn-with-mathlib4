module

public import Mathlib.Tactic

/-
https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Matrix/Basic.lean
 - 基本属性、転置など
-/

public import Mathlib.Data.Matrix.Basic

/- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Matrix/ConjTranspose.lean
- 随伴行列
 -/
-- import Mathlib.Data.Matrix.ConjTranspose

/- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/LinearAlgebra/Matrix/Basis.lean
- ベクトルと行列の関係など
-/
public import Mathlib.LinearAlgebra.Matrix.Basis

/- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean
- 逆行列A⁻¹の定義
-/
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean
- 行列式の定義
-/
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

-- 存在していない
-- import Mathlib.LinearAlgebra.Matrix.Unitary

/- ユニタリ群の定義 -/
public import Mathlib.LinearAlgebra.UnitaryGroup

/- Real as Cauchy sequence -/
public import Mathlib.Data.Real.Basic

-- open Nat Finset Real
-- open Matrix

/-- `!`がベクターの、`!!`が配列の即値形式 -/
def m1 :=!![(0.0 : ℝ), 1, 0; 1, 1, 0; 0, 0, 1]

#check m1.det.cauchy.unquot.val

-- #eval m1.det.cauchy.unquot.val (10 : Nat)

-- #eval (repr (0 : ℝ)).cauchy
#norm_num m1.det
#norm_num !![(3 : ℝ), 1, 0; 6, -2, 1; 3, 1, 2].det
#norm_num !![(1 : ℝ), 2; 3, 4].det

-- def m0 := Matrix.zero -- Matrix.of (fun _ _ ↦ 0)

def m : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of (fun (m n : Fin 3) ↦ if m = n then 1 else 0.5)

/-- zeroがあるはずなのだがよくわからない -/
def m0 := m - m -- Matrix.of (fun _ _ ↦ 0)

#check m
-- #eval m
#eval (1 : Fin 2)

/- 実数はCauchy列として定義されているので、それっぽく表示するには皮を剥がないといけない -/
-- #eval m0 (0 : Fin 2) (1 : Fin 2) |>.cauchy.unquot.val 10
-- #eval m (0 : Fin 2) (1 : Fin 2) |>.cauchy.unquot.val 10

-- #eval m.det
-- #norm_num m.det

/-! ここから先はcopilotに聞きつつ進める -/
open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
-- variable {R : Type*} [CommRing R] [IsDomain R] [StarRing R]

/-- Define a unitary matrix on ℝ -/
def is_unitary (A : Matrix m m ℝ) : Prop := A * Aᴴ = 1

/-- FIXME -/
example (A : Matrix m m ℝ) : is_unitary A → A.det = 1 := by
  rintro h
  dsimp [is_unitary, conjTranspose] at h
  simp [Matrix.det]
  sorry

module

public import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Nat.Basic
public import Formula.Leibniz
-- import Lean
-- import «Le»
-- import «Combinator»

universe u

/--
  Measures the execution time of a monadic computation.

  Given a monadic computation, this function returns both the result of the computation
  and the time it took to execute in nanoseconds.
-/
@[inline]
public def elapsedTime {α : Type} {m : Type → Type u} [Monad m] [MonadLiftT BaseIO m] (x : m α) : m (α × Nat) := do
  let beg ← IO.monoNanosNow
  let val ← x
  let fin ← IO.monoNanosNow
  return (val, fin - beg)

/--
  Main entry point of the program.

  Calculates an approximation of π using the Leibniz formula with different numbers
  of terms and displays the results along with computation times.
-/
public def main : IO Unit := do
  let pairs : Nat := 10 * 1000 * 1000
  let (result, time) ← elapsedTime <| leibnizIO pairs
  IO.println s!"pi {pairs} = {result} in {time / 1000_000} msec."

  let pairs : Nat := 100 * 1000 * 1000
  let (result, time) ← elapsedTime <| leibnizIO pairs
  IO.println s!"pi {pairs} = {result} in {time / 1000_000} msec."
  /-
  let lines ← readData "lakefile.lean"
  lines.forM IO.println
  let x ← IO.getEnv "HOME"
  match x with
  | some x => IO.println x
  | none => pure ()
  -/

-- #eval Nat.gcd 20 5
-- #eval Nat.lcm 20 5
-- theorem ConcrateMath (n m : Nat) : (n % m) = max (Nat.gcd n m) (Nat.gcd m n) := sorry

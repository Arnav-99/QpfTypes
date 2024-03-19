import Mathlib

open Nat

universe u

/-- An alternate definition of `fin n` defined as an inductive type instead of a subtype of `Nat`. -/
inductive PFin2 : Nat → Type u
  /- `0` as a member of `fin (succ n)` (`fin 0` is empty) -/
  | fz {n} : PFin2 (succ n)
  | /-- `n` as a member of `fin (succ n)` -/
  fs {n} : PFin2 n → PFin2 (succ n)
  deriving DecidableEq

def func: (i : Fin2 2) → Type u
  | Fin2.fz => PFin2 1
  | Fin2.fs Fin2.fz => PFin2 1

def sample1 : (x : Fin2 2) → (x_1 : func x) → Nat
  | Fin2.fz, x => 0
  | Fin2.fs y, x => 0

def sample2 : (x : Fin2 2) → (x_1 : func x) → Nat
  | Fin2.fz, x => 0
  | Fin2.fs y, x => 0

def ofFin2 : Fin2 n → PFin2 n
  | .fz   => .fz
  | .fs i => .fs <| ofFin2 i

def toFin2 : PFin2 n → Fin2 n
  | .fz   => .fz
  | .fs i => .fs <| toFin2 i

@[simp]
theorem ofFin2_toFin2_iso {i : Fin2 n} :
  (toFin2 <| ofFin2 i) = i :=
by
  induction i
  . rfl
  . simp [ofFin2, toFin2, *]

example : sample1 = sample2 := by {
  apply funext
  intro x
  apply funext
  rw [← (@ofFin2_toFin2_iso 2 x)]
  intro x_1
  -- fails with result is not type correct error
  -- cases (ofFin2 x)
}

module

public import Dropping3Bodies.Basic

@[expose] public section

/-! The cyclic order on the three body indices, independent of the dynamics. -/

namespace DroppingThreeBodies

/-- The next body in the fixed positive cyclic order. -/
def cyclicNext (i : Fin 3) : Fin 3 :=
  match i with
  | 0 => 1
  | 1 => 2
  | _ => 0

/-- The previous body in the fixed positive cyclic order. -/
def cyclicPrev (i : Fin 3) : Fin 3 :=
  match i with
  | 0 => 2
  | 1 => 0
  | _ => 1

@[simp] theorem cyclicNext_zero : cyclicNext (0 : Fin 3) = 1 := rfl
@[simp] theorem cyclicNext_one : cyclicNext (1 : Fin 3) = 2 := rfl
@[simp] theorem cyclicNext_two : cyclicNext (2 : Fin 3) = 0 := rfl
@[simp] theorem cyclicPrev_zero : cyclicPrev (0 : Fin 3) = 2 := rfl
@[simp] theorem cyclicPrev_one : cyclicPrev (1 : Fin 3) = 0 := rfl
@[simp] theorem cyclicPrev_two : cyclicPrev (2 : Fin 3) = 1 := rfl

theorem cyclicPrev_cyclicNext (i : Fin 3) :
    cyclicPrev (cyclicNext i) = i := by
  fin_cases i <;> decide

theorem cyclicNext_cyclicPrev (i : Fin 3) :
    cyclicNext (cyclicPrev i) = i := by
  fin_cases i <;> decide

theorem cyclicNext_cyclicNext (i : Fin 3) :
    cyclicNext (cyclicNext i) = cyclicPrev i := by
  fin_cases i <;> decide

theorem cyclicPrev_cyclicPrev (i : Fin 3) :
    cyclicPrev (cyclicPrev i) = cyclicNext i := by
  fin_cases i <;> decide

theorem cyclicPrev_ne_self (i : Fin 3) : cyclicPrev i ≠ i := by
  fin_cases i <;> decide

theorem cyclicNext_ne_self (i : Fin 3) : cyclicNext i ≠ i := by
  fin_cases i <;> decide

theorem cyclicPrev_ne_cyclicNext (i : Fin 3) :
    cyclicPrev i ≠ cyclicNext i := by
  fin_cases i <;> decide

end DroppingThreeBodies

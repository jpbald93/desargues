import Desargues.Main

/-!
# A non-vacuity example over `ℚ`

Concrete triangles in the projective plane over `ℚ`, in perspective from `O = (0, 0, 1)`.
The three Desargues points `AB ∩ A'B'`, `BC ∩ B'C'`, `CA ∩ C'A'` are all nonzero, the two
triangles are genuine, and the theorem's conclusion holds — so the statement of
`Desargues.desargues_det` is not vacuous.
-/

open Matrix
open scoped Matrix

namespace Desargues

/-- The vertices of the example, as vectors of `ℚ³`. -/
def exO : Fin 3 → ℚ := ![0, 0, 1]
def exA : Fin 3 → ℚ := ![1, 0, 0]
def exB : Fin 3 → ℚ := ![0, 1, 0]
def exC : Fin 3 → ℚ := ![1, 1, 1]
def exA' : Fin 3 → ℚ := ![2, 0, 3]
def exB' : Fin 3 → ℚ := ![0, 5, -1]
def exC' : Fin 3 → ℚ := ![4, 4, 11]

/-- The three Desargues points of the example, computed explicitly. -/
def exP : Fin 3 → ℚ := ![-2, -15, 0]
def exQ : Fin 3 → ℚ := ![-4, -39, -4]
def exR : Fin 3 → ℚ := ![2, -12, -12]

/-- The example *is* in perspective from `O`: the three pairs of corresponding vertices are
joined by lines through `O`. -/
theorem ex_perspective :
    br exO exA exA' = 0 ∧ br exO exB exB' = 0 ∧ br exO exC exC' = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [br, exO, exA, exA', exB, exB', exC, exC', cross_apply, vec3_dotProduct,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- The example is nondegenerate: `O ≠ 0` and both triangles are genuine triangles. -/
theorem ex_nonvacuous : exO ≠ 0 ∧ br exA exB exC ≠ 0 ∧ br exA' exB' exC' ≠ 0 := by
  refine ⟨by norm_num [exO], ?_, ?_⟩ <;>
    norm_num [br, exA, exA', exB, exB', exC, exC', cross_apply, vec3_dotProduct,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- The three Desargues points of the example are genuine points of `ℙ²`. -/
theorem ex_points_ne_zero : exP ≠ 0 ∧ exQ ≠ 0 ∧ exR ≠ 0 :=
  ⟨by norm_num [exP], by norm_num [exQ], by norm_num [exR]⟩

/-- The three points of the example are indeed the intersections of the corresponding sides. -/
theorem ex_P_eq : (exA ⨯₃ exB) ⨯₃ (exA' ⨯₃ exB') = exP := by
  ext i
  fin_cases i <;>
    norm_num [exP, exA, exA', exB, exB', cross_apply, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]

theorem ex_Q_eq : (exB ⨯₃ exC) ⨯₃ (exB' ⨯₃ exC') = exQ := by
  ext i
  fin_cases i <;>
    norm_num [exQ, exB, exB', exC, exC', cross_apply, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]

theorem ex_R_eq : (exC ⨯₃ exA) ⨯₃ (exC' ⨯₃ exA') = exR := by
  ext i
  fin_cases i <;>
    norm_num [exR, exA, exA', exC, exC', cross_apply, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]

/-- The conclusion of Desargues's theorem for the example, deduced from the theorem. -/
theorem ex_desargues : br exP exQ exR = 0 := by
  have h := desargues_det (o := exO) (a := exA) (b := exB) (c := exC) (a' := exA')
    (b' := exB') (c' := exC') (by norm_num [exO])
    ex_perspective.1 ex_perspective.2.1 ex_perspective.2.2
  rw [← ex_P_eq, ← ex_Q_eq, ← ex_R_eq]
  exact h

/-- Direct numerical verification of the same conclusion. -/
theorem ex_desargues_compute : br exP exQ exR = 0 := by
  norm_num [br, exP, exQ, exR, cross_apply, vec3_dotProduct, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

end Desargues

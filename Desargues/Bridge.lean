import Desargues.Examples

/-!
# Definition bridges for the example

The example points `exO`, `exA'`, `exB'`, `exC'` of `Desargues.Examples`, tied to Mathlib's
projective plane `ℙ ℚ (Fin 3 → ℚ)`:

* `exO_eq_cross` : the centre `O` is Mathlib's intersection (`Projectivization.cross`) of the
  joining lines `AA'` and `BB'`;
* `exA'_isCollinear`, `exB'_isCollinear`, `exC'_isCollinear` : each of `A'`, `B'`, `C'` lies on
  the line joining `O` to the corresponding vertex, in the sense of Mathlib's
  `Projectivization.IsCollinear`.

(`br` is bridged to `Matrix.det` by `br_eq_det` and to `IsCollinear` by
`isCollinear_mk_of_br_eq_zero` / `br_eq_zero_of_isCollinear_mk`.)
-/

open Matrix Projectivization
open scoped Matrix LinearAlgebra.Projectivization

namespace Desargues

/-- The example vertices are nonzero vectors, i.e. genuine points of `ℙ²`. -/
theorem ex_vertices_ne_zero :
    exO ≠ 0 ∧ exA ≠ 0 ∧ exB ≠ 0 ∧ exC ≠ 0 ∧ exA' ≠ 0 ∧ exB' ≠ 0 ∧ exC' ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h
  · simpa [exO] using congrFun h 2
  · simpa [exA] using congrFun h 0
  · simpa [exB] using congrFun h 1
  · simpa [exC] using congrFun h 0
  · simpa [exA'] using congrFun h 0
  · simpa [exB'] using congrFun h 1
  · simpa [exC'] using congrFun h 0

/-- **Bridge for `exO`.** The centre of perspectivity is the intersection, computed by
Mathlib's `Projectivization.cross`, of the joining lines `AA'` and `BB'`. -/
theorem exO_eq_cross : mk ℚ exO ex_vertices_ne_zero.1 =
    cross (cross (mk ℚ exA ex_vertices_ne_zero.2.1) (mk ℚ exA' ex_vertices_ne_zero.2.2.2.2.1))
      (cross (mk ℚ exB ex_vertices_ne_zero.2.2.1) (mk ℚ exB' ex_vertices_ne_zero.2.2.2.2.2.1)) := by
  have h1 : exA ⨯₃ exA' ≠ 0 := by
    intro h; have := congrFun h 1
    norm_num [exA, exA', cross_apply, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at this
  have h2 : exB ⨯₃ exB' ≠ 0 := by
    intro h; have := congrFun h 0
    norm_num [exB, exB', cross_apply, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at this
  have h3 : (exA ⨯₃ exA') ⨯₃ (exB ⨯₃ exB') ≠ 0 := by
    intro h; have := congrFun h 2
    norm_num [exA, exA', exB, exB', cross_apply, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at this
  rw [cross_mk_of_cross_ne_zero _ _ h1, cross_mk_of_cross_ne_zero _ _ h2,
    cross_mk_of_cross_ne_zero _ _ h3, mk_eq_mk_iff_crossProduct_eq_zero]
  ext i
  fin_cases i <;>
    norm_num [exO, exA, exA', exB, exB', cross_apply, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]

/-- **Bridge for `exA'`.** `A'` lies on the line `OA` (Mathlib collinearity in `ℙ²`). -/
theorem exA'_isCollinear : IsCollinear ({mk ℚ exO ex_vertices_ne_zero.1,
    mk ℚ exA ex_vertices_ne_zero.2.1, mk ℚ exA' ex_vertices_ne_zero.2.2.2.2.1} :
      Set (ℙ ℚ (Fin 3 → ℚ))) :=
  isCollinear_mk_of_br_eq_zero _ _ _ ex_perspective.1

/-- **Bridge for `exB'`.** `B'` lies on the line `OB` (Mathlib collinearity in `ℙ²`). -/
theorem exB'_isCollinear : IsCollinear ({mk ℚ exO ex_vertices_ne_zero.1,
    mk ℚ exB ex_vertices_ne_zero.2.2.1, mk ℚ exB' ex_vertices_ne_zero.2.2.2.2.2.1} :
      Set (ℙ ℚ (Fin 3 → ℚ))) :=
  isCollinear_mk_of_br_eq_zero _ _ _ ex_perspective.2.1

/-- **Bridge for `exC'`.** `C'` lies on the line `OC` (Mathlib collinearity in `ℙ²`). -/
theorem exC'_isCollinear : IsCollinear ({mk ℚ exO ex_vertices_ne_zero.1,
    mk ℚ exC ex_vertices_ne_zero.2.2.2.1, mk ℚ exC' ex_vertices_ne_zero.2.2.2.2.2.2} :
      Set (ℙ ℚ (Fin 3 → ℚ))) :=
  isCollinear_mk_of_br_eq_zero _ _ _ ex_perspective.2.2

end Desargues

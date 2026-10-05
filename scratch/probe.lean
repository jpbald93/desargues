import Desargues.Main
open Matrix
open scoped Matrix
namespace ProbeEx
def exO : Fin 3 → ℚ := ![0, 0, 1]
def exA : Fin 3 → ℚ := ![1, 0, 0]
def exB : Fin 3 → ℚ := ![0, 1, 0]
def exC : Fin 3 → ℚ := ![1, 1, 1]
def exA' : Fin 3 → ℚ := ![2, 0, 3]
def exB' : Fin 3 → ℚ := ![0, 5, -1]
def exC' : Fin 3 → ℚ := ![4, 4, 11]
def exP : Fin 3 → ℚ := ![-2, -15, 0]
def exQ : Fin 3 → ℚ := ![-4, -39, -4]
def exR : Fin 3 → ℚ := ![2, -12, -12]

example : exP ≠ 0 ∧ exQ ≠ 0 ∧ exR ≠ 0 :=
  ⟨by norm_num [exP], by norm_num [exQ], by norm_num [exR]⟩

example : (exA ⨯₃ exB) ⨯₃ (exA' ⨯₃ exB') = exP := by
  ext i
  fin_cases i <;>
    norm_num [exP, exA, exA', exB, exB', cross_apply, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

example : (exB ⨯₃ exC) ⨯₃ (exB' ⨯₃ exC') = exQ := by
  ext i
  fin_cases i <;>
    norm_num [exQ, exB, exB', exC, exC', cross_apply, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

example : (exC ⨯₃ exA) ⨯₃ (exC' ⨯₃ exA') = exR := by
  ext i
  fin_cases i <;>
    norm_num [exR, exA, exA', exC, exC', cross_apply, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

example : Desargues.br exP exQ exR = 0 := by
  have h := Desargues.desargues_det (o := exO) (a := exA) (b := exB) (c := exC) (a' := exA')
    (b' := exB') (c' := exC')
    (by norm_num [exO])
    (by norm_num [Desargues.br, exO, exA, exA', cross_apply, vec3_dotProduct, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons])
    (by norm_num [Desargues.br, exO, exB, exB', cross_apply, vec3_dotProduct, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons])
    (by norm_num [Desargues.br, exO, exC, exC', cross_apply, vec3_dotProduct, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons])
  rwa [show (exA ⨯₃ exB) ⨯₃ (exA' ⨯₃ exB') = exP from by
        ext i; fin_cases i <;>
          norm_num [exP, exA, exA', exB, exB', cross_apply, Fin.reduceFinMk,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
            Matrix.tail_cons],
      show (exB ⨯₃ exC) ⨯₃ (exB' ⨯₃ exC') = exQ from by
        ext i; fin_cases i <;>
          norm_num [exQ, exB, exB', exC, exC', cross_apply, Fin.reduceFinMk,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
            Matrix.tail_cons],
      show (exC ⨯₃ exA) ⨯₃ (exC' ⨯₃ exA') = exR from by
        ext i; fin_cases i <;>
          norm_num [exR, exA, exA', exC, exC', cross_apply, Fin.reduceFinMk,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
            Matrix.tail_cons]] at h

end ProbeEx

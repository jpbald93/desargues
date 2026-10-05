import Desargues.Basic
import Mathlib.LinearAlgebra.Projectivization.Collinear
import Mathlib.LinearAlgebra.Projectivization.Constructions
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Collinearity in the projective plane `ℙ K (Fin 3 → K)`

`IsCollinear` is Mathlib's `Projectivization.IsCollinear`. The main results here translate
between the bracket `[u v w]` of representatives and collinearity, and between collinearity and
the existence of a nonzero vector orthogonal to all three representatives (which is exactly the
statement that the three *dual* points, i.e. the three lines, are concurrent).
-/

open Matrix Projectivization
open scoped Matrix LinearAlgebra.Projectivization

namespace Desargues

variable {K : Type*} [Field K]

/-- Three points of `ℙ²` whose representatives have vanishing bracket are collinear. -/
theorem isCollinear_mk_of_br_eq_zero {u v w : Fin 3 → K}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) (h : br u v w = 0) :
    IsCollinear ({mk K u hu, mk K v hv, mk K w hw} : Set (ℙ K (Fin 3 → K))) := by
  set s : Submodule K (Fin 3 → K) := Submodule.span K (Set.range ![u, v, w]) with hs
  have hsub : Subspace.submodule s.projectivization = s := OrderIso.apply_symm_apply _ _
  refine ⟨s.projectivization, ?_, ?_, ?_⟩
  · rw [hsub]; infer_instance
  · rw [hsub]
    have hli : ¬ LinearIndependent K ![u, v, w] := by
      intro hli
      have hunit : IsUnit (Matrix.of ![u, v, w]) :=
        (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of ![u, v, w])).mp hli
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hunit
      apply hunit
      rw [← br_eq_det, h]
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank] at hli
    have hle := finrank_range_le_card (R := K) ![u, v, w]
    simp only [Fintype.card_fin] at hli hle
    rw [hs]
    change ¬ Fintype.card (Fin 3) = Module.finrank K (Submodule.span K (Set.range ![u, v, w]))
      at hli
    change Module.finrank K (Submodule.span K (Set.range ![u, v, w])) ≤ 3 at hle
    simp only [Fintype.card_fin] at hli
    omega
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact (Submodule.mk_mem_projectivization_iff s hu).mpr (Submodule.subset_span ⟨0, rfl⟩)
    · exact (Submodule.mk_mem_projectivization_iff s hv).mpr (Submodule.subset_span ⟨1, rfl⟩)
    · exact (Submodule.mk_mem_projectivization_iff s hw).mpr (Submodule.subset_span ⟨2, rfl⟩)

/-- Collinear representatives have vanishing bracket. -/
theorem br_eq_zero_of_isCollinear_mk {u v w : Fin 3 → K}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : IsCollinear ({mk K u hu, mk K v hv, mk K w hw} : Set (ℙ K (Fin 3 → K)))) :
    br u v w = 0 := by
  obtain ⟨M, hfin, hrank, hsub⟩ := h
  by_contra hne
  have hli : LinearIndependent K ![u, v, w] := by
    have hunit : IsUnit (Matrix.of ![u, v, w]) := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      rw [← br_eq_det]
      exact hne
    exact (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of ![u, v, w])).mpr hunit
  have hmem : ∀ (x : Fin 3 → K) (hx : x ≠ 0),
      mk K x hx ∈ ({mk K u hu, mk K v hv, mk K w hw} : Set (ℙ K (Fin 3 → K))) →
        x ∈ M.submodule := fun x hx hS => (Subspace.mem_submodule_iff M hx).mpr (hsub hS)
  have hle : Submodule.span K (Set.range ![u, v, w]) ≤ M.submodule := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact hmem u hu (by simp)
    · exact hmem v hv (by simp)
    · exact hmem w hw (by simp)
  have h3 := finrank_span_eq_card hli
  have hmono := Submodule.finrank_mono hle
  simp only [Fintype.card_fin] at h3
  omega

/-- If a nonzero vector `o` is orthogonal to three vectors `x`, `y`, `z`, then those three
vectors are linearly dependent, so the bracket `[x y z]` vanishes. -/
lemma br_eq_zero_of_dotProduct_eq_zero {o x y z : Fin 3 → K} (ho : o ≠ 0)
    (hx : o ⬝ᵥ x = 0) (hy : o ⬝ᵥ y = 0) (hz : o ⬝ᵥ z = 0) : br x y z = 0 := by
  have hM : (Matrix.det (Matrix.of ![x, y, z]) : K) = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨o, ho, ?_⟩
    ext i
    fin_cases i <;> simp only [Matrix.mulVec_apply, dotProduct_comm] <;> assumption
  rw [br_eq_det]
  exact hM

/-- Three collinear points are concurrent in the dual plane: there is a nonzero `o` orthogonal
to all three representatives. -/
theorem exists_dotProduct_eq_zero_of_br_eq_zero {x y z : Fin 3 → K} (h : br x y z = 0) :
    ∃ o ≠ 0, o ⬝ᵥ x = 0 ∧ o ⬝ᵥ y = 0 ∧ o ⬝ᵥ z = 0 := by
  have hM : (Matrix.det (Matrix.of ![x, y, z]) : K) = 0 := by
    rw [← br_eq_det]
    exact h
  obtain ⟨o, ho, ho0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hM
  refine ⟨o, ho, ?_, ?_, ?_⟩
  · have := congrFun ho0 0
    rw [Matrix.mulVec_apply] at this
    rw [show (Matrix.of ![x, y, z]).row 0 = x from rfl] at this
    simpa only [dotProduct_comm, Pi.zero_apply] using this
  · have := congrFun ho0 1
    rw [Matrix.mulVec_apply] at this
    rw [show (Matrix.of ![x, y, z]).row 1 = y from rfl] at this
    simpa only [dotProduct_comm, Pi.zero_apply] using this
  · have := congrFun ho0 2
    rw [Matrix.mulVec_apply] at this
    rw [show (Matrix.of ![x, y, z]).row 2 = z from rfl] at this
    simpa only [dotProduct_comm, Pi.zero_apply] using this

end Desargues

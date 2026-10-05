import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.Ring

/-!
# Desargues's theorem: the determinant identity

Points of the projective plane over a field `K` are represented by nonzero vectors of
`K³ = Fin 3 → K` (homogeneous coordinates).

* the line through two distinct points `u`, `v` is the cross product `u ⨯₃ v`;
* the intersection of two distinct lines `l`, `m` is the cross product `l ⨯₃ m`;
* three points are collinear iff the bracket `[u v w] = u ⬝ᵥ v ⨯₃ w` vanishes
  (`[u v w] = det ![u, v, w]`, Mathlib's `triple_product_eq_det`).

This file contains the purely algebraic core, valid over an arbitrary commutative ring.
-/

open Matrix
open scoped Matrix

namespace Desargues

variable {K : Type*} [CommRing K]

/-- The bracket `[u v w]`: the determinant of the `3 × 3` matrix with rows `u`, `v`, `w`. -/
def br (u v w : Fin 3 → K) : K := u ⬝ᵥ v ⨯₃ w

lemma br_eq_det (u v w : Fin 3 → K) : br u v w = Matrix.det (Matrix.of ![u, v, w]) :=
  triple_product_eq_det u v w

/-- **The key identity.** The bracket of the three Desargues points of the two triangles
`(a, b, c)` and `(a', b', c')` factors into the brackets of the two triangles and the bracket
of the three joining lines `aa'`, `bb'`, `cc'`. -/
theorem desargues_det_identity (a b c a' b' c' : Fin 3 → K) :
    br ((a ⨯₃ b) ⨯₃ (a' ⨯₃ b')) ((b ⨯₃ c) ⨯₃ (b' ⨯₃ c')) ((c ⨯₃ a) ⨯₃ (c' ⨯₃ a'))
      = br a b c * br a' b' c' * br (a ⨯₃ a') (b ⨯₃ b') (c ⨯₃ c') := by
  simp only [br, cross_cross_eq_smul_sub_smul, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, cross_self, dot_self_cross, smul_zero, zero_sub, mul_zero, dotProduct_neg]
  simp only [cross_apply, vec3_dotProduct, cons_val_zero, cons_val_one, cons_val_two,
    Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons, head_cons]
  ring

end Desargues

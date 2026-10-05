import Desargues.Basic
import Desargues.Plane

/-!
# Desargues's theorem

Desargues's theorem in the projective plane `ℙ K (Fin 3 → K)` over a field `K`, with points
given by homogeneous coordinates (nonzero vectors of `K³`), the line through two distinct points
by the cross product, the intersection of two distinct lines by the cross product, and
collinearity by the vanishing of the bracket `[u v w] = u ⬝ᵥ v ⨯₃ w`.

Statement: two triangles `ABC` and `A'B'C'` in perspective from a point `O` (so `O`, `A`, `A'`
are collinear, and likewise for the other two pairs of corresponding vertices) have their three
pairs of corresponding sides meeting in collinear points.
-/

open Matrix Projectivization
open scoped Matrix LinearAlgebra.Projectivization

namespace Desargues

variable {K : Type*} [Field K]

/-- **Desargues's theorem, determinant form.** If the two triangles `(a, b, c)` and
`(a', b', c')` are in perspective from the point `o` (`o`, `a`, `a'` collinear and likewise for
the other two pairs of corresponding vertices), then the three "Desargues points"
`AB ∩ A'B'`, `BC ∩ B'C'`, `CA ∩ C'A'`, given by the cross products of the sides, are collinear.

The hypothesis `o ≠ 0` only says that `o` represents a point. The statement is insensitive to
degeneracies: if a pair of corresponding sides meets in no genuine point (the cross product of
the two lines vanishes), the corresponding "intersection point" is the zero vector and the
conclusion still holds. -/
theorem desargues_det {o a b c a' b' c' : Fin 3 → K} (ho : o ≠ 0)
    (hOa : br o a a' = 0) (hOb : br o b b' = 0) (hOc : br o c c' = 0) :
    br ((a ⨯₃ b) ⨯₃ (a' ⨯₃ b')) ((b ⨯₃ c) ⨯₃ (b' ⨯₃ c')) ((c ⨯₃ a) ⨯₃ (c' ⨯₃ a')) = 0 := by
  rw [desargues_det_identity]
  have hl : br (a ⨯₃ a') (b ⨯₃ b') (c ⨯₃ c') = 0 :=
    br_eq_zero_of_dotProduct_eq_zero ho hOa hOb hOc
  rw [hl, mul_zero]

/-- **Desargues's theorem** in the projective plane `ℙ K (Fin 3 → K)`.

Two triangles `ABC` and `A'B'C'`, in perspective from a point `O` (`O`, `A`, `A'` collinear,
etc.), have the property that the three points `AB ∩ A'B'`, `BC ∩ B'C'`, `CA ∩ C'A'` are
collinear.

Non-degeneracy hypotheses and why they are needed:

* `A ≠ B`, `B ≠ C`, `C ≠ A` (and the primed analogues): consecutive vertices of each triangle
  are distinct points, so that the three *sides* of each triangle are genuine lines, i.e. the
  cross products of the side representatives are nonzero and `cross` really computes the line
  through two points. Without them the "side" would be the zero vector;
* `AB ≠ A'B'`, `BC ≠ B'C'`, `CA ≠ C'A'`: corresponding sides are distinct lines, so that the
  three intersection points `AB ∩ A'B'`, ... are genuine points of `ℙ²` rather than the zero
  vector, and the conclusion says something about the actual intersection points.

No hypothesis on `O` beyond it being a point of `ℙ²`, and the triangles need not be disjoint, nor
non-degenerate as triangles, nor is any assumption needed on the characteristic of `K`. -/
theorem desargues_mk [DecidableEq K] {a b c a' b' c' o : Fin 3 → K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (ha' : a' ≠ 0) (hb' : b' ≠ 0) (hc' : c' ≠ 0)
    (ho : o ≠ 0)
    (hAB : mk K a ha ≠ mk K b hb) (hBC : mk K b hb ≠ mk K c hc)
    (hCA : mk K c hc ≠ mk K a ha)
    (hA'B' : mk K a' ha' ≠ mk K b' hb') (hB'C' : mk K b' hb' ≠ mk K c' hc')
    (hC'A' : mk K c' hc' ≠ mk K a' ha')
    (hOa : br o a a' = 0) (hOb : br o b b' = 0) (hOc : br o c c' = 0)
    (h₁ : cross (mk K a ha) (mk K b hb) ≠ cross (mk K a' ha') (mk K b' hb'))
    (h₂ : cross (mk K b hb) (mk K c hc) ≠ cross (mk K b' hb') (mk K c' hc'))
    (h₃ : cross (mk K c hc) (mk K a ha) ≠ cross (mk K c' hc') (mk K a' ha')) :
    IsCollinear ({cross (cross (mk K a ha) (mk K b hb)) (cross (mk K a' ha') (mk K b' hb')),
      cross (cross (mk K b hb) (mk K c hc)) (cross (mk K b' hb') (mk K c' hc')),
      cross (cross (mk K c hc) (mk K a ha)) (cross (mk K c' hc') (mk K a' ha'))} :
        Set (ℙ K (Fin 3 → K))) := by
  rw [cross_mk_of_ne ha hb hAB, cross_mk_of_ne hb hc hBC, cross_mk_of_ne hc ha hCA,
    cross_mk_of_ne ha' hb' hA'B', cross_mk_of_ne hb' hc' hB'C', cross_mk_of_ne hc' ha' hC'A']
    at *
  rw [cross_mk_of_ne _ _ h₁, cross_mk_of_ne _ _ h₂, cross_mk_of_ne _ _ h₃]
  exact isCollinear_mk_of_br_eq_zero _ _ _ (desargues_det ho hOa hOb hOc)

/-- **Converse of Desargues's theorem, determinant form.** If the three intersection points of
corresponding sides of two nondegenerate triangles are collinear, then the three joining lines
`AA'`, `BB'`, `CC'` are concurrent.

Non-degeneracy: the two triangles are nondegenerate, `[a b c] ≠ 0` and `[a' b' c'] ≠ 0`, i.e.
their vertices are not collinear (so the triangles are genuine triangles). Note that if either
triangle is degenerate, `[a b c] = 0` and the determinant identity gives no information about
`[AA' BB' CC']`. -/
theorem desargues_converse_det {a b c a' b' c' : Fin 3 → K}
    (hABC : br a b c ≠ 0) (hA'B'C' : br a' b' c' ≠ 0)
    (hPQR : br ((a ⨯₃ b) ⨯₃ (a' ⨯₃ b')) ((b ⨯₃ c) ⨯₃ (b' ⨯₃ c'))
      ((c ⨯₃ a) ⨯₃ (c' ⨯₃ a')) = 0) :
    br (a ⨯₃ a') (b ⨯₃ b') (c ⨯₃ c') = 0 := by
  have h := desargues_det_identity a b c a' b' c'
  rw [hPQR] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (mul_ne_zero hABC hA'B'C')

/-- **Converse of Desargues's theorem, projective form.** If the three points of intersection of
corresponding sides of two nondegenerate triangles are collinear, then the joining lines
`AA'`, `BB'`, `CC'` are concurrent.

The points `mk K (a ⨯₃ a') hAA'`, `mk K (b ⨯₃ b') hBB'`, `mk K (c ⨯₃ c') hCC'` represent the
*lines* `AA'`, `BB'`, `CC'` in the dual plane; `IsCollinear` for these three points of the dual
plane is exactly the statement that the three lines are concurrent (see
`Desargues.exists_dotProduct_eq_zero_of_br_eq_zero`). This is the statement obtained from
`desargues_mk` by duality. -/
theorem desargues_converse_mk [DecidableEq K] {a b c a' b' c' : Fin 3 → K}
    (hAA' : a ⨯₃ a' ≠ 0) (hBB' : b ⨯₃ b' ≠ 0) (hCC' : c ⨯₃ c' ≠ 0)
    (hABC : br a b c ≠ 0) (hA'B'C' : br a' b' c' ≠ 0)
    (hP : (a ⨯₃ b) ⨯₃ (a' ⨯₃ b') ≠ 0) (hQ : (b ⨯₃ c) ⨯₃ (b' ⨯₃ c') ≠ 0)
    (hR : (c ⨯₃ a) ⨯₃ (c' ⨯₃ a') ≠ 0)
    (hPQR : IsCollinear ({mk K ((a ⨯₃ b) ⨯₃ (a' ⨯₃ b')) hP,
      mk K ((b ⨯₃ c) ⨯₃ (b' ⨯₃ c')) hQ,
      mk K ((c ⨯₃ a) ⨯₃ (c' ⨯₃ a')) hR} : Set (ℙ K (Fin 3 → K)))) :
    IsCollinear ({mk K (a ⨯₃ a') hAA', mk K (b ⨯₃ b') hBB',
      mk K (c ⨯₃ c') hCC'} : Set (ℙ K (Fin 3 → K))) :=
  isCollinear_mk_of_br_eq_zero hAA' hBB' hCC'
    (desargues_converse_det hABC hA'B'C' (br_eq_zero_of_isCollinear_mk hP hQ hR hPQR))

end Desargues

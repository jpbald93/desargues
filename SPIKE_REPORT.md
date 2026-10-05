# SPIKE_REPORT — desargues

**Item 10** of the overnight Lean queue (2026-10-02). Mathlib "100 theorems" list #87
(Desargues's theorem), not in Mathlib. Lean v4.33.1, project `jack:~/desargues`, library
`Desargues`, mathlib rev v4.33.1.

**Status: DONE — gate PASS** (full `lake build` 0 errors / 0 warnings; forbidden-token grep
empty; `#print axioms` shows only `propext, Classical.choice, Quot.sound`).

---

## 1. Prior art (Step 0)

Searched Mathlib source + `docs/100.yaml`/`1000.yaml`, `gh search code/prs/repos`, AFP, Coq,
Mizar, web.

* **Mathlib**: no projective Desargues. `Projectivization/Constructions.lean` has the
  cross-product/orthogonality API we build on, but no Desargues statement.
* **Open Mathlib PR #37456** (2026-09-27, t-algebra): *affine parallel form*
  (`parallel_third_side_of_perspective`), i.e. the affine–parallel version of the theorem over
  an affine space, **not** the projective-plane statement, and **still unmerged**.
  https://github.com/leanprover-community/mathlib4/pull/37456
* **Isabelle AFP `Projective_Geometry`** (Anthony Bordg, 2018): proves Desargues from an
  axiomatisation of (higher) projective space geometry via incidence axioms.
  https://isa-afp.org/entries/Projective_Geometry.html
* **GeoCoq** (Coq, Tarski axiom system) and earlier Bordg work (*A Case Study in Formalizing
  Projective Geometry in Coq*, https://inria.hal.science/inria-00432810) — axiomatic/incidence
  style, not coordinates.
* Irrelevant hits: `Vilin97/lean-pool` (a *Proj* `Desargues.lean` naming convention, different
  topic), `level0000x/Lv-00` (generic template databases), `paulklemstine/Lean` Nearfield
  (non-Desarguesian planes, mentions only), `ImperialCollegeLondon/xena-UROP-2018`
  (Tarski 8, unrelated statement).

**Conclusion**: no complete coordinate-based formal proof of Desargues's theorem in Lean.
Proceeding (the affine-parallel PR is not the same theorem and is unmerged).

## 2. Informal check (Mathlib hygiene)

Python on the VM, `code/` (never on jack):

| script | what it checks | result |
|---|---|---|
| `check_desargues.py` | random perspective configs over ℚ (3000): `det(P,Q,R)==0` | 3000/3000 |
| | **negative control**: random non-perspective configs | 2946/2985 non-zero ⇒ the hypothesis is not automatic |
| `explore_desargues.py` | cross–cross identity, substituted identity (all degeneracies), hyp-version search 40 000 configs, hypothesis necessity, converse, dual side identities | 0 failures; counterexamples confirm `o ∥ a` breaks things |
| `identity_check.py` | the factorisation `[PQR] = [abc][a'b'c'][aa'][bb'][cc']` and its two pieces | 0 failures /1500 |
| `master_identity.py` | master identity, concurrent-lines vanishing, parametrised form, `P ∈ span{A,B}` | 0 failures |
| `reduced_identity.py` | component forms + reduced det expansion | 0 failures |
| `exhaustive_f5.py`, `degenerate_f5.py` | brute force over 𝔽₅² including all degeneracies (`o×a = 0` etc.) | 0 counterexamples in ~600k tested configs |
| `equiv.py` | ℚ-converse with strong hypotheses (4207 genuine non-perspective collinear configs) | 0 counterexamples |
| `formula_test.py` | intermediate form attempt | (discarded; not used in final proof) |

Numerics confirmed the theorem statement before any Lean work, including that the statement is
**non-vacuous** and that dropping the collinearity hypothesis admits counterexamples.

## 3. What was proved (exact Lean statements, copied from source)

All under `namespace Desargues`, over `variable {K : Type*} [Field K]`.

**Bracket** — `Desargues/Basic.lean:26`
```lean
def br (u v w : Fin 3 → K) : K := u ⬝ᵥ v ⨯₃ w
```
(`br u v w = Matrix.det (Matrix.of ![u, v, w])` by `br_eq_det`, `Basic.lean:28`.)

**Headline algebraic identity** — `Desargues/Basic.lean:34`
```lean
theorem desargues_det_identity (a b c a' b' c' : Fin 3 → K) :
    br ((a ⨯₃ b) ⨯₃ (a' ⨯₃ b')) ((b ⨯₃ c) ⨯₃ (b' ⨯₃ c')) ((c ⨯₃ a) ⨯₃ (c' ⨯₃ a'))
      = br a b c * br a' b' c' * br (a ⨯₃ a') (b ⨯₃ b') (c ⨯₃ c')
```
valid over any `CommRing`.

**Headline theorem (determinant form)** — `Desargues/Main.lean:33`
```lean
theorem desargues_det {o a b c a' b' c' : Fin 3 → K} (ho : o ≠ 0)
    (hOa : br o a a' = 0) (hOb : br o b b' = 0) (hOc : br o c c' = 0) :
    br ((a ⨯₃ b) ⨯₃ (a' ⨯₃ b')) ((b ⨯₃ c) ⨯₃ (b' ⨯₃ c')) ((c ⨯₃ a) ⨯₃ (c' ⨯₃ a')) = 0
```

**Headline theorem (projective plane `ℙ K (Fin 3 → K)`)** — `Desargues/Main.lean:59`
```lean
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
        Set (ℙ K (Fin 3 → K)))
```

**Converse (determinant form)** — `Desargues/Main.lean:88`
```lean
theorem desargues_converse_det {a b c a' b' c' : Fin 3 → K}
    (hABC : br a b c ≠ 0) (hA'B'C' : br a' b' c' ≠ 0)
    (hPQR : br ((a ⨯₃ b) ⨯₃ (a' ⨯₃ b')) ((b ⨯₃ c) ⨯₃ (b' ⨯₃ c'))
      ((c ⨯₃ a) ⨯₃ (c' ⨯₃ a')) = 0) :
    br (a ⨯₃ a') (b ⨯₃ b') (c ⨯₃ c') = 0
```

**Converse (projective)** — `Desargues/Main.lean:106`
```lean
theorem desargues_converse_mk [DecidableEq K] {a b c a' b' c' : Fin 3 → K}
    (hAA' : a ⨯₃ a' ≠ 0) (hBB' : b ⨯₃ b' ≠ 0) (hCC' : c ⨯₃ c' ≠ 0)
    (hABC : br a b c ≠ 0) (hA'B'C' : br a' b' c' ≠ 0)
    (hP : (a ⨯₃ b) ⨯₃ (a' ⨯₃ b') ≠ 0) (hQ : (b ⨯₃ c) ⨯₃ (b' ⨯₃ c') ≠ 0)
    (hR : (c ⨯₃ a) ⨯₃ (c' ⨯₃ a') ≠ 0)
    (hPQR : IsCollinear ({mk K ((a ⨯₃ b) ⨯₃ (a' ⨯₃ b')) hP,
      mk K ((b ⨯₃ c) ⨯₃ (b' ⨯₃ c')) hQ,
      mk K ((c ⨯₃ a) ⨯₃ (c' ⨯₃ a')) hR} : Set (ℙ K (Fin 3 → K)))) :
    IsCollinear ({mk K (a ⨯₃ a') hAA', mk K (b ⨯₃ b') hBB',
      mk K (c ⨯₃ c') hCC'} : Set (ℙ K (Fin 3 → K)))
```

**Supporting collinearity lemmas** — `Desargues/Plane.lean`
* `isCollinear_mk_of_br_eq_zero :27` — `br u v w = 0` ⇒ `IsCollinear {mk u, mk v, mk w}`;
* `br_eq_zero_of_isCollinear_mk :59` — the converse;
* `br_eq_zero_of_dotProduct_eq_zero :88` — nonzero `o` orthogonal to `x, y, z` ⇒ `br x y z = 0`
  (used for the perspective hypothesis);
* `exists_dotProduct_eq_zero_of_br_eq_zero :100` — collinear representatives admit a nonzero
  common orthogonal vector (this is what makes the converse statement "concurrent lines").

**Model / non-vacuity** — `Desargues/Examples.lean`
`ex_perspective`, `ex_nonvacuous`, `ex_points_ne_zero`, `ex_P_eq`, `ex_Q_eq`, `ex_R_eq`,
`ex_desargues`, `ex_desargues_compute`: the configuration
`O=(0,0,1)`, `A=(1,0,0)`, `B=(0,1,0)`, `C=(1,1,1)`, `A'=(2,0,3)`, `B'=(0,5,-1)`,
`C'=(4,4,11)` over ℚ, with Desargues points `P=(-2,-15,0)`, `Q=(-4,-39,-4)`,
`R=(2,-12,-12)` — all nonzero, both triangles genuine, `br P Q R = 0` proved both via
`desargues_det` and by direct computation.

## 4. Hypotheses: what they mean and why they are required

* `ha…hc'`: the six vertices are genuine points (nonzero representatives).
* `ho : o ≠ 0`: `O` is a genuine point (perspective centre).
* `A ≠ B`, `B ≠ C`, `C ≠ A`, `A' ≠ B'`, `B' ≠ C'`, `C' ≠ A'`: consecutive vertices distinct, so
  the three **sides** of each triangle are genuine lines (`cross` of the representatives is
  nonzero). Without this the "side" would be the zero vector and `cross` would not compute the
  line through two points.
* `AB ≠ A'B'`, `BC ≠ B'C'`, `CA ≠ C'A'`: corresponding sides are **distinct lines**, so the
  three intersection points are genuine points of `ℙ²`; otherwise `cross (line)(line) = 0`.
* `O`, `A`, `A'` collinear (`br o a a' = 0`, and cyclically): this is the perspective hypothesis.
  `desargues_det` shows that `o ≠ 0` plus these three brackets suffice; the numerical work
  (`independence_test.py`, `degenerate_f5.py`) shows the bracket hypotheses are *not* automatic
  and that dropping them admits counterexamples for the conclusion.
* The converse additionally needs **nondegenerate triangles** `[a b c] ≠ 0`, `[a' b' c'] ≠ 0`:
  the identity is a product `[PQR] = [abc]·[a'b'c']·[AA' BB' CC']`, so if either triangle is
  degenerate the vanishing of `[PQR]` gives no information.

## 5. Proof outline

1. `cross_cross_eq_smul_sub_smul` (Mathlib) rewrites every Desargues point `(u×v)×(u'×v')` as a
   linear combination of `u'` and `v'`; with `vec3_dotProduct`/`cross_apply`, `ring` closes the
   degree-12 polynomial identity `desargues_det_identity`. (~9 s to check.)
2. Perspective `br o a a' = 0` says the nonzero vector `o` is orthogonal to the three joining
   lines `a×a'`, `b×b'`, `c×c'`; by `Matrix.exists_mulVec_eq_zero_iff` the triple
   `[aa' bb' cc']` vanishes (linear dependence of three vectors in a 2-dimensional orthogonal
   complement).
3. Multiply: `[PQR] = [abc]·[a'b'c']·0 = 0`.
4. Collinearity translation uses Mathlib's `Projectivization.IsCollinear` (the same route as
   `jack:~/pascal-hexagon`, which we read for style and did not import or modify).
5. Converse: from `[PQR] = 0` and `[abc], [a'b'c'] ≠ 0`, the product identity forces
   `[AA' BB' CC'] = 0`; the projective form is the dual statement — the three lines `AA'`, `BB'`,
   `CC'`, regarded as points of the dual plane, are collinear, which by
   `exists_dotProduct_eq_zero_of_br_eq_zero` is exactly their concurrency.

Trust note: no division, no `decide`/`native_decide`, no `norm_num` on ℚ in the headline
proofs — the algebraic core is `ring` over an arbitrary commutative ring.

## 6. Gate output

```
$ grep -rnE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\bset_option\b|\bmacro|\belab|\bsyntax\b|\bnotation\b|import Lean" Desargues Desargues.lean
(no output; exit 1)

$ lake build
Build completed successfully (1804 jobs).        # 0 errors, 0 warnings

$ lake env lean scratch/Ax.lean
'Desargues.desargues_det_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.desargues_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.desargues_mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.desargues_converse_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.desargues_converse_mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.isCollinear_mk_of_br_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.br_eq_zero_of_isCollinear_mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.br_eq_zero_of_dotProduct_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.exists_dotProduct_eq_zero_of_br_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.ex_perspective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.ex_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.ex_points_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.ex_P_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.ex_Q_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.ex_R_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.ex_desargues' depends on axioms: [propext, Classical.choice, Quot.sound]
'Desargues.ex_desargues_compute' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 7. Not done / honest scope

* Only fields (`Field K`) for the projective corollaries; the algebraic core
  `desargues_det_identity` and `br` are over any `CommRing`.
* Converse is stated and proved as the dual statement, so "concurrency" appears as
  `IsCollinear` of the three lines in the dual plane; this is exactly concurrency
  (`exists_dotProduct_eq_zero_of_br_eq_zero`), but a reader wanting a point `O` with `O` on all
  three lines should read it through that lemma. No `IsConcurrent` predicate exists in Mathlib.
* No general projective-space version (dimension ≥ 3), no axiom-system version, no affine-form
  statement (the pending Mathlib PR covers the affine-parallel form independently).
* Not pushed to GitHub.
* Sources mirrored to `/home/work/Projects/desargues/` (Desargues.lean, Desargues/*.lean,
  lakefile.toml, lean-toolchain, lake-manifest.json, scratch/, code/), sha256-verified against
  jack.

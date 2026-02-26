import Mathlib

namespace DedekindDomain
open scoped NumberField Polynomial

/--
Parameters for the quadratic field `ℚ(√d)` considered in Lecture 2.1:
`d` is nonzero, nontrivial (`d ≠ 1`), and squarefree.
-/
class IsQuadraticParam (d : ℤ) : Prop where
  ne_zero : d ≠ 0
  ne_one : d ≠ 1
  squarefree : Squarefree d

/-- The ambient type `Q(√d)` used in Lecture 2.1. -/
structure Qsqrtd (d : ℤ) extends QuadraticAlgebra ℚ (d : ℚ) 0

/--
The ring of integers `𝓞 (Q(√d))`.
Typeclass assumptions `[Field (Qsqrtd d)] [NumberField (Qsqrtd d)]`
are exactly the legality conditions needed to form `𝓞`.
-/
abbrev 𝓞d (d : ℤ) [IsQuadraticParam d] [Field (Qsqrtd d)] [NumberField (Qsqrtd d)] : Type :=
  𝓞 (Qsqrtd d)

/--
Lecture 2.1: explicit description of quadratic integers as a subset of `Q(√d)`.

- if `d ≡ 1 (mod 4)`, then
  `O_d = {((a : ℚ) / 2) + ((b : ℚ) / 2)ω | a,b ∈ ℤ, a ≡ b (mod 2)}`
- otherwise
  `O_d = {a + bω | a,b ∈ ℤ}`.
-/
def quadraticIntegerSet (d : ℤ) [IsQuadraticParam d] : Set (Qsqrtd d) :=
  if _ : d % 4 = 1 then
    {x | ∃ a b : ℤ,
      x.re = (a : ℚ) / 2 ∧ x.im = (b : ℚ) / 2 ∧ a ≡ b [ZMOD 2]}
  else
    {x | ∃ a b : ℤ, x.re = (a : ℚ) ∧ x.im = (b : ℚ)}

/-- Unfolded membership characterization of `quadraticIntegerSet` (Lecture 2.1 formula). -/
theorem mem_quadraticIntegerSet_iff (d : ℤ) [IsQuadraticParam d] (x : Qsqrtd d) :
    x ∈ quadraticIntegerSet d ↔
      (if d % 4 = 1 then
        ∃ a b : ℤ, x.re = (a : ℚ) / 2 ∧ x.im = (b : ℚ) / 2 ∧ a ≡ b [ZMOD 2]
      else
        ∃ a b : ℤ, x.re = (a : ℚ) ∧ x.im = (b : ℚ)) := by
  rfl

/--
Lecture 2.1 statement shape:
membership in `𝓞 (Q(√d))` is equivalent to the explicit piecewise description.
-/
def od_mem_iff_statement (d : ℤ) [IsQuadraticParam d] [Field (Qsqrtd d)] [NumberField (Qsqrtd d)] :
    Prop :=
  ∀ x : Qsqrtd d, x ∈ Set.range (fun y : 𝓞d d => ((y : 𝓞 (Qsqrtd d)) : Qsqrtd d)) ↔
    x ∈ quadraticIntegerSet d

/-- Definition 2.5: conjugation on `Q(√d)`, `a + b√d ↦ a - b√d`. -/
def conj_qsqrtd (d : ℤ) (x : Qsqrtd d) : Qsqrtd d := ⟨⟨x.re, -x.im⟩⟩

/-- Definition 2.6: trace on `Q(√d)`. -/
def tr_qsqrtd (d : ℤ) (x : Qsqrtd d) : ℚ :=
  x.re + (conj_qsqrtd d x).re

/-- Definition 2.6: norm on `Q(√d)`. -/
def norm_qsqrtd (d : ℤ) (x : Qsqrtd d) : ℚ :=
  x.re * (conj_qsqrtd d x).re + (d : ℚ) * x.im * (conj_qsqrtd d x).im

@[simp] theorem conj_qsqrtd_re (d : ℤ) (x : Qsqrtd d) :
    (conj_qsqrtd d x).re = x.re := rfl

@[simp] theorem conj_qsqrtd_im (d : ℤ) (x : Qsqrtd d) :
    (conj_qsqrtd d x).im = -x.im := rfl

@[simp] theorem tr_qsqrtd_eq (d : ℤ) (x : Qsqrtd d) :
    tr_qsqrtd d x = 2 * x.re := by
  simp [tr_qsqrtd, two_mul]

@[simp] theorem norm_qsqrtd_eq (d : ℤ) (x : Qsqrtd d) :
    norm_qsqrtd d x = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := by
  simp [norm_qsqrtd, conj_qsqrtd, pow_two]

/--
Exercise 2.7
-/
def exercise_2_7_placeholder : Prop := True










end DedekindDomain

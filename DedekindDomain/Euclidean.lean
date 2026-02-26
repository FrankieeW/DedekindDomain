import Mathlib

namespace DedekindDomain
open scoped NumberField Polynomial

/-!
Lecture 10.1 -- 10.5 (integer rings as Euclidean domains).

This file provides a first formalization scaffold:
- Definition 10.1: Euclidean function
- Definition 10.2: norm Euclidean condition
- Lemma 10.3: approximation criterion
- Theorem 10.4: imaginary quadratic classification
- Theorem 10.5: PID examples
-/

section Lecture10_1_to_10_5

variable {R : Type*} [CommRing R] [IsDomain R]


/-- Definition 10.1: Euclidean function on an integral domain. -/
def IsEuclideanFunction (f : R → ℕ) : Prop :=
  ∀ a b : R, b ≠ 0 → ∃ q r : R, a = b * q + r ∧ (r = 0 ∨ f r < f b)

/-- A domain is Euclidean if it admits a Euclidean function. -/
def IsEuclideanDomain : Prop :=
  ∃ f : R → ℕ, IsEuclideanFunction f

variable {K : Type*} [Field K] [NumberField K]

/-- Definition 10.2: `𝓞 K` is norm Euclidean if `|N|` is a Euclidean function. -/
def IsNormEuclidean (normAbs : 𝓞 K → ℕ) : Prop :=
  IsEuclideanFunction (R := 𝓞 K) normAbs

variable (normAbsK : K → ℕ) (normAbsOK : 𝓞 K → ℕ)

/--
Approximation property in Lemma 10.3:
for every `α : K`, there exists `β : 𝓞 K` with `|N(α - β)| < 1`.
-/
def ApproximationProperty : Prop :=
  ∀ α : K, ∃ β : 𝓞 K, normAbsK (α - β.val) < 1

/--
Lemma 10.3 (statement scaffold):
norm Euclidean is equivalent to an approximation property
`∀ α, ∃ β, |N(α - β)| < 1`.

Proof idea from lecture notes:

`(→)` Assume `IsNormEuclidean`.
Given `α`, write `α = a / b` with `a,b ∈ 𝓞 K`, `b ≠ 0`.
From Euclideanity for `(a,b)`, choose `q,r ∈ 𝓞 K` with
`a = b*q + r` and `|N(r)| < |N(b)|`.
Then
`|N(α - q)| = |N(b⁻¹ (a - b*q))| = |N(b)|⁻¹ |N(r)| < 1`.
So take `β := q`.

`(←)` Assume the approximation property.
Given `a,b ∈ 𝓞 K` with `b ≠ 0`, set `α := a / b`.
Pick `β ∈ 𝓞 K` with `|N(α - β)| < 1`.
Define `q := β` and
`r := a - b*q = b*(α - β)`.
By multiplicativity of norm:
`|N(r)| = |N(b)| * |N(α - β)| < |N(b)|`.
Hence `|N|` is a Euclidean function on `𝓞 K`.
-/
theorem normEuclidean_iff_approximation
    (hcompat : ∀ x : 𝓞 K, normAbsOK x = normAbsK x.val) :
    IsNormEuclidean normAbsOK ↔ ApproximationProperty (K := K) normAbsK := by
  sorry
--------------------------------------------------------------


-- /--
-- Theorem 10.4 (statement scaffold):
-- for squarefree `d < 0`, norm Euclidean and Euclidean coincide exactly for
-- `d ∈ {-1, -2, -3, -7, -11}`.
-- -/



/--
Theorem 10.5:
`𝓞\_{-19}, 𝓞_{-43}, 𝓞_{-67}, 𝓞_{-163}` are PIDs
Thus these rings are examples of PIDs which are not Euclidean domains!
show `𝓞_{-19}` is a PID but not Euclidean.
-/
lemma 

end Lecture10_1_to_10_5

end DedekindDomain

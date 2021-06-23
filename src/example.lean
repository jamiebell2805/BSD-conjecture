-- example of an elliptic curve

import elliptic_curve_rationals -- <-- has a dodgy sorry I think

namespace elliptic_curve

/-- `E` is the elliptic curve $y^2=x^3-x$ over the integers.

## Notes

Cremona and Stein call this curve 32A2. Note in particular that it is a
global minimal model. The curve, and our model, have bad reduction
only at the prime 2. -/
def E : elliptic_curve := ⟨-1,0,by unfold disc; norm_num⟩

/- 

## The `E` namespace

This is like saying: Let $E$ be the elliptic curve $y^2=x^3-x$ over the
rationals. We now develop some theory which is specific to this curve $E$,
for example a computation of its rank (note: this is not yet done).

-/

namespace E -- our example of an elliptic curve.

/-- In standard Lean notation $y^2=x^3+ax+b$, $a=-1$.
  This is an implementation issue, so we teach it to the simplifier. -/
@[simp] lemma a : E.a = -1 := rfl
/-- In standard Lean notation $y^2=x^3+ax+b$, $b=0$.
  This is an implementation issue, so we teach it to the simplifier. -/
@[simp] lemma b : E.b = 0 := rfl

theorem five_is_good : 5 ∈ E.good_primes :=
begin
--  delta E,
  split,
  { norm_num },
  { simp [disc],
    norm_num },
end

/-- `good_five` is the prime 5 in the type of good primes for the integral model of E. -/
def good_five : ↥(E.good_primes) := ⟨5, five_is_good⟩

-- API for this definition, teach it to simplifier and then forget it
@[simp] lemma good_five_coe : (good_five : ℤ) = 5 := rfl
/-
The affine curve $y^2=x^3-x$ mod 5 has solutions
$(0,0),(\pm1,0),(2,\pm1),(3,\pm1)$,
so seven solutions.
-/
theorem five_points : E.p_points good_five = {(0,0),(1,0),(-1,0),(2,1),(2,-1),(3,1),(3,-1)} :=
begin
  delta p_points,
  simp,
  -- urk. Need tactical assistance
  sorry
end

theorem a_five : a_p E good_five = -2 :=
begin
  delta a_p,
  simp,
  let card_five_points := ↑(fintype.card (fintype ↥(E.p_points good_five))),
--  conv begin to_lhs, congr, skip, congr, end,
  change (5 : ℤ) - card_five_points = -2,
  suffices : card_five_points = 7,
    rw this, norm_num,
  have h := five_points,
  -- no idea
  sorry,  
end

end E

end elliptic_curve
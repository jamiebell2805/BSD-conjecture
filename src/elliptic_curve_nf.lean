import tactic
import group_theory.subgroup
import group_theory.finiteness
import group_theory.quotient_group
import data.fintype.card
import data.set.finite
import init.data.nat.lemmas
import data.nat.prime
import data.zmod.basic
import data.complex.basic
import analysis.special_functions.pow
import order.filter.at_top_bot
import analysis.analytic.basic
import analysis.calculus.iterated_deriv
import tprod
import algebra.module.basic
import field_theory.tower
import fg_quotient


local attribute [semireducible] with_zero
open_locale classical
noncomputable theory

variables {k : Type} [field k][algebra ℚ k][finite_dimensional ℚ k][char_zero k]

def disc (a b : k) : k :=
-16*(4*a^3+27*b^2)

structure elliptic_curve_nf (k : Type) [field k][algebra ℚ k][finite_dimensional ℚ k][char_zero k] :=
(a b : k)
(disc_nonzero : disc a b ≠ 0)

namespace elliptic_curve_nf

def finite_points (E : elliptic_curve_nf k) := {P : k × k // let ⟨x, y⟩ := P in 
  y^2  = x^3 + E.a*x + E.b}

def points (E : elliptic_curve_nf k) := with_zero E.finite_points

variable (E : elliptic_curve_nf k)

instance : has_zero (points E) := with_zero.has_zero

def neg_finite : finite_points E → finite_points E
| P := 
  let ⟨⟨x, y⟩, hP⟩ := P in 
  ⟨(x, -y), begin
    change y^2  = x^3 + E.a*x + E.b at hP,
    change (-y)^2 = x^3 + E.a*x + E.b,
    convert hP using 1,
    ring,
  end⟩

def neg : points E → points E
| 0 := 0
| (some P) := (some (neg_finite E P))


def double : points E → points E
| 0 := 0
| (some P) :=
let ⟨⟨x, y⟩, h⟩ := P in
if h2 : y = 0 then 0 else
  let A : k := E.a in
  let B : k := E.b in
  let d := 2*y in
  let sd := (3*x^2+A) in
  let td := y*d-sd*x in
  let x₂dd := sd^2-2*x*d^2 in
  let y₂ddd := sd*x₂dd+td*d^2 in
  let y₂' := -y₂ddd/d^3 in
  let x₂ := x₂dd/d^2 in
  some ⟨⟨x₂, y₂'⟩, begin
    show y₂'^2  = x₂^3 + A*x₂ + B,
    simp only [x₂, y₂', y₂ddd, x₂dd, sd, d, td],
    have h1: 2 * y ≠ 0,
    { simp,
      exact h2  },
    change y^2=x^3+A*x+B at h,
    apply eq_of_sub_eq_zero,
    rw ← sub_eq_zero at h,
    field_simp,
    have : (-((y * (2 * y) - (3 * x ^ 2 + A) * x) * (2 * y) ^ 2) + -((3 * x ^ 2 + A) * ((3 * x ^ 2 + A) ^ 2 - 2 * x * (2 * y) ^ 2))) ^ 2 * (((2 * y) ^ 2) ^ 3 * (2 * y) ^ 2) - ((2 * y) ^ 3) ^ 2 * (((3 * x ^ 2 + A) ^ 2 - 2 * x * (2 * y) ^ 2) ^ 3 * (2 * y) ^ 2 + A * ((3 * x ^ 2 + A) ^ 2 - 2 * x * (2 * y) ^ 2) * ((2 * y) ^ 2) ^ 3 + B * (((2 * y) ^ 2) ^ 3 * (2 * y) ^ 2)) = 16384*y^14*(y^2-(x^3+A*x+B)),
      ring,
    rw this, clear this,
    rw h,
    simp,
  end⟩

--(deterministic) timeout
def add : points E → points E → points E
| 0 P := P
| P 0 := P
| (some P) (some Q) :=
let ⟨⟨x1, y1⟩, h1⟩ := P in
let ⟨⟨x2, y2⟩, h2⟩ := Q in
if hd : x1 = x2 then (if y1 = y2 then double E (some P) else 0) else 
  let A : k := E.a in
  let B : k := E.b in
  let d := (x1 - x2) in
  let sd := (y1 - y2) in
  let td := y1*d-sd*x1 in
  let x₃dd := sd^2-(x1+x2)*d*d in
  let y₃ddd := sd*x₃dd+td*d*d in
  let x₃ := x₃dd/d^2 in
  let y₃' := -y₃ddd/d^3 in
  some ⟨⟨x₃, y₃'⟩, begin
    show y₃'^2  = x₃^3 + A*x₃ + B,
    simp only [x₃, y₃', y₃ddd, x₃dd, sd, d, td],
    field_simp,
    change y1^2=x1^3+A*x1+B at h1,
    change y2^2=x2^3+A*x2+B at h2,
    apply eq_of_sub_eq_zero,
    rw ← sub_eq_zero at h1 h2 hd,
    field_simp,
    have h : (-((y1 * (x1 - x2) - (y1 - y2) * x1) * (x1 - x2) * (x1 - x2)) + -((y1 - y2) * ((y1 - y2) ^ 2 - (x1 + x2) * (x1 - x2) * (x1 - x2)))) ^ 2 * (((x1 - x2) ^ 2) ^ 3 * (x1 - x2) ^ 2) - ((x1 - x2) ^ 3) ^ 2 * (((y1 - y2) ^ 2 - (x1 + x2) * (x1 - x2) * (x1 - x2)) ^ 3 * (x1 - x2) ^ 2 + A * ((y1 - y2) ^ 2 - (x1 + x2) * (x1 - x2) * (x1 - x2)) * ((x1 - x2) ^ 2) ^ 3 + B * (((x1 - x2) ^ 2) ^ 3 * (x1 - x2) ^ 2))
    =(x1-x2)^11*((y1^2-(x1^3+A*x1+B))*(y1^2-2*y1*y2+B+3*x1*x2^2-x2^3-x1^3+A*x2)+(y2^2-(x2^3+A*x2+B))*(-y2^2+2*y1*y2-B-3*x1^2*x2+x1^3+x2^3-A*x1)),
    ring,
    rw h, clear h,
    --rw h1, rw h2,
    --ring,
    sorry,
  end⟩

instance : has_neg (points E) := ⟨E.neg⟩ 
instance : has_add (points E) := ⟨E.add⟩

instance : add_comm_group (points E) :=
{ zero := 0,
  add := has_add.add,
  neg := has_neg.neg,
  zero_add := begin
    intro a,
    cases a,
    { refl },
    { refl },
  end,
  add_zero := begin
    intro a,
    cases a,
    { refl },
    { refl },
  end,
  add_assoc := begin
    sorry,
  end,
  add_left_neg := begin
    rintro ⟨⟨x,y⟩,h⟩,
    {refl},
    
    


    sorry,
  end,
  add_comm := begin
    intros a b,
    cases a,
    cases b,
    {refl},
    {refl},
    cases b,
    {refl},
    

    

    sorry,
  end,
}

theorem fg : add_group.fg (points E) := begin
  sorry,
end

def torsion_points (E : elliptic_curve_nf k) : (set (points E)) := 
{P | ∃ (n : ℤ), (n • P = 0)∧(n ≠ 0)}

def torsion_subgroup (E : elliptic_curve_nf k) : add_subgroup (points E) :=
{ carrier := (torsion_points E),
  zero_mem' := begin
    unfold torsion_points,
    rw set.mem_set_of_eq,
    use 1,
    simp,
  end,
  add_mem' := begin
    unfold torsion_points at *,
    intros a b ha hb,
    cases ha with na hna,
    cases hna with ha1 ha2,
    cases hb with nb hnb,
    cases hnb with hb1 hb2,
    rw set.mem_set_of_eq,
    use na*nb,
    split,
    { rw smul_add,
      rw mul_comm,
      rw mul_smul,
      rw ha1,
      rw mul_comm,
      rw mul_smul,
      rw hb1,
      simp},
    { simp,
      tauto
    },
  end,
  neg_mem' := begin
    unfold torsion_points at *,
    intros x hx,
    cases hx with n hn,
    cases hn with hn1 hn2,
    rw set.mem_set_of_eq,
    use n,
    rw smul_neg,
    rw hn1,
    simp,
    exact hn2,
  end,
}

def torsion_free (E : elliptic_curve_nf k) := 
  (quotient_add_group.quotient (torsion_subgroup E))

instance: add_comm_group (torsion_free E) := begin
  unfold torsion_free,
  apply_instance,
end


theorem torsion_free_fg : add_group.fg (torsion_free E) := begin
  apply add_fg_quotient_of_fg,
  apply fg, 
end

def generators (E : elliptic_curve_nf k) := 
  {S : set (torsion_free E) | (set.finite S) ∧ (add_subgroup.closure S = ⊤)}

def sizes (E : elliptic_curve_nf k) : (set ℕ) :=
  {n : ℕ | ∃ (S : generators E), (fintype.card (fintype S)) = n}

theorem sizes_non_empty : ∃ (n : ℕ), (n ∈ sizes E) := begin
  unfold sizes,
  have h : ∃ (S : set (torsion_free E)), (add_subgroup.closure S = ⊤) ∧ (S.finite),
  {rw ← add_group.fg_iff,
  exact torsion_free_fg E},
  cases h with S hS,
  cases hS with hclosure hfinite,
  use fintype.card (fintype S),
  rw set.mem_set_of_eq,
  use S,
  {simp only [elliptic_curve_nf.generators.equations._eqn_1],
  rw set.mem_set_of_eq,
  exact ⟨hfinite, hclosure⟩},
  {refl},
end
open_locale classical
noncomputable def rank (E : elliptic_curve_nf k) : ℕ :=
  nat.find (sizes_non_empty E)
  
def good_primes (E : elliptic_curve_nf k): (set k) :=sorry 
--{p : ℕ | nat.prime p ∧ ¬ (↑p ∣ (disc E.a E.b))}

-- def p_points (E : elliptic_curve_nf k) (p : good_primes E k) := sorry
--   {P : zmod p × zmod p | let ⟨x, y⟩ := P in y^2  = x^3 + E.a*x + E.b}

-- noncomputable def a_p (E : elliptic_curve) (p : good_primes E) : ℤ := 
--   p - fintype.card (fintype (p_points E p))

def half_plane := {z : ℂ // complex.re z > 3/2}

instance : has_coe half_plane ℂ := ⟨subtype.val⟩

-- noncomputable def local_factor (E : elliptic_curve) (s : ℂ) : good_primes E → ℂ
-- | p := 1 - (a_p E p) * p ^ (-s) + p ^ (1-2*s)

-- theorem hasse_bound (E :elliptic_curve) (p : good_primes E) : abs(a_p E p) ≤ 2 * p^(1/2) := begin
--  sorry,
-- end

-- theorem converges (E : elliptic_curve) (s : half_plane) : prodable (local_factor E s) := begin
--   sorry,
-- end

-- noncomputable def L_function_product (E : elliptic_curve) (s : half_plane) : ℂ :=
-- 1/(tprod (local_factor E s))

-- theorem analytic_continuation: ∃ f : ℂ → ℂ, (differentiable ℂ f)∧(∀ z : half_plane, f z = L_function_product E z)
-- ∧ (∀ g : ℂ → ℂ, (differentiable ℂ g)∧(∀ z : half_plane, g z = L_function_product E z) → g = f) := begin
--   sorry,
-- end

-- noncomputable def L_function : ℂ → ℂ := classical.some (analytic_continuation E)

-- noncomputable def L_derivative (E : elliptic_curve) : ℕ → ℂ → ℂ
-- |n := iterated_deriv n (L_function E)

-- theorem has_order_of_vanishing : ∃ n : ℕ, L_derivative E n 1 ≠ 0 := begin
--   sorry,
-- end

-- noncomputable def analytic_rank (E : elliptic_curve) : ℕ :=
--   nat.find (has_order_of_vanishing E)

-- theorem BSD : analytic_rank E = rank E := begin
--   sorry,
-- end

end elliptic_curve_nf

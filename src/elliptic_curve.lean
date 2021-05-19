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


local attribute [semireducible] with_zero
def disc (a b : ℤ) : ℤ :=
-16*(4*a^3+27*b^2)

structure elliptic_curve :=
(a b : ℤ)
(disc_nonzero : disc a b ≠ 0)

namespace elliptic_curve

def finite_points (E : elliptic_curve) := {P : ℚ × ℚ // let ⟨x, y⟩ := P in 
  y^2  = x^3 + E.a*x + E.b}

def points (E : elliptic_curve) := with_zero E.finite_points

variable (E : elliptic_curve)

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
  --line above doesn't seem to work

def double : points E → points E
| 0 := 0
| (some P) :=
let ⟨⟨x, y⟩, h⟩ := P in
if h2 : y = 0 then 0 else
  let d := 2*y in
  let sd := (3*x^2+E.a) in
  let td := y*d-sd*x in
  let x₂dd := sd^2-2*x*d^2 in
  let y₂ddd := sd*x₂dd+td*d^3 in
  let y₂' := -y₂ddd/d^3 in
  let x₂ := x₂dd/d^2 in
  some ⟨⟨x₂, y₂'⟩, begin
  sorry,
  end⟩

def add : points E → points E → points E
| 0 P := P
| P 0 := P
| (some P) (some Q) :=
let ⟨⟨x1, y1⟩, h1⟩ := P in
let ⟨⟨x2, y2⟩, h2⟩ := Q in
if hd : x1 = x2 then (if y1 = y2 then double E (some P) else 0) else 
  let d := (x1 - x2) in
  let sd := (y1 - y2) in
  let td := y1*d-sd*x1 in
  let x3dd := sd^2-(x1+x2)*d*d in
  let y3ddd := sd*x3dd+td*d*d in
  let x₃ := x3dd/d^2 in
  let y₃' := -y3ddd/d^3 in
  some ⟨⟨x₃, y₃'⟩, begin
    sorry,
  end⟩

instance : has_neg (points E) := ⟨E.neg⟩ 
instance : has_add (points E) := ⟨E.add⟩

instance : add_comm_group (points E) :=
{ zero := 0,
  add := has_add.add,
  neg := has_neg.neg,
  zero_add := begin
    sorry,
  end,
  add_zero := begin
    sorry,
  end,
  add_assoc := begin
    sorry,
  end,
  add_left_neg := begin
    sorry,
  end,
  add_comm := begin
    sorry,
  end,
}

theorem fg : add_group.fg (points E) := begin
  sorry,
end

def torsion_points (E : elliptic_curve) : (set (points E)) := 
{P | ∃ (n : ℤ), (n • P = 0)}

def torsion_subgroup (E : elliptic_curve) : add_subgroup (points E) :=
{ carrier := (torsion_points E),
  zero_mem' := begin
    unfold torsion_points,
    rw set.mem_set_of_eq,
    use 0,
    simp,
  end,
  add_mem' := begin
    unfold torsion_points at *,
    intros a b ha hb,
    cases ha with na hna,
    cases hb with nb hnb,
    rw set.mem_set_of_eq,
    use na*nb,
    rw smul_add,
    rw mul_comm,
    rw mul_smul,
    rw hna,
    rw mul_comm,
    rw mul_smul,
    rw hnb,
    simp,
  end,
  neg_mem' := begin
    unfold torsion_points at *,
    intros x hx,
    cases hx with n hn,
    rw set.mem_set_of_eq,
    use n,
    rw smul_neg,
    rw hn,
    simp,
  end,
}

def torsion_free (E : elliptic_curve) := 
  (quotient_add_group.quotient (torsion_subgroup E))

instance: add_comm_group (torsion_free E) := begin
  unfold torsion_free,
  apply_instance,
end

theorem torsion_free_fg : add_group.fg (torsion_free E) := begin
  sorry,
end

def generators (E : elliptic_curve) := 
  {S : set (torsion_free E) | (set.finite S) ∧ (add_subgroup.closure S = ⊤)}

def sizes (E : elliptic_curve) : (set ℕ) :=
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
  {simp only [elliptic_curve.generators.equations._eqn_1],
  rw set.mem_set_of_eq,
  exact ⟨hfinite, hclosure⟩},
  {refl},
end
open_locale classical
noncomputable def rank (E : elliptic_curve) : ℕ :=
  nat.find (sizes_non_empty E)
  
def good_primes := {p : ℕ | nat.prime p ∧ ¬ (↑p ∣ (disc E.a E.b))}

def p_points (E : elliptic_curve) (p : good_primes E) :=
  {P : zmod p × zmod p | let ⟨x, y⟩ := P in y^2  = x^3 + E.a*x + E.b}

noncomputable def a_p (E : elliptic_curve) (p : good_primes E) : ℤ := 
  p - fintype.card (fintype (p_points E p))

def half_plane := {z : ℂ | complex.re z > 3/2}

noncomputable def local_factor (E : elliptic_curve) (s : ℂ) : good_primes E → ℂ
| p := 1 - (a_p E p) * p ^ (-s) + p ^ (1-2*s)

theorem hasse_bound (E :elliptic_curve) (p : good_primes E) : abs(a_p E p) ≤ 2 * p^(1/2) := begin
 sorry,
end

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
noncomputable theory
open finset filter function classical
open_locale topological_space classical big_operators nnreal

variables [comm_monoid α] [topological_space α]

def has_prod (f : β → α) (a : α) : Prop := tendsto (λs:finset β, ∏ b in s, f b) at_top (𝓝 a)

def prodable (f : β → α) : Prop := ∃a, has_prod f a

@[irreducible] def tprod {β} (f : β → α) := if h : prodable f then classical.some h else 1

theorem converges (E : elliptic_curve) (s : half_plane) : prodable (local_factor E s) := begin
  sorry,
end

def L_function_product (E : elliptic_curve) : half_plane → ℂ
| s := 1/(tprod (local_factor E s))

theorem analytic_continuation: ∃ f : ℂ → ℂ, (differentiable ℂ f)∧(∀ z : half_plane, f z = L_function_product E z)
∧ (∀ g : ℂ → ℂ, (differentiable ℂ g)∧(∀ z : half_plane, g z = L_function_product E z) → g = f) := begin
  sorry,
end

noncomputable def L_function : ℂ → ℂ := classical.some (analytic_continuation E)

def L_derivative (E : elliptic_curve) : ℕ → ℂ → ℂ
|n := iterated_deriv n (L_function E)

theorem has_order_of_vanishing : ∃ n : ℕ, L_derivative E n 1 ≠ 0 := begin
  sorry,
end

noncomputable def analytic_rank (E : elliptic_curve) : ℕ :=
  nat.find (has_order_of_vanishing E)

theorem BSD : analytic_rank E = rank E := begin
  sorry,
end

end elliptic_curve

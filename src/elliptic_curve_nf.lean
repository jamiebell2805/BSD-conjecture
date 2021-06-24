import data.nat.prime
import data.zmod.basic
import data.complex.basic
import analysis.special_functions.pow
import analysis.analytic.basic
import analysis.calculus.iterated_deriv
import tprod
import algebra.module.basic
import field_theory.tower
import fg_quotient


local attribute [semireducible] with_zero
open_locale classical
noncomputable theory

variables {k : Type} [field k][char_zero k][finite_dimensional ℚ k]

def disc (a b : k) : k :=
-16*(4*a^3+27*b^2)

structure elliptic_curve_nf (k : Type) [field k][char_zero k][finite_dimensional ℚ k] :=
(a b : k)
(disc_nonzero : disc a b ≠ 0)

namespace elliptic_curve_nf

variable (E : elliptic_curve_nf k)

def finite_points (E : elliptic_curve_nf k) := {P : k × k // let ⟨x, y⟩ := P in 
  y^2  = x^3 + E.a*x + E.b}

lemma finite_points.ext_iff {x1 y1 : k} (h1 : y1^2  = x1^3 + E.a*x1 + E.b)
  {x2 y2 : k} (h2 : y2^2  = x2^3 + E.a*x2 + E.b) :
  (⟨(x1, y1), h1⟩ : E.finite_points) = ⟨(x2, y2), h2⟩ ↔ x1 = x2 ∧ y1 = y2 :=
begin
  split,
  { intro h,
    rw subtype.ext_iff at h,
    change (x1, y1) = (x2, y2) at h,
    exact prod.mk.inj h },
  { rintro ⟨rfl, rfl⟩,
    refl },
end

def points (E : elliptic_curve_nf k) := with_zero E.finite_points

instance : has_zero (points E) := with_zero.has_zero

def points_mk {x y : k} (h : y^2  = x^3 + E.a*x + E.b) : points E := some ⟨⟨x, y⟩, h⟩

lemma ext_iff
  {x1 y1 : k} (h1 : y1^2  = x1^3 + E.a*x1 + E.b)
  {x2 y2 : k} (h2 : y2^2  = x2^3 + E.a*x2 + E.b) :
  E.points_mk h1 = E.points_mk h2 ↔ x1 = x2 ∧ y1 = y2 :=
begin
  split,
  { intro h,
    change some _ = some _ at h,
    rw option.some_inj at h,
    rwa finite_points.ext_iff at h },
  { rintro ⟨rfl, rfl⟩,
    refl }
end

def is_finite (P : points E) := ∃ {x y : k} (h : y^2  = x^3 + E.a*x + E.b), P = E.points_mk h

lemma not_is_finite_zero : ¬ E.is_finite 0.

lemma is_finite_some (P : finite_points E) : E.is_finite (some P) :=
begin
  rcases P with ⟨⟨x, y⟩, h⟩,
  use [x, y, h],
  refl,
end

def x_coord : Π {P : points E}, E.is_finite P → k
| none h0 := false.elim (E.not_is_finite_zero h0) -- 0 can't happen
| (some ⟨(x,y),h⟩) _ := x

lemma x_coord_some {x y : k} (h : y^2  = x^3 + E.a*x + E.b) :
  E.x_coord (E.is_finite_some ⟨(x,y),h⟩) = x := rfl

def y_coord : Π {P : points E}, E.is_finite P → k
| none h0 := false.elim (E.not_is_finite_zero h0)
| (some ⟨(x,y),h⟩) _ := y

lemma y_coord_some {x y : k} (h : y^2  = x^3 + E.a*x + E.b) :
  E.y_coord (E.is_finite_some ⟨(x,y),h⟩) = y := rfl

lemma is_zero_or_finite (P : points E) :
  P = 0 ∨ E.is_finite P :=
begin
  rcases P with (_ | ⟨⟨x, y⟩, h⟩),
  { left, refl },
  { right, exact ⟨x, y, h, rfl⟩ }
end

def is_on_curve (x y : k) := y^2 = x^3 + E.a*x + E.b

lemma is_on_curve_def {x y : k} : E.is_on_curve x y ↔ y^2 = x^3 + E.a*x + E.b :=
iff.rfl

lemma coords_are_on_curve {P : points E} (hP : E.is_finite P) :
  E.is_on_curve (E.x_coord hP) (E.y_coord hP) :=
match P, hP with
| none, h0 := false.elim (E.not_is_finite_zero h0)
| some ⟨(x,y),h⟩, _ := h
end

lemma is_zero_or_finite' (P : points E) : P = 0 ∨ ∃ (x y : k)
  (h : E.is_on_curve x y), P = E.points_mk h :=
begin
  cases E.is_zero_or_finite P,
  { left, assumption },
  { right,
    rcases h with ⟨x, y, h1, rfl⟩,
    use [x, y, h1] }
end

lemma is_finite_spec {P : points E} (hP : E.is_finite P) :
  P = E.points_mk (E.coords_are_on_curve hP) :=
begin
  cases E.is_zero_or_finite' P, 
  { subst h,
    exfalso,
    exact E.not_is_finite_zero hP },
  { rcases h with ⟨x, y, h1, rfl⟩,
    refl }
end

lemma is_on_curve_neg {x y : k} (h : E.is_on_curve x y) : E.is_on_curve x (-y) :=
begin
  rw is_on_curve_def at *,
  convert h using 1,
  ring,
end

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

instance : has_neg (points E) := ⟨E.neg⟩ 

lemma neg_zero : -(0 : points E) = 0 := rfl

lemma neg_finite_def {x y : k} (h : E.is_on_curve x y) :
  -(E.points_mk h) = E.points_mk (E.is_on_curve_neg h) := rfl 

lemma neg_finite_def' {x y : k} (h : E.is_on_curve x y) :
  E.neg_finite ⟨(x, y), h⟩ = ⟨⟨x,-y⟩, E.is_on_curve_neg h⟩ := rfl 

lemma neg_some_some_neg (P : finite_points E) :
  -(id (some P) : E.points) = some (E.neg_finite P) := rfl
  

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


lemma double_zero : E.double 0 = 0 := rfl

lemma double_order_two {x : k} (h : E.is_on_curve x 0) :
  E.double (E.points_mk h) = 0 := begin
    change dite _ _ _ = _,
    simp,
  end
  -- not rfl in this case

lemma double_finite {x y : k} (hy : y ≠ 0) (h : E.is_on_curve x y) :
  E.is_finite (E.double (E.points_mk h)) := 
begin
  change E.is_finite (dite (y = 0) _ _),
  rw dif_neg hy,
  exact E.is_finite_some _,
end

lemma double_x_of_finite {x y : k} (hy : y ≠ 0) (h : E.is_on_curve x y) :
  E.x_coord (E.double_finite hy h) = ((3*x^2+E.a)^2-2*x*(2*y)^2)/(2*y)^2 :=
begin
  convert E.x_coord_some _,
  exact dif_neg hy,
end

lemma double_y_of_finite {x y : k} (hy : y ≠ 0) (h : E.is_on_curve x y) :
  E.y_coord (E.double_finite hy h) = 
(-((3*x^2+E.a)*((3*x^2+E.a)^2-2*x*(2*y)^2)+(y*(2*y)-(3*x^2+E.a)*x)*(2*y)^2))/(2*y)^3 :=
begin
  convert E.y_coord_some _,
  exact dif_neg hy,
end

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
    { ring },
    rw h1 at h,
    rw h2 at h,
    simpa using h,
    end⟩


instance : has_add (points E) := ⟨E.add⟩

theorem zero_add (P : points E) : (0 : points E) + P = P := begin
    cases P,
    { refl },
    { refl },
  end
theorem add_zero (P : points E) : P + 0 = P := begin
    cases P,
    { refl },
    { refl },
end
lemma add_self (P : points E) : P + P = E.double P := begin
  cases P,
  {refl},
  { rcases P with ⟨⟨x, y⟩, h⟩,
    change dite _ _ _ = _,
    rw dif_pos rfl,
    split_ifs,
    { refl },
    { refl },
  },
end

lemma add_left_neg_finite {x y : k}(h : E.is_on_curve x y) :
  (id (some ⟨⟨x,-y⟩, E.is_on_curve_neg h⟩):points E) + some⟨⟨x,y⟩,h⟩ = 0 := begin
    simp,
    change dite _ _ _ = _,
    rw dif_pos rfl,
    split_ifs,
    {have hy: y=0,
      { rw ← add_self_eq_zero,
        rw ← h_1,
        rw ← sub_eq_add_neg,
        rw ← sub_eq_zero at h_1,
        exact h_1 }, -- not linarith here
      rw hy at h,
      convert E.double_order_two h,
      rw h_1, exact hy },
    { refl },
  end

theorem add_left_neg (P : points E) : (-P) + P = 0 := begin
    cases P,
    { refl },
    { change -(id(some P): points E) + some P = 0,
      rw neg_some_some_neg,
      rcases P with ⟨⟨x, y⟩, h⟩,
      change E.is_on_curve x y at h,
      rw E.neg_finite_def',
      apply add_left_neg_finite},
  end


-- had to break up add_comm_finite to avoid timeout
theorem add_comm_equal {x1 x2 y1 y2 : k}(h1 : E.is_on_curve x1 y1)
  (h2 : E.is_on_curve x2 y2)(h3: x1=x2)(h4: y1=y2) :
  E.points_mk h1 + E.points_mk h2 = E.points_mk h2 + E.points_mk h1 := begin
    have heq: E.points_mk h1 = E.points_mk h2,
      { rw ext_iff,
        exact ⟨h3, h4⟩,
      },
    rw heq,
end

theorem add_comm_neg {x1 x2 y1 y2 : k}(h1 : E.is_on_curve x1 y1)
  (h2 : E.is_on_curve x2 y2)(h3: x1=x2)(h4: ¬ y1=y2) :
  E.points_mk h1 + E.points_mk h2 = E.points_mk h2 + E.points_mk h1 := begin
    change dite _ _ _ = dite _ _ _,
    split_ifs,
    { exfalso,
      apply h4,
      rw h_1  },
    { refl },
    { exfalso,
      apply h,
      rw h3 },
    
end

theorem add_comm_general {x1 x2 y1 y2 : k}(h1 : E.is_on_curve x1 y1)
  (h2 : E.is_on_curve x2 y2)(h3: ¬ x1=x2) :
  E.points_mk h1 + E.points_mk h2 = E.points_mk h2 + E.points_mk h1 := begin
    change dite _ _ _ = dite _ _ _,
    split_ifs,
    { exfalso,
      apply h3,
      rw h },
    { exfalso,
      apply h3,
      rw h },
    { rw option.some_inj,
      rw finite_points.ext_iff,
      split,
      { have h5: x1-x2 ≠ 0,
        { rw sub_ne_zero,
          exact h3 },
        have h6: x2-x1 ≠ 0,
        { rw sub_ne_zero,
          exact h },
        rw ← sub_eq_zero,
        field_simp,
        ring,
      },
      { have h5: x1-x2 ≠ 0,
        { rw sub_ne_zero,
          exact h3 },
        have h6: x2-x1 ≠ 0,
        { rw sub_ne_zero,
          exact h },
        rw ← sub_eq_zero,
        field_simp,
        ring,
      },

    },
    
end

theorem add_comm_finite {x1 x2 y1 y2 : k}(h1 : E.is_on_curve x1 y1)
  (h2 : E.is_on_curve x2 y2) :
  E.points_mk h1 + E.points_mk h2 = E.points_mk h2 + E.points_mk h1 := begin
    have hx: x1=x2 ∨ ¬ x1=x2,
      { tauto },
    cases hx,
    { have hy: y1=y2 ∨ ¬ y1=y2,
      { tauto },
      cases hy,
      { apply add_comm_equal,
        exact hx,
        exact hy },
      { apply add_comm_neg,
        exact hx,
        exact hy },
    },
    { apply add_comm_general,
      exact hx },
end

theorem add_comm (P Q : points E) : P + Q = Q + P := begin
  cases E.is_zero_or_finite' P,
  { rw h,
    rw add_zero,
    rw zero_add
  },
  { cases E.is_zero_or_finite' Q,
    { rw h_1,
      rw add_zero,
      rw zero_add
    },
    { cases h with x1 h,
      cases h with y1 hP,
      cases hP with hP1 hP2,
      cases h_1 with x2 h_1,
      cases h_1 with y2 hQ,
      cases hQ with hQ1 hQ2,
      rw [hP2, hQ2],
      apply E.add_comm_finite,
    },
  },
end

instance : add_comm_group (points E) :=
{ zero := 0,
  add := (+),
  neg := has_neg.neg,
  zero_add := E.zero_add,
  add_zero := E.add_zero,
  add_assoc := begin
    sorry,
  end,
  add_left_neg := E.add_left_neg,
  add_comm := E.add_comm,
}

theorem fg : add_group.fg (points E) := begin
  sorry,
end

def torsion_points (E : elliptic_curve_nf k) : 
(set (points E)) := 
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
noncomputable def rank : ℕ :=
  nat.find (sizes_non_empty E)
  

def primes : Type := sorry

def good_primes (E : elliptic_curve_nf k) : Type := sorry

def residue_characteristic (p : primes) : ℕ := sorry

def residue_field (p : primes) : Type := sorry

def p_points (p : good_primes E) : 
  finset (residue_field p × residue_field p):= sorry

noncomputable def a_p (p : good_primes E) : ℤ := 
  residue_characteristic p - finset.card (p_points E p)

def half_plane := {z : ℂ // complex.re z > 3/2}

instance : has_coe half_plane ℂ := ⟨subtype.val⟩

noncomputable def local_factor (s : ℂ) : good_primes E → ℂ
| p := 1 - (a_p E p) * (residue_characteristic p) ^ (-s) + (residue_characteristic p) ^ (1-2*s)

theorem hasse_bound (p : good_primes E) : 
  (a_p E p)^2 ≤ 4 * (residue_characteristic p) := sorry

theorem converges (s : half_plane) : 
  prodable (local_factor E s) := sorry

noncomputable def L_function_product  (s : half_plane) : ℂ :=
1/(tprod (local_factor E s))

theorem analytic_continuation: ∃ f : ℂ → ℂ, (differentiable ℂ f)∧(∀ z : half_plane, f z = L_function_product E z)
∧ (∀ g : ℂ → ℂ, (differentiable ℂ g)∧(∀ z : half_plane, g z = L_function_product E z) → g = f) := sorry

noncomputable def L_function : ℂ → ℂ := classical.some (analytic_continuation E)

noncomputable def L_derivative (E : elliptic_curve_nf k) : ℕ → ℂ → ℂ
|n := iterated_deriv n (L_function E)

theorem has_order_of_vanishing : ∃ n : ℕ, L_derivative E n 1 ≠ 0 := sorry

noncomputable def analytic_rank (E : elliptic_curve_nf k) : ℕ :=
  nat.find (has_order_of_vanishing E)

theorem BSD : analytic_rank E = rank E := sorry

end elliptic_curve_nf

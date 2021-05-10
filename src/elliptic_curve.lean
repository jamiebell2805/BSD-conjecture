import tactic

def disc (a b : ℚ) : ℚ :=
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
| (some P) := 
  

end elliptic_curve

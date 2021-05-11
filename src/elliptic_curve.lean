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
| (some P) := (some neg_finite P)
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
  let y₃ := -y3ddd/d^3 in
  some ⟨⟨x₃, y₃⟩, begin
    sorry,
  end⟩






end elliptic_curve

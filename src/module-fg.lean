import elliptic_curve_rationals
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
import ring_theory.noetherian


namespace elliptic_curve
variable (E : elliptic_curve)

instance module : module ℤ (points E) := begin
  apply add_comm_group.int_module,
end

theorem points_is_noetherian : is_noetherian ℤ (points E) := begin
  apply is_noetherian_of_fg_of_noetherian',

  sorry,
end

def torsion_submodule (E : elliptic_curve) : submodule ℤ (points E) :=
{ carrier := (torsion_points E),
  zero_mem' := begin
    sorry
  end,
  add_mem' := begin
    sorry
  end,
  smul_mem' := begin
    sorry,
  end
}

def torsion_free_module (E : elliptic_curve) := 
  (submodule.quotient (torsion_submodule E))

instance: module ℤ (torsion_free E) := begin
  apply_instance,
end

theorem is_noetherian_torsion_free : is_noetherian ℤ (torsion_submodule E).quotient := begin
  apply is_noetherian_of_quotient_of_noetherian ℤ (points E) (torsion_submodule E),
  apply points_is_noetherian,
end

theorem is_fg_torsion_free : submodule.fg (module ℤ (torsion_free E)) := begin

end elliptic_curve
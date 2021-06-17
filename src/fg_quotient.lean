import group_theory.subgroup
import group_theory.finiteness
import group_theory.quotient_group
import algebra.group.hom
import tactic
import init.function

variables (G H: Type*)[group G][group H](N : subgroup G)[subgroup.normal N](f : monoid_hom G H)(S : set G)
variables (A : Type*)[add_comm_group A](B : add_subgroup A)

@[to_additive add_fg_surj_image_fg]
theorem fg_surj_image_fg: (function.surjective f)
   → (group.fg G) → (group.fg H):= begin
  intros hsurj hfg,
  rw group.fg_iff at *,
  rcases hfg with ⟨S, ⟨hSclosure, hSfinite⟩⟩,
  use f '' S,
  split,
  { rw ← monoid_hom.map_closure,
    rw hSclosure,
    rw ← monoid_hom.range_eq_map,
    rw monoid_hom.range_top_iff_surjective,
    exact hsurj },
  { apply set.finite.image,
    exact hSfinite }
end

@[to_additive add_quotient_surj]
theorem quotient_surj: 
function.surjective (quotient_group.mk' N) := 
quotient.surjective_quotient_mk'

@[to_additive add_fg_quotient_of_fg]
theorem fg_quotient_of_fg: (group.fg G)
   → (group.fg (quotient_group.quotient N)) := begin
  apply fg_surj_image_fg G (quotient_group.quotient N) (quotient_group.mk' N),
  apply quotient_surj,
end


import data.set data.equiv
import algebra.group

variables {G : Type*} [group G]

class is_subgroup (H : set G): Prop :=
(mul_ : ∀ g h, g ∈ H → h ∈ H → g*h ∈ H)
(inv_ : ∀ g, g ∈ H → g⁻¹ ∈ H)
(one_ : (1:G) ∈ H)

namespace is_subgroup
variables { H : set G } [is_subgroup H] { x y : G }

lemma mul : x ∈ H → y ∈ H → x*y ∈ H :=
mul_ _ _

instance : has_mul H :=
⟨λ h k, ⟨h*k, mul h.property k.property⟩⟩  

lemma inv : x ∈ H → x⁻¹ ∈ H :=
inv_  _

instance : has_inv H :=
⟨λ h, ⟨h⁻¹, inv h.property⟩⟩

lemma one : (1:G) ∈ H := one_ _

instance : has_one H := 
⟨⟨(1:G), one⟩⟩

instance : group H :=
begin
refine { mul := (*), one := 1, inv := λ x, x⁻¹, ..},
{ intros a b c,
 cases a, cases b, cases c,
 simp[has_mul.mul],
 exact mul_assoc _ _ _ },
{ intro a, cases a, simp[has_mul.mul], exact group.one_mul _ },
{ intro a, cases a, simp[has_mul.mul], exact group.mul_one _ },
{ intro a, cases a,  simp[has_mul.mul, has_inv.inv], congr, exact group.mul_left_inv _ }
end
end is_subgroup


open equiv
universe u
variables {α : Type*} { β : Type* } 
lemma equiv.ext (f g : equiv α β) (H : ∀ x, f x = g x) : f = g :=
eq_of_to_fun_eq (funext H)


/- The group of permutations (self-equivalences) of a type `α` -/
instance perm_group {α : Type u} : group (perm α) :=
begin 
  refine { mul := λ f g, equiv.trans g f, one := equiv.refl α, inv:= equiv.symm, ..};
  intros; apply equiv.ext; try { apply trans_apply },
  apply inverse_apply_apply
end


variable {X : Type*}

def is_prop_preserving (prop : set X → Prop) (f : perm X) := ∀ L, prop L → prop (f '' L) ∧ prop (⇑f⁻¹ '' L)

lemma prop_group (prop : set X → Prop) : is_subgroup ({ f | is_prop_preserving prop f } : set (perm X)) := 
begin
split; simp,
{ intros g h gp hp L Lprop,
  split,
  { cases (hp L Lprop) with hpL _,
    cases (gp _ hpL) with gpL _,
    rw[←set.image_comp] at gpL,
    finish },
  { cases (gp L Lprop) with _ gpLinv,
    cases (hp _ gpLinv) with _ hpLinv,
    rw[←set.image_comp] at hpLinv,
    finish } },
{ intros g gp L Lprop, cases gp L Lprop with gp gpinv, finish },
{ intro L, 
  rw[show (1:perm X)⁻¹ = 1, from rfl], simp,
  have : (1:perm X) '' L = L, simpa using set.image_id L, 
  finish },
end

lemma stabilizer_group (x : X) : is_subgroup ({ f | f x = x } : set (perm X)) := 
begin
split; simp,
{ intros g h gx hx,
  simpa [hx, gx, show (g * h) x = g (h x), from rfl]},
{ intros g gx, 
  simpa using (congr_arg g.symm gx).symm },
{ refl }
end

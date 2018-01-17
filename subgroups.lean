import data.set
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
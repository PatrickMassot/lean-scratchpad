import analysis.topology.topological_space
import data.set
import homeos
import tactic.find
import invariant_norms
import tactic

noncomputable theory
local attribute [instance] classical.prop_decidable

set_option pp.coercions false

open set function equiv

def fix {X} (f : X → X) := { x : X | f x = x }

lemma fix_stable {X} (f : X → X) : f '' fix f = fix f :=
begin
  apply subset.antisymm,
  { intros x H,
    rcases H with ⟨y, y_in_fix, f_y_x⟩,
    simp [fix] at y_in_fix,
    rw y_in_fix at f_y_x,
    finish },
  { intros x H,
    existsi x,
    finish }
end

variables {X : Type} [topological_space X] (f : X → X)

def supp := closure (-fix f)

lemma compl_supp_eq_interior_fix : -supp f = interior (fix f) :=
calc -supp f = -closure (-fix f) : rfl
         ... = -(-interior (fix f)) : by rw closure_compl
         ... =  interior (fix f) : by rw compl_compl

lemma compl_supp_subset_fix : -supp f ⊆ fix f :=
calc -supp f = interior (fix f) : by rw compl_supp_eq_interior_fix
         ... ⊆ fix f : interior_subset

lemma mem_supp_or_fix (x) : x ∈ supp f ∨ f x = x :=
or_iff_not_imp_left.2 (λ h, compl_supp_subset_fix _ h)
-- Recall: or_iff_not_imp_left : a ∨ b ↔ (¬ a → b)

lemma stable_support (f : homeo X X) : f '' supp f = supp f :=
calc 
  f '' supp f = f '' (closure (-fix f)) : rfl
          ... =  closure (f '' (-fix f)) : by rw f.image_closure
          ... =  closure (-(f '' (fix f))) : by rw f.image_compl
          ... =  closure (-(fix f)) : by rw fix_stable

lemma fundamental' {f g : homeo X X} (H : supp f ∩ supp g = ∅) : f ∘ g = g ∘ f :=
begin
  funext x,
  suffices special_case : 
    ∀ f g : homeo X X, supp f ∩ supp g = ∅ → ∀ x ∈ supp f, f (g x) = g (f x),
  { cases mem_supp_or_fix f x with hf hf,
    { exact special_case f g H x hf },
    { cases mem_supp_or_fix g x with hg hg,
      { rw inter_comm at H,
        exact (special_case g f H x hg).symm },
      { simp [hf, hg] } } },
  intros f g H x h,
  have hg : g x = x :=
    compl_supp_subset_fix _ ((subset_compl_iff_disjoint.2 H) h),
  simp [hg],
  refine (compl_supp_subset_fix _ $ (subset_compl_iff_disjoint.2 H) _).symm,
  rw ← stable_support,
  finish
end

lemma fundamental {f g : homeo X X} (H : supp f ∩ supp g = ∅) : f * g = g * f :=
homeo.ext $ λ x, by simpa using congr_fun (fundamental' H) x

lemma supp_conj (f g : homeo X X) : supp (conj g f : homeo X X) = g '' supp f :=
begin
  unfold supp,
  rw homeo.image_closure,
  congr_n 1,
  apply set.ext,
  intro x,
  rw mem_image_iff_of_inverse g.left_inverse g.right_inverse,
  apply not_congr,
  dsimp [conj],
  exact calc
     (g * f * g⁻¹) x = x
        ↔ g⁻¹ (g (f (g⁻¹ x))) = g⁻¹ x : by simp [(g⁻¹).bijective.1.eq_iff]
    ... ↔ (f (g⁻¹ x)) = g⁻¹ x : by rw [← aut_mul_val, mul_left_inv]; simp
end

local notation `[[`a, b`]]` := comm a b


lemma trading_of_displaced (g a b : homeo X X) (supp_hyp : supp a ∩ g '' supp b = ∅) :
∃ c d e f : homeo X X, [[a, b]] = (conj c g⁻¹)*(conj d g)*(conj e g⁻¹)*(conj f g) :=
begin
  apply commutator_trading,
  rw ← supp_conj at supp_hyp,
  rw commuting,
  exact fundamental supp_hyp,
end

/-
lemma fix_conj (f g : perm X) : fix (conj g f : perm X) = g '' (fix f) :=
begin
  apply set.ext,
  intro x,
  rw mem_image_iff_of_inverse g.left_inverse g.right_inverse,
  dsimp[conj],
  exact calc
     (g * f * g⁻¹) x = x
        ↔ g⁻¹ (g (f (g⁻¹ x))) = g⁻¹ x : by { simp [(g⁻¹).bijective.1.eq_iff], }
    ... ↔ (f (g⁻¹ x)) = g⁻¹ x : by  rw [← perm_mul_val, mul_left_inv] ; simp
end


instance : has_coe (homeo X X) (perm X) := ⟨λ f, f.to_equiv⟩

set_option pp.coercions true
--set_option pp.all true 

lemma mul_perm_homeo (f g : homeo X X) : (f : perm X)*(g : perm X) = (f*g : homeo X X) :=
begin
  apply equiv.ext,
  intro x,
  simp,
  sorry -- rw equiv.trans_apply,
end

lemma inv_perm_homeo (f : homeo X X) : (f : perm X)⁻¹ = (f⁻¹ : homeo X X) := rfl

lemma conj_perm_homeo (f g : homeo X X) : conj (g : perm X) (f : perm X) = (conj g f : homeo X X) :=
by simp [conj, mul_perm_homeo, inv_perm_homeo]



lemma supp_conj (f g : homeo X X) : supp (conj g f : homeo X X) = g '' supp f :=
begin
  unfold supp,
  rw homeo.image_closure,
  congr_n 1,
  rw g.image_compl,
  congr,
  have := fix_conj (f : perm X)  (g : perm X),
  rw conj_perm_homeo at this,
  exact this
end
-/
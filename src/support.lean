import analysis.topology.topological_space
import data.set
import homeos
import tactic.find
import norms2
import tactic

noncomputable theory
local attribute [instance] classical.prop_decidable

meta def by_double_inclusion : tactic unit := do
`[apply set.subset.antisymm_iff.2, split]

section topo
open set function

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]
/-
class foo :=
(data : Type)

class bar extends foo

lemma foo_lemma (f : foo) : true := trivial

lemma bar_lemma (f : bar) : true := by apply foo_lemma 

lemma bar_lemma' (f : bar) : true := foo_lemma f.to_foo
-/

lemma equiv.image_eq_preimage {α β} (e : α ≃ β) (s : set α) : e '' s = e.symm ⁻¹' s := 
ext $ assume x, mem_image_iff_of_inverse e.left_inv e.right_inv

lemma equiv.subset_image {α β} (e : α ≃ β) (s : set α) (t : set β) : t ⊆ e '' s ↔ e.symm '' t ⊆ s :=
by rw [image_subset_iff, e.image_eq_preimage]

lemma homeo.subset_image (e : homeo α β) (s : set α) (t : set β) : t ⊆ e '' s ↔ e.symm '' t ⊆ s :=
equiv.subset_image _ _ _

lemma equiv.symm_image_image (f : equiv α β) (s : set α) : f.symm '' (f '' s) = s :=
by rw [←image_comp] ; simpa using image_id s

lemma symm_image_image (f : homeo α β) (s : set α) : f.symm '' (f '' s) = s :=
equiv.symm_image_image _ _

lemma homeo.image_closure (f : homeo α β) (s : set α) : f '' closure s = closure (f '' s) :=
subset.antisymm
  (image_closure_subset_closure_image f.fun_con)
  ((homeo.subset_image _ _ _).2 $
    calc f.symm '' closure (f '' s) ⊆ closure (f.symm '' (f '' s)) :
        image_closure_subset_closure_image f.inv_con
      ... = closure s : by rw symm_image_image f s)

set_option pp.coercions false


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

def supp := closure {x : X | f x ≠ x}

lemma supp_eq_closure_compl_fix : supp f = closure (-fix f) := rfl

lemma compl_supp_eq_interior_fix : -supp f = interior (fix f) :=
by rw [supp_eq_closure_compl_fix, closure_compl, compl_compl]

lemma compl_supp_subset_fix : -supp f ⊆ fix f :=
by rw compl_supp_eq_interior_fix; apply interior_subset

lemma mem_supp_or_fix (x) : x ∈ supp f ∨ f x = x :=
or_iff_not_imp_left.2 (λ h, compl_supp_subset_fix _ h)

lemma equiv.image_compl (f : equiv α β) (s : set α) :
  f '' -s = -(f '' s) :=
image_compl_eq f.bijective

lemma homeo.image_compl (f : homeo α β) (s : set α) : f '' -s = -(f '' s)  := 
equiv.image_compl _ _

lemma stable_support (f : homeo X X) : f '' supp f = supp f :=
by rw [supp_eq_closure_compl_fix, homeo.image_closure, homeo.image_compl, fix_stable]

lemma notin_of_in_of_inter_empty {α : Type*} {s t : set α} {x : α} (H : s ∩ t = ∅) (h : x ∈ s) : x ∉ t :=
(subset_compl_iff_disjoint.2 H) h

lemma fundamental {f g : homeo X X} (H : supp f ∩ supp g = ∅) : f ∘ g = g ∘ f :=
begin
  funext x,
  suffices : ∀ f g : homeo X X, supp f ∩ supp g = ∅ → ∀ x ∈ supp f, f (g x) = g (f x),
  { cases mem_supp_or_fix f x with hf hf,
    { exact this f g H x hf },
    cases mem_supp_or_fix g x with hg hg,
    { rw inter_comm at H,
      exact (this g f H x hg).symm },
    { simp [hf, hg] } },
  intros f g H x h,
  have hg : g x = x :=
    compl_supp_subset_fix _ ((subset_compl_iff_disjoint.2 H) h),
  simp [hg],
  refine (compl_supp_subset_fix _ $ (subset_compl_iff_disjoint.2 H) _).symm,
  rw ← stable_support,
  exact mem_image_of_mem f h
end

lemma fundamental' {f g : homeo X X} (H : supp f ∩ supp g = ∅) : f * g = g * f :=
homeo.ext $ λ x, by simpa using congr_fun (fundamental H) x

lemma supp_conj (f g : homeo X X) : supp (conj g f : homeo X X) = g '' supp f :=
begin
  unfold supp,
  rw homeo.image_closure,
  congr_n 1,
  apply set.ext (λ x, _),
  rw mem_image_iff_of_inverse g.left_inverse g.right_inverse,
  apply not_congr,
  dsimp [conj],
  exact calc
     (g * f * g⁻¹) x = x
        ↔ g⁻¹ (g (f (g⁻¹ x))) = g⁻¹ x : by simp [(g⁻¹).bijective.1.eq_iff]
    ... ↔ (f (g⁻¹ x)) = g⁻¹ x : by rw [← aut_mul_val, mul_left_inv]; simp
end

local notation `[[`a, b`]]` := comm a b

lemma TT (g a b : homeo X X) (supp_hyp : supp a ∩ g '' supp b = ∅) :
∃ c d e f : homeo X X, [[a, b]] = (conj c g)*(conj d g⁻¹)*(conj e g)*(conj f g⁻¹) :=
begin
  apply commutator_trading,
  rw commuting,
  rw ← supp_conj at supp_hyp,
  have := congr_arg (conj g⁻¹) (fundamental' supp_hyp),
  simpa [conj_mul, conj_action.symm]
end

end topo
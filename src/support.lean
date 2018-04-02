import analysis.topology.topological_space
import data.set
import homeos
import tactic.find


noncomputable theory
local attribute [instance] classical.prop_decidable

meta def by_double_inclusion : tactic unit := do
`[apply set.subset.antisymm_iff.2, split]

section topo
open set 

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


variables {X : Type} [topological_space X] (f : X → X)

def fix := { x : X | f x = x }



lemma fix_stable : f '' fix f = fix f :=
begin
  by_double_inclusion,
  { intros x H,
    rcases H with ⟨y, y_in_fix, f_y_x⟩,
    simp [fix] at y_in_fix,
    rw y_in_fix at f_y_x,
    finish },
  { intros x H,
    existsi x,
    finish }
end

def supp := closure {x : X | f x ≠ x}

lemma compl_supp_subset_fix : -supp f ⊆ fix f :=
compl_subset_of_compl_subset 
  (calc  -fix f = {x : X | f x ≠ x} : rfl
            ... ⊆ supp f : subset_closure)

lemma fuck (f : equiv α β) (b) : f (f.inv_fun b) = b := f.right_inv b

lemma equiv.image_compl  (f : equiv α β) (s : set α) :
  f '' -s = -(f '' s) :=
begin
  apply subset.antisymm,
  { intros b b_in_image_compl,
    rcases b_in_image_compl with ⟨a, a_compl_s, f_a_b⟩,
    rw (equiv.apply_eq_iff_eq_inverse_apply f a b).1 f_a_b at a_compl_s,
    exact (mt (@mem_image_iff_of_inverse α β f.to_fun f.inv_fun b s f.left_inv f.right_inv).1) a_compl_s },
  { intros, 
    rw subset_def,
    intros b b_in_compl_image,
    apply (@mem_image_iff_of_inverse _ _ _ _ _ _ f.left_inv f.right_inv).2,
    have b_not_in_image := not_mem_of_mem_compl b_in_compl_image,
    rw set.mem_compl_eq,
    by_contra,
    have := mem_image_of_mem f a,
    rw fuck at this,
    finish }
end

lemma homeo.image_compl  (f : homeo α β) (s : set α) : f '' -s = -(f '' s)  := 
equiv.image_compl _ _

variable (F : homeo X X)
#check (F.to_equiv).to_fun
#check ⇑F
example (h : homeo α β) : (h : α → β) = h.to_equiv := rfl


lemma stable_support (f : homeo X X) : f '' supp f = supp f :=
begin
  have point_set : f '' {x : X | f x ≠ x } = {x : X | f x ≠ x },
    by rw [show {x : X | f x ≠ x} = -fix f, from rfl, homeo.image_compl f (fix f), fix_stable],
  unfold supp,
  rw [homeo.image_closure, point_set]
end

lemma notin_of_in_of_inter_empty {α : Type*} {s t : set α} {x : α} (H : s ∩ t = ∅) (h : x ∈ s) : x ∉ t :=
begin
  by_contradiction h',
  have : x ∈ s ∩ t := ⟨h, h'⟩,
  rw H at this,
  assumption
end

lemma fundamental (f g : homeo X X) (H : supp f ∩ supp g = ∅) : f ∘ g = g ∘ f :=
begin
  funext,
  by_cases h : x ∈ supp f ∪ supp g,
  { cases h,
    { have x_in_fix_g : g x = x := 
        calc x ∈ -supp g : notin_of_in_of_inter_empty H h
          ... ⊆ fix g : compl_supp_subset_fix g,
      
      have f_x_supp_f : f x ∈ supp f := stable_support f ▸ mem_image_of_mem f h,
      
      have f_x_in_fix_g : g (f x) = f x := 
        calc f x ∈ -supp g : notin_of_in_of_inter_empty H f_x_supp_f
          ... ⊆ fix g : compl_supp_subset_fix g,
      
      
      exact calc (f ∘ g) x = f (g x) : rfl
        ... = f x : by rw x_in_fix_g 
        ... = g (f x) : by  rw f_x_in_fix_g },
    { rw inter_comm at H,
      have x_in_fix_f : f x = x := 
        calc x ∈ -supp f : notin_of_in_of_inter_empty H h
          ... ⊆ fix f : compl_supp_subset_fix f,
      
      have g_x_supp_g : g x ∈ supp g := stable_support g ▸ mem_image_of_mem g h,
      
      have g_x_in_fix_f : f (g x) = g x := 
        calc g x ∈ -supp f : notin_of_in_of_inter_empty H g_x_supp_g
          ... ⊆ fix f : compl_supp_subset_fix f,
      
      
      exact calc (f ∘ g) x = f (g x) : rfl
        ... = g x : by rw g_x_in_fix_f 
        ... = g (f x) : by  rw x_in_fix_f } },
  { replace h : x ∈ -(supp f ∪ supp g) := h,
    rw compl_union (supp f) (supp g) at h,
    
    have f_x : f x = x := compl_supp_subset_fix f h.1,
    have g_x : g x = x := compl_supp_subset_fix g h.2,
    
    
    exact calc (f ∘ g) x = f (g x) : rfl
        ... = f x : by rw g_x 
        ... = x : by  rw f_x
        ... = g x : by rw g_x
        ... = g (f x) : by rw f_x }
end

end topo
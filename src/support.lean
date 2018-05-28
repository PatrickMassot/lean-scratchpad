import analysis.topology.topological_space
import data.set
import data.fin
import tactic.find
import tactic.ring
import algebra.group

import homeos
import invariant_norms
import bigop

noncomputable theory
local attribute [instance] classical.prop_decidable

set_option pp.coercions false

open set function equiv list

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

lemma fix_of_not_in_supp {x : X} {f : homeo X X} (h : x ∉ supp f) : f x = x :=
compl_supp_subset_fix f h

lemma mem_supp_or_fix (x) : x ∈ supp f ∨ f x = x :=
or_iff_not_imp_left.2 (λ h, compl_supp_subset_fix _ h)
-- Recall: or_iff_not_imp_left : a ∨ b ↔ (¬ a → b)

lemma stable_support (f : homeo X X) : f '' supp f = supp f :=
calc 
  f '' supp f = f '' (closure (-fix f)) : rfl
          ... =  closure (f '' (-fix f)) : by rw f.image_closure
          ... =  closure (-(f '' (fix f))) : by rw f.image_compl
          ... =  closure (-(fix f)) : by rw fix_stable

lemma fundamental {f g : homeo X X} (H : supp f ∩ supp g = ∅) : f * g = g * f :=
begin
  ext x,
  by_cases H' : x ∈ supp f ∨ x ∈ supp g,
  { -- Here we assume H' : x ∈ supp f ∨ x ∈ supp g
    wlog h : x ∈ supp f using f g,
    have x_not_supp_g : x ∉ supp g := (subset_compl_iff_disjoint.2 H) h,
    have f_x_supp_f : f x ∈ supp f, 
    { have : f x ∈ f '' supp f := mem_image_of_mem f h, 
      finish [stable_support f] },
    have : f x ∉ supp g := (subset_compl_iff_disjoint.2 H) f_x_supp_f,
    finish [fix_of_not_in_supp] },
  { -- Now we assume H' : ¬(x ∈ supp f ∨ x ∈ supp g)
    rw not_or_distrib at H',
    finish [fix_of_not_in_supp] }
end
/- Calc version of above proof
lemma fundamental'' {f g : homeo X X} (H : supp f ∩ supp g = ∅) : f * g = g * f :=
begin
  ext x,
  by_cases H' : x ∈ supp f ∨ x ∈ supp g,
  { -- Here we assume H' : x ∈ supp f ∨ x ∈ supp g
    wlog h : x ∈ supp f using f g,
    exact calc 
    (f * g) x = f (g x) : by simp
          ... = f x     : by { have x_not_supp_g : x ∉ supp g := (subset_compl_iff_disjoint.2 H) h,
                               finish [fix_of_not_in_supp] }
          ... = g (f x) : by { have f_x_supp_f : f x ∈ supp f,
                               { have : f x ∈ f '' supp f := mem_image_of_mem f h, 
                                 finish [stable_support f] },
                               have : f x ∉ supp g := (subset_compl_iff_disjoint.2 H) f_x_supp_f,
                               finish [fix_of_not_in_supp] }
          ... = (g * f) x : by simp },
  { -- Now we assume H' : ¬(x ∈ supp f ∨ x ∈ supp g)
    rw not_or_distrib at H',
    finish [fix_of_not_in_supp] }
end
-/
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

local notation `〚`a, b`〛` := comm a b  -- type with \llb / \rrb

lemma numbers' {N} (H : N > 0) : ∀ i, i ∈ range' 0 (N - 1 + 1 - 0) → N - (N - 1 - i) = i + 1 :=
begin
  intros i hyp,
  simp [nat.add_sub_cancel' H] at hyp,
  rw [nat.sub_sub, add_comm, nat.sub_sub_self hyp.2]
end

/- replace hyp := hyp.right,
  have := nat.succ_le_of_lt  hyp,
  
  rw [← int.coe_nat_inj', int.coe_nat_sub, int.coe_nat_sub, int.coe_nat_sub],
  { ring },
  { assumption },
  { sorry },
  { sorry }-/


lemma trading_of_displaced (g a b : homeo X X) 
  (supp_hyp : supp a ∩ g '' supp b = ∅) :
  ∃ c d e f : homeo X X, 〚a, b〛 = (conj c g⁻¹)*(conj d g)*(conj e g⁻¹)*(conj f g) :=
begin
  apply commutator_trading,
  rw ←supp_conj at supp_hyp,
  rw [commuting, fundamental supp_hyp]
end

--set_option trace.class_instances true
--set_option pp.all true

lemma commutators_crunching (U : set X) (φ f : homeo X X)
(wandering_hyp : ∀ i j : ℕ, i ≠ j → ⇑(φ^i) '' U ∩ ⇑(φ^j) '' U = ∅)
(N : ℕ) (aa : ℕ → homeo X X) (b : ℕ → homeo X X) 
(supp_hyp : ∀ k : ℕ, supp (aa k) ⊆ U ∧ supp (b k) ⊆ U)
(comm_hyp : f = Π_(i = 1..N) 〚aa i, b i〛) :
∃ A B C D : homeo X X, f = 〚A, B〛 * 〚C, D〛 := 
begin
  by_cases H : N = 0,
  { rw big.empty_range at comm_hyp,
    repeat { existsi (1 : homeo X X) },
    simp [comm_hyp, comm],
    simp [H, zero_lt_one] },
  { replace H : N ≥ 1 := nat.succ_le_of_lt (nat.pos_of_ne_zero H),
    let G := homeo X X,
    let g := λ i, (Π_(j=1..i) 〚aa i, b i〛: G),
    let F := (Π_(i=0..(N-1)) conj (φ^i) $ g (N-i) : G),

    have commute : ∀ (i j k l : ℕ), i ≠ j → 
      (conj (φ^i) (aa k))*(conj (φ^j) (b l)) = (conj (φ^j) (b l))*(conj (φ^i) (aa k)),
    begin
      intros i j k l i_neq_j,
      apply fundamental,
      repeat { rw supp_conj },
      specialize wandering_hyp i j i_neq_j,
      have supp_a := set.image_subset (φ^i : G) (supp_hyp k).left,
      have supp_b := set.image_subset (φ^j : G)  (supp_hyp l).right,
      
      have := set.inter_subset_inter supp_a supp_b,
      rw wandering_hyp at this,
      exact set.eq_empty_of_subset_empty this
    end,

    have numbers := 
    calc 1 + (1 + (N - 1)) - 1 =  (1 + (N-1)) + 1 - 1 : by simp 
    ... = 1 + (N-1) : by rw nat.add_sub_cancel
    ... = N : by rw nat.add_sub_cancel' H,
    
    have cφf:= calc 
    conj φ F = conj φ (Π_(i=0..(N-1)) conj (φ^i) $ g (N-i)) : rfl
    ... = Π_(i=0..(N-1)) conj φ (conj (φ^i) $ g (N-i)) : by rw (big.mph _ _ _ _ _ (is_group_hom.mul (conj φ)) (is_group_hom.one _))
    ... = Π_(i=0..(N-1)) conj (φ^(i+1)) $ g (N-i) : by simp[pow_succ]
    ... = Π_(i=1..N) conj (φ^i) $ g (N-(i-1)) : by { rw big.shift _ _ _ _ 0 (N-1) 1, simp, rw numbers, apply big.ext, simp, intros i hyp, rw nat.add_sub_cancel' (mem_range'.1 hyp).left},

    have := (@inv_is_group_anti_hom G _ _).mul,
    let gg := λ i, (conj (φ^i) $ (g (N-i))⁻¹ : G),
    have Finv := calc
    F⁻¹ = (Π_(i=0..(N-1)) conj (φ^i) $ g (N-i) : G)⁻¹ : rfl
    ... = (λ (g : G), g⁻¹) (Π_(i=0..(N-1)) conj (φ^i) $ g (N-i) : G) : rfl
    ... = (Π_(i=0..(N-1)) (conj (φ^(N-1-i)) $ g (N - (N - 1 - i)))⁻¹ : G) : by { rw big.range_anti_mph _ (1:G) _ _ _ _ this ; simp }
    ... = (Π_(i=0..(N-1)) (conj (φ^(N-1-i)) $ g (i+1))⁻¹ : G) : by { apply big.ext, { simp }, intros i hyp, rw numbers' H i hyp }
    ... = (Π_(i=0..(N-1)) conj (φ^(N-1-i)) $ (g (i+1))⁻¹ : G) : by { apply big.ext, simp, intros, rw ←is_group_hom.inv (conj _), apply_instance }
    ... = (Π_(i=0..(N-1)) conj (φ^i) $ (g (N-i))⁻¹ : G) : by { rw big.reverse_range_of_commute, apply big.ext, simp, simp, sorry, sorry }
    ... = (Π_(i=0..(N-1)) gg i)*(gg N)  : by { dsimp [g], simp[big.nil], sorry }
    ... = (Π_(i=0..N) gg i) : by{  have := (big.concat_true (*) (1:G) (range' 0 (N - 1 + 1 - 0)) gg N), cc, },

    
    have : conj (φ^N) (g 0)⁻¹ = 1,
    by { dsimp [g], simp[big.nil] } ,
    

    sorry }
end

#check big.concat_true
#check int.cast_inj
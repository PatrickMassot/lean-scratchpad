import algebra.group
import data.set.basic
import analysis.real
import tactic.norm_num
import .choice

set_option pp.beta true

example (P Q R : Prop) : ((P ∨ Q → R) ∧ P) → R :=
begin
  rintro ⟨hyp1, hyp2⟩,
  apply hyp1,
  left,
  assumption,
end

example (P Q R : Prop) : ((P ∨ Q → R) ∧ P) → R :=
by finish

example (X : Type) (A B C : set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext x,
  split,
  { rintro ⟨x_1, x_B | x_C⟩,
    { left,
      apply and.intro,
      { assumption },
      { assumption } },
    { right,
      apply and.intro,
      { assumption },
      { assumption } } },
  { rintro (⟨x_A, x_B⟩|⟨x_A, x_C⟩),
    { apply and.intro,
      { assumption },
      { left,
        assumption } },
    { apply and.intro,
      { assumption },
      { right,
        assumption } } }
end

example (X : Type) (A B C : set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
by ext x; split; finish

example (X : Type) (A B C : set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
set.inter_distrib_left _ _ _

example (X Y : Type) (f : X → Y) :
  (∀ y : Y, ∃ x : X, f(x) = y) ↔ (∃ g : Y → X, f ∘ g = id) :=
begin
  split,
  { intro hyp,
    choice hyp with g H,
    existsi g,
    exact funext H, },
  { rintros ⟨g, f_rond_g⟩ y,
    existsi g y,
    exact congr_fun f_rond_g y }
end

example (G H : Type) [group G] [group H] (f : G → H)
  (Hyp : ∀ a b : G, f (a*b) = f a * f b) : f 1 = 1 :=
begin
  have clef := calc
   f 1 = f (1*1) : by simp
   ... = f 1 * f 1 : Hyp 1 1,
  exact mul_self_iff_eq_one.1 (eq.symm clef)
end

example (u : ℕ → ℝ) (H : ∀ n, u (n+1) = 2*u n) (H' : u 0 > 0) :
  ∀ n, u n > 0 :=
begin
  intro n,
  induction n with n IH,
  { exact H' },
  { rw H,
    apply mul_pos,
    norm_num,
    exact IH }
end
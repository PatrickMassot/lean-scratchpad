import algebra.group
import data.set.basic
import analysis.real
import tactic.norm_num
import .choice
set_option pp.beta true

example (P Q R : Prop) : ((P ∨ Q → R) ∧ P) → R :=
begin
  intro hyp,
  cases hyp with hyp1 hyp2,
  apply hyp1,
  apply or.inl,
  assumption,
end

example (P Q R : Prop) : ((P ∨ Q → R) ∧ P) → R :=
begin
  finish
end

example (X : Type) (A B C : set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext x,
  split,
  { intro hyp,
    cases hyp with x_1 x_B_ou_C,
    cases x_B_ou_C,
    { apply or.inl,
      apply and.intro,
      { assumption },
      { assumption } },
    { apply or.inr,
      apply and.intro,
      { assumption },
      { assumption } } },
  { intro hyp, 
    cases hyp, 
    { cases hyp with x_A x_B,
      apply and.intro,
      { assumption },
      { apply or.inl,
        assumption } },
    { cases hyp with x_A x_C,
        apply and.intro,
        { assumption },
        { apply or.inr,
          assumption } } }
end

example (X Y : Type) (f : X → Y) : 
  (∀ y : Y, ∃ x : X, f(x) = y) ↔ (∃ g : Y → X, f ∘ g = id) :=
begin
  split,
  { intro hyp,
    choice hyp with g H,
    existsi g,
    funext y,
    exact H y, },
  { intros hyp y,
    cases hyp with g f_rond_g,
    existsi g y,
    change (f ∘ g) y = y,
    apply congr_fun,
    exact f_rond_g, }
end

example (G H : Type) [group G] [group H] (f : G → H) 
  (Hyp : ∀ a b : G, f (a*b) = f a * f b) : f 1 = 1 :=
begin
  have clef := calc
   f 1 = f (1*1) : by simp
   ... = f 1 * f 1 : Hyp 1 1,
  rw mul_self_iff_eq_one.1 (eq.symm clef),
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
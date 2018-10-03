import tactic.linarith tactic.tidy

open tactic
@[tidy] meta def tactic.interactive.apply_eq : tactic unit :=
do gs ← get_goals,
   l ← local_context,
   l.mmap $ λ h, try $ do {
     `(%%x = %%y) ← infer_type h,
     (vs,t) ← infer_type x >>= mk_local_pis,
     p' ← mk_app `eq [x.mk_app vs, y.mk_app vs],
     p' ← pis vs p',
     assert (to_string h.local_pp_name ++ "_ev" : string) p',
     vs ← intros,
     vs.reverse.mmap (λ v,
       do revert v,
          applyc ``congr_fun),
     exact h },
   gs' <- get_goals,
   guard (gs ≠ gs')

@[tidy] meta def fini := `[finish]
@[tidy] meta def linarit := `[linarith]
@[tidy] meta def tautol := `[tauto]

example (P Q R : Prop) : ((P ∨ Q → R) ∧ P) → R :=
by tidy

example (X : Type) (A B C : set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
by tidy

example (X Y : Type) (f : X → Y) :
  (∀ y : Y, ∃ x : X, f(x) = y) ↔ (∃ g : Y → X, f ∘ g = id) :=
begin
  split,
  { intro hyp,
    choose g H using hyp,
    tidy },
  { rintros ⟨g, f_rond_g⟩ y,
    existsi g y,
    tidy }
end
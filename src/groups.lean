import data.set.basic
import data.list
import algebra.group_power

open set
open function

local infix ` ^ ` := gpow

variables {α : Type} [group α]

def is_generating (S: set α) : Prop := 
∀ g : α, ∃ l : list α, g = list.prod l ∧ ∀ x ∈ l, x ∈ S ∨ x⁻¹ ∈ S

/-lemma group_generates_itself : is_generating (@univ α) | g := ⟨[g], by simp⟩-/

def power (p : α ×  ℤ) : α := p.1^p.2

def is_generating2 (S: set α) : Prop := 
∀ g : α, ∃ l : list (α × ℤ), g = (l.map power).prod ∧ ∀ p ∈ l, (p : α × ℤ).1 ∈ S


/-
lemma gen_is_gen2 (S : set α) : is_generating S ↔ is_generating2 S :=
forall_congr $ λ g, begin
  split; intro h; rcases h with ⟨l, rfl, hl⟩;
    induction l with a l IH; try { exact ⟨[], by simp⟩ };
    rcases IH (λ x m, hl x (list.mem_cons_of_mem _ m)) with ⟨l', e, h⟩,
  { cases hl a (list.mem_cons_self _ _) with m m;
    [existsi (a,1)::l', existsi (a⁻¹,-1)::l'];
    simp [power, e, m, h] {contextual:=tt} },
  { cases a with a n,
    rcases int.eq_coe_or_neg n with ⟨n, rfl | rfl⟩,
    { existsi list.repeat a n ++ l',
      simpa [power, e, or_imp_distrib, forall_and_distrib, iff_true_intro h]
      using λ x (m : x ∈ list.repeat a n), show x ∈ S ∨ x⁻¹ ∈ S, from
        (list.eq_of_mem_repeat m).symm ▸ or.inl (hl _ (list.mem_cons_self _ _)) },
    { existsi list.repeat a⁻¹ n ++ l',
      simp [power, e, or_imp_distrib, forall_and_distrib, iff_true_intro h],
      exact λ x m, (list.eq_of_mem_repeat m).symm ▸
        by simp [hl _ (list.mem_cons_self _ _)] } }
end
-/

attribute [simp] inv_pow

lemma gen_is_gen2 (S : set α) : is_generating S ↔ is_generating2 S :=
forall_congr $ λ g, begin
  split,
  { intro h,
    rcases h with ⟨l, rfl, hl⟩,
    induction l with a l IH, { exact ⟨[], by simp⟩ },
    rcases IH (λ x m, hl x (list.mem_cons_of_mem _ m)) with ⟨l', e, h⟩,
    cases hl a (list.mem_cons_self _ _) with m m,
    { existsi (a,1)::l',
      simp [power, e, m, h] {contextual:=tt} },
    { existsi (a⁻¹,-1)::l',
      simp [power, e, m, h] {contextual:=tt} } },
  { intro h,
    rcases h with ⟨l, rfl, hl⟩,
    induction l with a l IH, { exact ⟨[], by simp⟩ },
    rcases IH (λ x m, hl x (list.mem_cons_of_mem _ m)) with ⟨l', e, h⟩,
    cases a with a n,
    rcases int.eq_coe_or_neg n with ⟨n, rfl | rfl⟩,
    { existsi list.repeat a n ++ l',
      simpa [power, e, or_imp_distrib, forall_and_distrib, iff_true_intro h]
      using λ x (m : x ∈ list.repeat a n), show x ∈ S ∨ x⁻¹ ∈ S, from
        (list.eq_of_mem_repeat m).symm ▸ or.inl (hl _ (list.mem_cons_self _ _)) },
    { existsi list.repeat a⁻¹ n ++ l',
      simpa [power, e, or_imp_distrib, forall_and_distrib, iff_true_intro h]
      using λ x (m : x ∈ list.repeat a⁻¹ n), show x ∈ S ∨ x⁻¹ ∈ S, from
        (list.eq_of_mem_repeat m).symm ▸ by simp [hl _ (list.mem_cons_self _ _)] } }
end


lemma gen_is_gen2_bis (S : set α) : is_generating S ↔ is_generating2 S :=
begin
  split,
  { intros h g,
    have H := h g; clear h,
    induction H with ls prop,
    induction prop with p1 p2,
    have key_fact : ∀ x : {x // x ∈ ls}, ∃ p : α × ℤ, p.1 ∈ S ∧ power p = x.1,
    { intro x, cases x with x x_in_ls,
      specialize p2 x x_in_ls,
      cases p2 with a a,
        existsi ((x, 1) : α × ℤ),
        simp [a, gpow_one, power],
      existsi ((x⁻¹, -1) : α × ℤ),
      simp [a, gpow_neg, power] },
    clear p2,
    cases classical.axiom_of_choice key_fact with f prop,
    clear key_fact,
    dsimp at f prop,
    existsi (ls.attach.map f),
    split,
    { rw p1; clear p1 g,
      congr,
      suffices : ls = list.map (power ∘ f) (list.attach ls), 
        simpa using this,
      have fact := λ x, (prop x).2, 
      clear prop S,
      simp [comp, fact, list.attach_map_val],
      },
    { clear p1,
      intro p,
      have fact := λ x, (prop x).1,
      clear prop,
      simp,
      intros x h a,
      rw ←a,
      specialize fact ⟨x, h⟩,
      assumption,},
  },
  { 
    intros hyp_gen2 g, specialize hyp_gen2 g, rcases hyp_gen2 with ⟨l, rfl, Hl2⟩,
    induction l with a l IH,
    -- empty list case
    { existsi ([]),
      simp },
    -- non-empty list case
    { cases a with x n,
      induction n with d Hd,
      { 
        rw list.map_cons,

        admit },
      { admit } },
    }
end

/-
lemma gen_is_gen2 (S : set α) : is_generating S ↔ is_generating2 S :=
begin
apply iff.intro,
  unfold is_generating,
  unfold is_generating2,
  intros h g,
  have H := h g; clear h,
  induction H with list prop,
  induction prop with p1 p2,
  have key_fact : ∀ x ∈ list, ∃ n : ℤ, ∃ y ∈ S, x = y^n,
    intro x,
    intro x_in_list,
    specialize p2 x x_in_list,
    cases p2 with a,
      existsi (1:ℤ),
      existsi x,
      simp [a, gpow_one],
    existsi -(1:ℤ),
    existsi x⁻¹,
    simp [a, gpow_minus_one],
  
    
    
  admit,
admit,
end
-/


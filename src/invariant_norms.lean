import tactic.finish
import algebra.group algebra.big_operators

noncomputable theory
local attribute [instance] classical.prop_decidable
local attribute [simp] mul_assoc

open list

variables {α β : Type} [group α] [group β] {a b g h : α}


-- Conjuguation in a group
--------------------------

def conj (a b : α) := a*b*a⁻¹

@[simp] lemma conj_action : conj (g * h) a = conj g (conj h a) :=
by simp[conj]

@[simp] lemma conj_by_one : conj 1 a = a :=
by simp[conj]

instance conj.is_group_hom : is_group_hom (conj a) :=
⟨λ x y, by simp [conj, mul_assoc]⟩

lemma inv_conj : conj a (b⁻¹) = (conj a b)⁻¹ :=
is_group_hom.inv (conj a) b

lemma conj_mul : conj g (a * b) = conj g a * conj g b :=
is_group_hom.mul _ _ _

@[simp] lemma conj_one : conj a 1 = 1 :=
is_group_hom.one (conj a)

-- Products
-----------

/- "is_product S n a" means a can be written as a product of n elements of S or S⁻¹ -/
def is_product (S : set α) (n : ℕ) (g : α) : Prop :=
∃ l : list α, g = prod l ∧ (∀ x ∈ l, x ∈ S ∨ x⁻¹ ∈ S) ∧ l.length = n

lemma is_product_mul {S : set α} {m n a b}
  (h₁ : is_product S m a) (h₂ : is_product S n b) : is_product S (m + n) (a * b) :=
begin
  rcases h₁ with ⟨l₁, prod₁, inS₁, len₁⟩,
  rcases h₂ with ⟨l₂, prod₂, inS₂, len₂⟩,

  existsi l₁ ++ l₂, -- denoted by l in comments
  repeat {split},
  { -- prove a*b = prod l
    simp [prod₁,prod₂] },
  { -- prove elements of l are in S or S⁻¹
    simpa,
    intros x x_in_l₁_or_l₂,
    cases x_in_l₁_or_l₂,
    { apply inS₁ x, assumption },
    { apply inS₂ x, assumption },
  },
  { -- prove length l is m + n
  simp [len₁, len₂] }
end

lemma is_product_inv (S : set α) {n a} (h : is_product S n a) : is_product S n (a⁻¹) :=
begin
  rcases h with ⟨l, product, inS, len⟩,
  existsi map (λ x, x⁻¹) (reverse l),
  repeat {split},
  { rw product,
    apply inv_prod },
  { simpa,
    intros,
    have H := (inS x_1) a_1,
    have H' : x_1 = x⁻¹ := eq_inv_of_eq_inv (eq.symm a_2),
    simp[H'] at H,
    exact or.symm H },
  { simpa }
end


lemma is_product_conj {S T : set α} (g) (H : ∀ a, a ∈ S → conj g a ∈ T)
  {n a} (h : is_product S n a) : is_product T n (conj g a) :=
begin
  rcases h with ⟨l, prod, inS, len⟩,
  existsi (map (conj g) l),
  repeat {split},
  { rw prod,
    apply is_group_hom.prod },
  { clear prod a len n,
    intros x x_in_conj_l,
    rw mem_map at x_in_conj_l,
    rcases x_in_conj_l with ⟨b, b_in_l, conj_b_x⟩,
    specialize inS b b_in_l, clear b_in_l l,
    cases inS,
    { have conj_in_T := H b inS,
      rw conj_b_x at conj_in_T,
      exact or.inl conj_in_T},
    { have conj_in_T := H b⁻¹ inS, 
      rw [inv_conj, conj_b_x] at conj_in_T,
      exact or.inr conj_in_T } },
  { simp[len] }
end

--- Generating sets
-------------------

def is_generating (S : set α) : Prop := 
∀ g : α, ∃ n : ℕ, is_product S n g

structure generating_set :=
(set : set α)
(gen : is_generating set)

-- Invariant norms on a group
-----------------------------

structure is_invariant_norm (ν : α → ℕ) : Prop :=
  (nonneg : ∀ g : α, 0 ≤ ν g) -- this is silly but ultimately the target will be ℝ
  (eq_zero : ∀ g : α, ν g = 0 → g = 1)
  (mul : ∀ g h : α, ν (g*h) ≤ ν g + ν h)
  (inv : ∀ g : α, ν g⁻¹ = ν g)
  (conj : ∀ g h : α, ν (conj h g) = ν g)
     
def is_conj_invariant_set (S : set α) : Prop :=
   ∀ g s : α, s ∈ S → conj g s ∈ S
     

/- Given a generating set S and an alement a,
   gen_norm S a is the minimal number of elements of S or S⁻¹ 
   required to write a as a product. 
   The next two lemma prove the definition is what it should be -/
def gen_norm (S : generating_set) (a : α) := nat.find (S.gen a)

lemma is_product_norm (S : generating_set) (g : α) :
is_product S.set (gen_norm S g) g :=
nat.find_spec (S.gen g)

lemma norm_min (S : generating_set) {a : α} {n} :
is_product S.set n a → gen_norm S a ≤ n :=
by apply nat.find_min' (S.gen a) 


lemma inv_norm_of_inv_set [str : group α] (S : @generating_set α str) :
is_conj_invariant_set S.set → is_invariant_norm (gen_norm S) :=
begin
  intro inv_hyp,
  constructor; intros,
  { apply nat.zero_le },
  { have H' := is_product_norm S g,
    rw a at H',
    rcases H' with ⟨l, prod, inS, len⟩,
    rw [eq_nil_of_length_eq_zero len] at prod,
    simp at prod,
    assumption },
  { have g_prod := is_product_norm S g,
    have h_prod := is_product_norm S h,
    have estimate := is_product_mul g_prod h_prod,
    exact norm_min S estimate },
  { apply le_antisymm,
    { apply norm_min,
      exact is_product_inv S.set (is_product_norm S g) },
    { apply norm_min,
      simpa using is_product_inv S.set  (is_product_norm S g⁻¹) } },
  { apply le_antisymm ; apply norm_min,
    { exact is_product_conj h (inv_hyp h) (is_product_norm S g) },
    { have prod := is_product_conj h⁻¹ (inv_hyp h⁻¹) (is_product_norm S (conj h g)),
      rw [←conj_action] at prod,
      simp[conj_by_one] at prod,
      exact prod } },
end

-- Commutators
--------------

def comm (a b : α) := a*b*a⁻¹*b⁻¹
local notation `[[`a, b`]]` := comm a b

lemma commuting : [[a, b]] = 1 ↔ a*b = b*a :=
by simp [comm, -mul_assoc, mul_inv_eq_iff_eq_mul]

lemma commutator_trading (comm_hyp : [[a, conj g b]] = 1) :
∃ c d e f : α, [[a, b]] = (conj c g⁻¹)*(conj d g)*(conj e g⁻¹)*(conj f g) :=
begin
  unfold conj at comm_hyp,
  let b':= g*b*g⁻¹,

  exact ⟨_, _, _, _, calc 
   [[a, b]] = a * b * a⁻¹ * b⁻¹ : rfl
      ...  = a * (g⁻¹  * b' * g)  * a⁻¹ * (g⁻¹ * b'⁻¹ * g)  : by simp
      ...  = a * g⁻¹ * (a⁻¹ * a) * b' * g  * a⁻¹ * (b'⁻¹ * b') * g⁻¹ * b'⁻¹ * g  : by simp
      ...  = a * g⁻¹ * (a⁻¹ * a) * b' * g  * (b'*a)⁻¹ * b' * g⁻¹ * b'⁻¹ * g  : by simp
      ...  = a * g⁻¹ * (a⁻¹ * a) * b' * g  * (a*b')⁻¹ * b' * g⁻¹ * b'⁻¹ * g  : by simp [commuting.1 comm_hyp]
      ...  = (conj a g⁻¹) * (conj (a*b') g) * (conj b' g⁻¹) * (conj 1 g) : by simp [conj]⟩
end
import analysis.topology.topological_space
import analysis.topology.continuity

open set function

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
  [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]


structure homeo (α β) [topological_space α] [topological_space β] extends equiv α β :=
(fun_con : continuous to_fun)
(inv_con : continuous inv_fun)

instance : has_coe_to_fun (homeo α β) := ⟨_, λ f, f.to_fun⟩

theorem homeo.bijective (f : homeo α β) : bijective f := f.to_equiv.bijective

def homeo.comp : homeo α β → homeo β γ → homeo α γ
| ⟨e1@⟨f₁, g₁, _, _⟩, f₁_con, g₁_con⟩ ⟨e2@⟨f₂, g₂, _, _⟩, f₂_con, g₂_con⟩ :=
⟨e1.trans e2,
  continuous.comp f₁_con f₂_con,
  continuous.comp g₂_con g₁_con⟩

def homeo.symm (h : homeo α β) : homeo β α :=
{ fun_con := h.inv_con, inv_con := h.fun_con, .. h.to_equiv.symm }

--instance : has_inv (homeo α α) := ⟨λ f, f.symm⟩
local notation f`⁻¹` := f.symm
local notation f ∘ g := homeo.comp g f

theorem homeo.left_inverse (f : homeo α β) : left_inverse f⁻¹ f := f.left_inv

theorem homeo.right_inverse (f : homeo α β) : function.right_inverse f⁻¹ f := f.right_inv

@[simp] lemma homeo.comp_val (f : homeo α β) (g : homeo β γ) (x) : homeo.comp f g x = g (f x) :=
by cases f with e₁; cases g with e₂; cases e₁; cases e₂; refl

def homeo.id (α) [topological_space α] : homeo α α :=
{ fun_con := continuous_id, inv_con := continuous_id, .. equiv.refl α }

@[simp]
lemma home.id_apply : (homeo.id α : α → α) = id := rfl


@[simp] lemma homeo.id_val (x : α) : (homeo.id α) x = x := rfl

theorem homeo.ext {f g : homeo α β} (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr;
   exact equiv.eq_of_to_fun_eq (funext H)


lemma id_circ_f (f : homeo α β) : (homeo.id β) ∘ f = f :=
homeo.ext $ by simp


lemma f_circ_id (f : homeo α β) : f ∘ (homeo.id α) = f := 
homeo.ext $ by simp

lemma homeo_comp_assoc (f: homeo α β) (g : homeo β γ) (h : homeo γ δ) : (h ∘ g) ∘ f = h ∘ (g ∘ f) :=
homeo.ext $ by simp

lemma homeo.mul_left_inv (f: homeo α β) : f ∘ f⁻¹ = homeo.id β :=
homeo.ext
begin
  suffices : ∀ (x : β), f (f⁻¹ x) = x,
    simp [this],
  intro,
  cases f,
  rw homeo.symm,
  apply equiv.apply_inverse_apply,
end

lemma homeo.symm_comp (h : homeo α β) : h⁻¹ ∘ h = homeo.id α :=
begin
  apply homeo.ext,
  simp,
  intros,
  cases h with f f_con f_inv_con,
  rw homeo.symm,
  apply equiv.apply_inverse_apply,
end
universe u
instance aut (α : Type u) [topological_space α] : group (homeo α α) :=
{ mul := (∘), 
  mul_assoc := λ a b c, homeo.ext $ by simp,
  one := homeo.id α, 
  one_mul := id_circ_f,
  mul_one := f_circ_id, 
  inv := homeo.symm, 
  mul_left_inv := homeo.symm_comp }

@[simp] theorem aut_mul_val (f g : homeo α α) (x) : (f * g) x = f (g x) :=
homeo.comp_val _ _ _

@[simp] theorem aut_one_val (x) : (1 : homeo α α) x = x := rfl

theorem aut_inv (f : homeo α α) : f⁻¹ = f.symm := rfl

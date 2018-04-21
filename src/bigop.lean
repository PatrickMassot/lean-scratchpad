import data.list.basic
import data.nat.prime

open classical

open list
/- The elements being manipulated are of type R, with operation op, with range r ∈ list I, filtered by the predicte I-/
variables {R : Type*} {I : Type*} (op : R → R → R) (nil: R) 
          (r : list I) (P : I → Prop) [∀ i, decidable $ P i] (F : I → R)

def apply_bigop : R :=
foldr (λ i x, if P i then op (F i) x else x) nil r

/- variable in filtered list -/

local notation `big[`:0 op `/`:0 nil `]_(`:0 binder `∈` r `|` P:(scoped p, p) `)` F:(scoped f, f) := 
apply_bigop op nil r P F

local notation `Σ_(`:0 binder `∈` r `|` P:(scoped p, p) `)` F:(scoped f, f) := 
apply_bigop (+) 0 r P F

local notation `Π_(`:0 binder `∈` r `|` P:(scoped p, p) `)` F:(scoped f, f) := 
apply_bigop (*) 1 r P F

/- variable in unfiltered list -/

local notation `big[`:0 op `/`:0 nil `]_(`:0 binder `∈` r `)` F:(scoped f, f) := 
apply_bigop op nil r (λ i, true) F

local notation `Σ_(`:0 binder `∈` r `)` F:(scoped f, f) := 
apply_bigop (+) 0 r (λ i, true) F

local notation `Π_(`:0 binder `∈` r `)` F:(scoped f, f) := 
apply_bigop (*) 1 r (λ i, true) F

/- variable is natural numbers from a to b filtered -/

local notation `big[`:0 op `/`:0 nil `]_(`:0 binder `=` a `..` b `|` P:(scoped p, p) `)` F:(scoped f, f) := 
apply_bigop op nil (range' a (b-a+1)) P F

local notation `Σ_(`:0 binder `=` a `..` b `|` P:(scoped p, p)  `)` F:(scoped f, f) := 
apply_bigop (+) 0 (range' a (b-a+1)) P F

local notation `Π_(`:0 binder `=` a `..` b `|` P:(scoped p, p)  `)` F:(scoped f, f) := 
apply_bigop (*) 1 (range' a (b-a+1)) P F


/- variable is natural numbers from a to b -/

local notation `big[`:0 op `/`:0 nil `]_(`:0 binder `=` a `..` b `)` F:(scoped f, f) := 
apply_bigop op nil (range' a (b-a+1)) (λ i, true) F

local notation `Σ_(`:0 binder `=` a `..` b `)` F:(scoped f, f) := 
apply_bigop (+) 0 (range' a (b-a+1)) (λ i, true) F

local notation `Π_(`:0 binder `=` a `..` b `)` F:(scoped f, f) := 
apply_bigop (*) 1 (range' a (b-a+1)) (λ i, true) F

#eval big[(*)/1]_(i ∈ (range' 1 5) | true) i
#eval big[(*)/1]_(i ∈ (range' 1 5)) i
#eval big[(*)/1]_(i = 1 .. 5) i
#eval big[(*)/1]_(i=1..5) i
#eval Π_(i = 1..5) i
#eval Π_(i ∈ (range' 1 5) | true) i

#eval Σ_(i ∈ range 5 | nat.prime i) i
#eval Σ_(i = 1..5 | nat.prime i) i


lemma big_append [is_associative R op] (r₁ r₂ : list I) : 
(big[op/nil]_(i ∈ r₁++r₂ | (P i)) (F i)) = op (big[op/nil]_(i ∈ r₁ | (P i)) (F i)) (big[op/nil]_(i ∈ r₂ | (P i)) (F i)) :=
begin
  sorry
end

lemma sum_append (r₁ r₂ : list I) (F : I → ℕ): (Σ_(i ∈ r₁ ++ r₂ | P i) F i) =  (Σ_(i ∈ r₁ | P i) F i) + Σ_(i ∈ r₂ | P i) F i :=
big_append _ _ _ _ _ _
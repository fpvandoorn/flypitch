import ..src.fol

universe variable u

namespace hidden

inductive dvector (α : Type u) : ℕ → Type u
| nil {} : dvector 0
| cons : ∀{n}, α → dvector n → dvector (n+1)

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

structure Language : Type (u+1) := 
(functions : ℕ → Type u) (relations : ℕ → Type u)

end hidden

open fol
variable (L : Language.{u})

/- terms -/
namespace term1
inductive term : Type u
| var {} : ℕ → term
| func : ∀ {l : ℕ}, L.functions l → dvector term l → term
end term1

namespace term2
mutual inductive term, terms
with term : Type u
| var {} : ℕ → term
| func : ∀ {l : ℕ}, L.functions l → terms l → term
with terms : ℕ → Type u
| nil : terms 0
| cons : ∀{l}, term → terms l → terms (l+1)
end term2

namespace term3
structure Language' : Type (u+1) := 
(functions : Type u) (relations : Type u) 
(farity : functions → ℕ) (rarity : relations → ℕ) 

inductive preterm (L : Language'.{u}) : Type u
| var {} : nat → preterm 
| func : L.functions → preterm
| app : preterm → preterm → preterm

inductive good {L : Language'} : nat → preterm L → Prop 
| var : ∀ (k : nat), good 0 (preterm.var k)
| fnc : ∀ (f : L.functions), good (L.farity f) (preterm.func f) 
| app : ∀ t1 t2 l, good (l+1) t1 → good 0 t2 → good l (preterm.app t1 t2)

def term (L : Language') := {t : preterm L // good 0 t}
end term3

namespace term4
inductive preterm : ℕ → Type u
| var {} : ℕ → preterm 0
| func : ∀ {l : ℕ}, L.functions l → preterm l
| app : ∀ {l : ℕ}, preterm (l+1) → preterm 0 → preterm l

def term := preterm L 0

inductive preformula : ℕ → Type u
| falsum {} : preformula 0
| equal (t₁ t₂ : term L) : preformula 0
| rel {l : ℕ} (R : L.relations l) : preformula l
| apprel {l : ℕ} (f : preformula (l + 1)) (t : term L) : preformula l
| imp (f₁ f₂ : preformula 0) : preformula 0
| all (f : preformula 0) : preformula 0

@[reducible] def formula := preformula L 0

end term4

/- de Bruijn variables -/

inductive peano_functions : ℕ → Type
| zero : peano_functions 0
| succ : peano_functions 1
| plus : peano_functions 2
| mult : peano_functions 2

def L_peano : Language := ⟨peano_functions, λ n, empty⟩

def L_peano_zero : term L_peano := func peano_functions.zero
def L_peano_succ (t : term L_peano) : term L_peano := 
app (func peano_functions.succ) t
def L_peano_plus (t₁ t₂ : term L_peano) : term L_peano := 
@term_of_function L_peano 2 peano_functions.plus t₁ t₂
def L_peano_mult (t₁ t₂ : term L_peano) : term L_peano := 
@term_of_function L_peano 2 peano_functions.mult t₁ t₂

local infix ` ⊹ `:100 := L_peano_plus
local infix ` × `:150 := L_peano_mult
instance : has_zero (term L_peano) := ⟨L_peano_zero⟩

#check ∀' ∀' (&0 ⊹ &1 ≃ &1 ⊹ &0)

def L_peano_le (x y : term L_peano) : formula L_peano := sorry 
local infix ` <== `:80 := L_peano_le
#check ∀' ∀' (&0 <== &1 ⟹ ∀' (&1 ⊹ &0 <== &2 ⊹ &0))

/- ∀x y, ... -/

#check ∀' ∀' (∀' (&0 × &1 <== &2) ⟹ (&0 : term L_peano) ≃ L_peano_zero)
/- ∀x y, ... -/

/- lifting and substitution -/
def lift_term_at : ∀ {l}, preterm L l → ℕ → ℕ → preterm L l
| _ &k          n m := &(if m ≤ k then k+n else k)
| _ (func f)    n m := func f
| _ (app t₁ t₂) n m := app (lift_term_at t₁ n m) (lift_term_at t₂ n m)

def subst_term : ∀ {l}, preterm L l → term L → ℕ → preterm L l
| _ &k          s n := if k < n then &k else if n < k then &(k - 1) else s ↑ n
| _ (func f)    s n := func f
| _ (app t₁ t₂) s n := app (subst_term t₁ s n) (subst_term t₂ s n)

def lift_formula_at : ∀ {l}, preformula L l → ℕ → ℕ → preformula L l
| _ falsum       n m := falsum
| _ (t₁ ≃ t₂)    n m := lift_term_at t₁ n m ≃ lift_term_at t₂ n m
| _ (rel R)      n m := rel R
| _ (apprel f t) n m := apprel (lift_formula_at f n m) (lift_term_at t n m)
| _ (f₁ ⟹ f₂)   n m := lift_formula_at f₁ n m ⟹ lift_formula_at f₂ n m
| _ (∀' f)       n m := ∀' lift_formula_at f n (m+1)

def subst_formula : ∀ {l}, preformula L l → term L → ℕ → preformula L l
| _ falsum       s n := falsum
| _ (t₁ ≃ t₂)    s n := subst_term t₁ s n ≃ subst_term t₂ s n
| _ (rel R)      s n := rel R
| _ (apprel f t) s n := apprel (subst_formula f s n) (subst_term t s n)
| _ (f₁ ⟹ f₂)   s n := subst_formula f₁ s n ⟹ subst_formula f₂ s n
| _ (∀' f)       s n := ∀' subst_formula f s (n+1)







/- bounded terms -/

def L_peano_bd_plus {n} (t₁ t₂ : bounded_term L_peano n) : 
  bounded_term L_peano n := 
@bounded_term_of_function L_peano 2 n peano_functions.plus t₁ t₂
def L_peano_bd_mult {n} (t₁ t₂ : bounded_term L_peano n) : 
  bounded_term L_peano n := 
@bounded_term_of_function L_peano 2 n peano_functions.mult t₁ t₂
local infix ` +' `:100 := L_peano_bd_plus
local infix ` ×' `:150 := L_peano_bd_mult
def succ {n} : bounded_term L_peano n → bounded_term L_peano n := @bounded_term_of_function L_peano 1 n peano_functions.succ
def zero {n} : bounded_term L_peano n := bd_const peano_functions.zero

def p_zero_ne_succ : sentence L_peano := ∀' ∼(zero ≃ succ &0)
def p_succ_inj : sentence L_peano := ∀' ∀'(succ &1 ≃ succ &0 ⟹ &1 ≃ &0)
def p_add_zero : sentence L_peano := ∀'(&0 +' zero ≃ &0)
def p_add_succ : sentence L_peano := ∀' ∀'(&1 +' succ &0 ≃ succ (&1 +' &0))
def p_mul_zero : sentence L_peano := ∀'(&0 ×' zero ≃ zero)
def p_mul_succ : sentence L_peano := ∀' ∀' (&1 ×' succ &0 ≃ &1 ×' &0 +' &1)

@[simp] def alls {L : Language} : Πn, bounded_formula L n → bounded_formula L 0
| 0     f := f
| (n+1) f := alls n (∀' f)

def p_induction {n : ℕ} (ψ : bounded_formula L_peano (n+1)) : 
  sentence L_peano :=
alls n (ψ[zero/0] ⟹ (∀' (ψ ⟹ (ψ ↑' 1 # 1)[succ &0/0]) ⟹ ∀' ψ))

def L_peano_le' (t₁ t₂ : term L_peano) : formula L_peano := 
∃' (&0 ⊹ t₁ ↑ 1 ≃ t₂ ↑ 1)

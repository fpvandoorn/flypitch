import ..src.fol

universe variable u

namespace hidden

#print vector

inductive dvector (α : Type u) : ℕ → Type u
| nil {} : dvector 0
| cons : ∀{n}, α → dvector n → dvector (n+1)

structure Language : Type (u+1) := 
(functions : ℕ → Type u) (relations : ℕ → Type u)

end hidden 

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

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

def not'  (f : formula L)     : formula L := f ⟹ ⊥
def and'  (f₁ f₂ : formula L) : formula L := ∼(f₁ ⟹ ∼f₂)
def or'   (f₁ f₂ : formula L) : formula L := ∼f₁ ⟹ f₂
def biimp (f₁ f₂ : formula L) : formula L := (f₁ ⟹ f₂) ⊓ (f₂ ⟹ f₁)
def ex    (f : formula L)     : formula L := ∼ ∀' ∼f




/- de Bruijn variables -/

inductive peano_functions : ℕ → Type
| zero : peano_functions 0
| succ : peano_functions 1
| plus : peano_functions 2
| mult : peano_functions 2

def L_peano : Language := ⟨peano_functions, λ n, empty⟩

def zero : term L_peano := func peano_functions.zero
def succ (t : term L_peano) : term L_peano := 
app (func peano_functions.succ) t
def L_peano_plus (t₁ t₂ : term L_peano) : term L_peano := 
@term_of_function L_peano 2 peano_functions.plus t₁ t₂
def L_peano_mult (t₁ t₂ : term L_peano) : term L_peano := 
@term_of_function L_peano 2 peano_functions.mult t₁ t₂

local infix ` +' `:100 := L_peano_plus
local infix ` ×' `:150 := L_peano_mult

#check ∀' ∀' (&0 +' &1 ≃ &1 +' &0)
/- -/

def L_peano_le (x y : term L_peano) : formula L_peano := sorry
local infix ` <== `:80 := L_peano_le

#check ∀' ∀' (&0 <== &1 ⟹ ∀' (&1 +' &0 <== &2 +' &0))
/- -/

#check ∀' ∀' (∀' (&0 ×' &1 <== &2) ⟹ (&0 : term L_peano) ≃ zero)
/- -/

def p_zero_ne_succ : formula L_peano := ∀' ∼(zero ≃ succ &0)
def p_succ_inj : formula L_peano := ∀' ∀'(succ &1 ≃ succ &0 ⟹ &1 ≃ &0)
def p_add_zero : formula L_peano := ∀'(&0 +' zero ≃ &0)
def p_add_succ : formula L_peano := ∀' ∀'(&1 +' succ &0 ≃ succ (&1 +' &0))
def p_mul_zero : formula L_peano := ∀'(&0 ×' zero ≃ zero)
def p_mul_succ : formula L_peano := ∀' ∀' (&1 ×' succ &0 ≃ &1 ×' &0 +' &1)





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


def L_peano_le' (t₁ t₂ : term L_peano) : formula L_peano := 
∃' (&0 +' t₁ ↑ 1 ≃ t₂ ↑ 1)
-- ∃ x, x + t₁ = t₂ 







/- provability -/

inductive prf : set (formula L) → formula L → Type u
| axm     {Γ A} (h : A ∈ Γ) : prf Γ A
| impI    {Γ : set $ formula L} {A B} (h : prf (insert A Γ) B) : prf Γ (A ⟹ B)
| impE    {Γ} (A) {B} (h₁ : prf Γ (A ⟹ B)) (h₂ : prf Γ A) : prf Γ B
| falsumE {Γ : set $ formula L} {A} (h : prf (insert ∼A Γ) ⊥) : prf Γ A
| allI    {Γ A} (h : prf ((λx, x ↑ 1) '' Γ) A) : prf Γ (∀' A)
| allE₂   {Γ} A t (h : prf Γ (∀' A)) : prf Γ (A[t // 0])
| ref     (Γ t) : prf Γ (t ≃ t)
| subst₂  {Γ} (s t f) (h₁ : prf Γ (s ≃ t)) (h₂ : prf Γ (f[s // 0])) : prf Γ (f[t // 0])

/- we prove meta-theoretic properties: weakening, substitution, ... -/




/- bounded terms -/

namespace hidden
inductive bounded_preterm (n : ℕ) : ℕ → Type u
| bd_var {} : ∀ (k : fin n), bounded_preterm 0
| bd_func {} : ∀ {l : ℕ} (f : L.functions l), bounded_preterm l
| bd_app : ∀ {l : ℕ} (t : bounded_preterm (l + 1)) (s : bounded_preterm 0), bounded_preterm l

def bounded_term   (n) := bounded_preterm L n 0
def closed_preterm (l) := bounded_preterm L 0 l
def closed_term        := closed_preterm L 0

inductive bounded_preformula : ℕ → ℕ → Type u
| bd_falsum {} {n} : bounded_preformula n 0
| bd_equal {n} (t₁ t₂ : bounded_term L n) : bounded_preformula n 0
| bd_rel {n l : ℕ} (R : L.relations l) : bounded_preformula n l
| bd_apprel {n l} (f : bounded_preformula n (l + 1)) (t : bounded_term L n) : bounded_preformula n l
| bd_imp {n} (f₁ f₂ : bounded_preformula n 0) : bounded_preformula n 0
| bd_all {n} (f : bounded_preformula (n+1) 0) : bounded_preformula n 0

def bounded_formula (n : ℕ) := bounded_preformula L n 0
def presentence     (l : ℕ) := bounded_preformula L 0 l
def sentence                := presentence L 0

def Theory := set (sentence L)
end hidden

namespace bounded_peano
def L_peano_bd_plus {n} (t₁ t₂ : bounded_term L_peano n) : bounded_term L_peano n := 
@bounded_term_of_function L_peano 2 n peano_functions.plus t₁ t₂
def L_peano_bd_mult {n} (t₁ t₂ : bounded_term L_peano n) : bounded_term L_peano n := 
@bounded_term_of_function L_peano 2 n peano_functions.mult t₁ t₂
local infix ` +' `:100 := L_peano_bd_plus
local infix ` ×' `:150 := L_peano_bd_mult
def succ {n} : bounded_term L_peano n → bounded_term L_peano n := 
@bounded_term_of_function L_peano 1 n peano_functions.succ
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

def p_induction {n : ℕ} (ψ : bounded_formula L_peano (n+1)) : sentence L_peano :=
alls n (ψ[zero/0] ⟹ (∀' (ψ ⟹ (ψ ↑' 1 # 1)[succ &0/0]) ⟹ ∀' ψ))

end bounded_peano




/- semantics -/

namespace hidden
structure Structure :=
(carrier : Type u) 
(fun_map : ∀{n}, L.functions n → dvector carrier n → carrier)
(rel_map : ∀{n}, L.relations n → dvector carrier n → Prop) 
end hidden
namespace hidden2
variable {L}
def realize_term {S : Structure L} (v : ℕ → S) : 
  ∀{l} (t : preterm L l) (xs : dvector S l), S.carrier
| _ &k          xs := v k
| _ (func f)    xs := S.fun_map f xs
| _ (app t₁ t₂) xs := realize_term t₁ $ realize_term t₂ ([])::xs

def realize_formula {S : Structure L} : ∀{l}, (ℕ → S) → preformula L l → dvector S l → Prop
| _ v falsum       xs := false
| _ v (t₁ ≃ t₂)    xs := realize_term v t₁ xs = realize_term v t₂ xs
| _ v (rel R)      xs := S.rel_map R xs
| _ v (apprel f t) xs := realize_formula v f $ realize_term v t ([])::xs
| _ v (f₁ ⟹ f₂)   xs := realize_formula v f₁ xs → realize_formula v f₂ xs
| _ v (∀' f)       xs := ∀(x : S), realize_formula (v [x // 0]) f xs

@[simp] def realize_bounded_term {S : Structure L} {n} (v : dvector S n) : 
  ∀{l} (t : bounded_preterm L n l) (xs : dvector S l), S.carrier
| _ &k             xs := v.nth k.1 k.2
| _ (bd_func f)    xs := S.fun_map f xs
| _ (bd_app t₁ t₂) xs := realize_bounded_term t₁ $ realize_bounded_term t₂ ([])::xs

@[simp] def realize_bounded_formula {S : Structure L} : 
  ∀{n l} (v : dvector S n) (f : bounded_preformula L n l) (xs : dvector S l), Prop
| _ _ v bd_falsum       xs := false
| _ _ v (t₁ ≃ t₂)       xs := realize_bounded_term v t₁ xs = realize_bounded_term v t₂ xs
| _ _ v (bd_rel R)      xs := S.rel_map R xs
| _ _ v (bd_apprel f t) xs := realize_bounded_formula v f $ realize_bounded_term v t ([])::xs
| _ _ v (f₁ ⟹ f₂)      xs := realize_bounded_formula v f₁ xs →  realize_bounded_formula v f₂ xs
| _ _ v (∀' f)          xs := ∀(x : S), realize_bounded_formula (x::v) f xs

/- Now we can prove soundness! -/

end hidden2


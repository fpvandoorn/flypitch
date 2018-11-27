
universe variable u

inductive dvector (α : Type u) : ℕ → Type u
| nil {} : dvector 0
| cons : ∀{n} (x : α) (xs : dvector n), dvector (n+1)

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l


structure Language : Type (u+1) := 
(functions : ℕ → Type u) (relations : ℕ → Type u)

variable (L : Language.{u})

namespace term1
inductive term : Type u
| var {} : ℕ → term
| func : ∀ {l : ℕ}, L.functions l → dvector term l → term
end term1

namespace term2
mutual inductive term, terms
with term : Type u
| var {} : ℕ → term
| func : ∀ {l : ℕ} (f : L.functions l) (ts : terms l), term
with terms : ℕ → Type u
| nil : terms 0
| cons : ∀{l}, term → terms l → terms (l+1)
end term2

namespace term3
structure Language' : Type (u+1) := 
(functions : Type u) (relations : Type u) 
(farity : functions → ℕ) (rarity : relations → ℕ) 

inductive term (L : Language') : Type u
| var {} : ℕ → term
| func : ∀ {l : ℕ} (f : L.functions) (ts : list term), term
end term3


inductive preterm : ℕ → Type u
| var {} : ℕ → preterm 0
| func : ∀ {l : ℕ}, L.functions l → preterm l
| app : ∀ {l : ℕ}, preterm (l+1) → preterm 0 → preterm l

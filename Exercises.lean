-- try it
def Implies (p q : Prop) : Prop := p → q
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop

structure Proof ( p :  Prop ) : Type where
  proof : p
#print Proof
axiom and_comm_IBA ( p q : Prop): Proof (Implies (And p q) (And q p))
variable (p q : Prop)
#check and_comm_IBA p q

axiom modus_ponens: Proof (Implies p q) → Proof p → Proof q

axiom implies_intro :(Proof p → Proof q) → Proof (Implies p q)


-- try it
variable {p : Prop}
variable {q : Prop}
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

axiom hp: p

theorem t2 : q → p := t1 hp

-- try it
axiom unsound : False
-- Everything follows from false
theorem ex : 1 = 0 :=
  False.elim unsound

variable (p q r s : Prop)

theorem t3 (h₁ : p → r) (h₂ : r → s) : p → s :=
fun h₃ : p => h₂ (h₁ h₃)

theorem t4 (h₁ : p ∧ q) : p := And.left h₁
theorem t5 (h₁ : p ∧ q) : q := And.right h₁

theorem t6 (h₁ : p ∧ q) : q ∧ p := And.intro  (And.right h₁) (And.left h₁)

theorem t7 (h : p ∧ q) : q ∧ p :=
⟨ h.right , h.left ⟩

theorem t8 (h : p ∧ q) : p ∧ (q ∧ p) :=
⟨ h.left , ⟨ h.right, h.left ⟩ ⟩

theorem t9 (h: p ∨ q) : q ∨ p :=
Or.elim h
  (fun h₁ : p => Or.intro_right q h₁)
  (fun h₂ : q => Or.intro_left p h₂)

  theorem t10 (h : p → q) (h₁ : ¬ q) : ¬ p :=
  fun h₂ : p => h₁ (h h₂)

theorem and_swap : p ∧ q ↔ (q ∧ p) :=
Iff.intro
(fun h₀ : p ∧ q => ⟨ h₀.right , h₀.left ⟩ )
(fun h₁ : q ∧ p => ⟨ h₁.right , h₁.left ⟩ )

-- try it
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
Iff.intro
(fun h : p ∧ q => ⟨ And.right h , And.left h ⟩ )
(fun g : q ∧ p => ⟨ And.right g , And.left g ⟩ )

example : p ∨ q ↔ q ∨ p :=
Iff.intro
(fun h : p ∨ q =>
Or.elim h
(fun h₁ : p => Or.intro_right q h₁)
(fun h₂ : q => Or.intro_left p h₂)
)
(fun g : q ∨ p =>
Or.elim g
(fun g₁ : q => Or.intro_right p g₁)
(fun g₂ : p => Or.intro_left q g₂))
-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
Iff.intro
(fun f : (p ∧ q) ∧ r =>
⟨ And.left (And.left f), ⟨ And.right (And.left f) , And.right f ⟩ ⟩
)
(fun f : p ∧ (q ∧ r) =>
⟨ ⟨ And.left f , And.left (And.right f) ⟩  , And.right (And.right f) ⟩  )
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
Iff.intro
(fun h : (p ∨ q) ∨ r =>
Or.elim h
(fun h₁ : p ∨ q =>
Or.elim h₁
(fun h₂ : p => Or.intro_left (q ∨ r) h₂)
(fun h₃ : q => Or.intro_right p (Or.intro_left r h₃))
)
(fun h₄ : r => Or.intro_right p (Or.intro_right q h₄))
)
(fun g : p ∨ (q ∨ r) =>
Or.elim g
(fun g₁ : p => Or.intro_left r (Or.intro_left q g₁))
(fun g₂ : q ∨ r =>
Or.elim g₂
(fun g₄ : q => Or.intro_left r (Or.intro_right p g₄))
(fun g₅ : r => Or.intro_right (p ∨ q) g₅) )
)

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
Iff.intro
(fun f : p ∧ (q ∨ r) =>
have f₁ := And.left f
have f₂ := And.right f
Or.elim f₂
(fun f₃ : q => Or.intro_left (p ∧ r) (⟨ f₁ , f₃ ⟩ ))
(fun f₄ : r => Or.intro_right (p ∧ q) (⟨ f₁ , f₄ ⟩))
)
(fun h : (p ∧ q) ∨ (p ∧ r) =>
Or.elim h
(fun h₁ : p ∧ q =>
have h₂ := And.left h₁
have h₃ := And.right h₁
show p ∧ (q ∨ r) from ⟨ h₂ , Or.intro_left r h₃⟩ )
(fun g₁ : p ∧ r =>
have g₂ := And.left g₁
have g₃ := And.right g₁
show p ∧ (q ∨ r) from ⟨ g₂ , Or.intro_right q g₃ ⟩ ))


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
Iff.intro
(fun f : p ∨ (q ∧ r) =>
Or.elim f
(fun f₁ : p => ⟨ Or.intro_left q f₁ , Or.intro_left r f₁⟩ )
(fun f₂ : q ∧ r =>
have f₃ := And.left f₂
have f₄ := And.right f₂
show (p ∨ q) ∧ (p ∨ r) from ⟨ Or.intro_right p f₃ , Or.intro_right p f₄ ⟩ )
)
(fun h : (p ∨ q) ∧ (p ∨ r) =>
have h₁ := h.left
have h₂ := h.right
Or.elim h₁
(fun h₃ : p => Or.intro_left (q ∧ r) h₃)
(fun h₄ : q =>
Or.elim h₂
(fun h₅ : p => Or.intro_left (q ∧ r) h₅)
(fun h₆ : r => Or.intro_right p (⟨ h₄ , h₆ ⟩ )))
)

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
Iff.intro
(fun h : (p → (q → r)) =>
  (fun h₁ : p ∧ q =>
    (have h₂ := And.left h₁
    have h₃ := And.right h₁
    have h₄ := h h₂
    have h₅ := h₄ h₃
    show r from h₅))
)
(fun f : p ∧ q → r =>
fun f₁ : p =>
fun f₂ : q =>
show r from f ⟨ f₁ , f₂ ⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
Iff.intro
(fun f : (p ∨ q) → r =>
  have f₁ := fun f₂ : p => f (Or.intro_left q f₂)
  have f₃ := fun f₄ : q => f (Or.intro_right p f₄)
  show (p → r) ∧ (q → r) from ⟨ f₁ , f₃ ⟩
)
(fun g : (p → r) ∧ (q → r) =>
  fun g₁ : (p ∨ q) =>
    Or.elim g₁
    (fun g₂ : p => g.left g₂)
    (fun g₃ : q => g.right g₃)
  )
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
Iff.intro
(fun f : ¬(p ∨ q) =>
  have f₁ := fun f₂ : p => f (Or.intro_left q f₂)
  have f₃ := fun f₄ : q => f (Or.intro_right p f₄)
  have f₅ := ⟨ f₁ , f₃ ⟩
  show ¬p ∧ ¬q from f₅)
(fun h : ¬p ∧ ¬q =>
  have h₁ := h.left
  have h₂ := h.right
  fun g : p ∨ q =>
    Or.elim g
    (fun g₁ : p => h₁ g₁)
    (fun g₂ : q => h₂ g₂))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
fun a : ¬p ∨ ¬q =>
  fun a₁ : p ∧ q =>
    Or.elim a
    (fun a₂ : ¬p => a₂ (a₁.left))
    (fun a₃ : ¬q => a₃ (a₁.right))

example : ¬(p ∧ ¬p) :=
fun a : p ∧ ¬ p =>
  have h := a.left
  have f := a.right
  show False from f h
example : p ∧ ¬q → ¬(p → q) :=
fun a : p ∧ ¬q  =>
  fun b : p → q =>
    have c := b a.left
    have d := a.right c
    show False from d

example : ¬p → (p → q) :=
fun a : ¬p =>
  fun b : p =>
  have c := a b
  have d := False.elim c
  show q from d
example : (¬p ∨ q) → (p → q) :=
fun a : (¬ p ∨ q) =>
  fun b : p =>
  Or.elim a
  (fun c : ¬p => False.elim (c b))
  (fun d : q => d)

example : p ∨ False ↔ p :=
Iff.intro
(fun a : p ∨ False =>
  Or.elim a
  (fun b : p => b)
  (fun c : False => False.elim c))
(fun d : p =>
Or.intro_left False d)
example : p ∧ False ↔ False :=
Iff.intro
(fun a : p ∧ False => a.right)
(fun b : False => False.elim b)
example : (p → q) → (¬q → ¬p) :=
fun a : p → q =>
  fun b : ¬q =>
   fun c : p => b (a c)
-- try it
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
Iff.intro
(fun h : ∀ x, p x ∧ q x =>
have h₁ := fun y : α => (h y).left
have h₂ := fun z : α => (h z).right
show (∀ x, p x) ∧ (∀ x, q x) from ⟨ h₁ , h₂ ⟩)
(fun h : (∀ x, p x) ∧ (∀ x, q x) =>
  fun a : α => ⟨ h.left a , h.right a ⟩)
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
fun h : ∀ x , p x → q x =>
  fun g : ∀ x, p x =>
    fun a : α =>
      have h₁ := h a
      have h₂ := g a
      have h₃ := h₁ h₂
      show q a from h₃

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
fun h : (∀ x, p x) ∨ (∀ x, q x) =>
  fun a : α =>
    Or.elim h
    (fun h₁ : (∀ x, p x) => Or.intro_left (q a) (h₁ a))
    (fun h₂ : (∀ x, q x) => Or.intro_right (p a) (h₂ a))
-- try it
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
fun a : α =>
  Iff.intro
  (fun h : (∀ x : α , r) => h a)
  (fun g : r =>
    fun b : α => g)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry


example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
Iff.intro
(fun f : ∀ x, r → p x =>
  fun g : r =>
    fun b : α => (f b) g)
(fun f : r → ∀ x, p x =>
  fun a : α =>
    fun g : r => (f g) a)
    -- try it
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
Classical.byCases
(fun a : shaves barber barber =>
have h₁ := h barber
have h₂ := Iff.mp h₁
have h₃ := h₂ a
have h₄ := h₃ a
show False from h₄
)
(fun a : ¬ shaves barber barber =>
have h₁ := h barber
have h₂ := Iff.mpr h₁
have h₃ := h₂ a
have h₄ := a h₃
show False from h₄
)
-- try it
def even (n : Nat) : Prop := ∃ k : Nat , 2 * k = n

def prime (n : Nat) : Prop := ∀ k : Nat, (∃ m : Nat , k * m = n → (k = 1 ∨ k = n))

def infinitely_many_primes : Prop := ∀ n : Nat , (∃ k : Nat, (prime k ∧ n < k))

def Fermat_prime (n : Nat) : Prop := ∃ k : Nat, (prime n ∧ n = ((2 ^ 2)^k) + 1)

def infinitely_many_Fermat_primes : Prop := ∀ n : Nat , ∃ k : Nat , (n < k ∧ Fermat_prime k)

def goldbach_conjecture : Prop :=
∀ n : Nat , ((even n ∧ n > 2) → ∃ k₁ k₂ : Nat (prime k₁ ∧ prime k₂ ∧ k₁ + k₂ = n))

def Goldbach's_weak_conjecture : Prop := ∀ n : Nat, ((n > 5 ∧ ¬ even n) → ∃ k₁ k₂ k₃ : Nat, (prime k₁ ∧ prime k₂ ∧ prime k₃ ∧ n = k₁ + k₂ + k₃))

def Fermat's_last_theorem : Prop :=
¬(∀ n : Nat, (n > 2 → ∃ k₁ k₂ k₃: Nat (k₁ > 0 ∧ k₂ > 0 ∧ k₃ > 0 ∧ (k₁^ n + k₂ ^ n = k₃ ^ n ))))

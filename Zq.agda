{-# OPTIONS --cubical --safe --postfix-projections #-}
module Zq where

open import Cubical.Foundations.Everything hiding (Square)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Equality using (_≡p_; reflp; ctop)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (_⊎_ to infix 1 _⊎_)
open import Cubical.HITs.PropositionalTruncation as Tr
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Function.Base using (_∋_)
open import Level using (0ℓ; _⊔_)

open import Zb

-- Pairs

infix 2 _×_ _×?_
_×_ : ∀ {a b} → Type a → Type b → Type (a ⊔ b)
A × B = Σ A \ _ → B

_×?_ : ∀ {a b} {A : Type a} {B : Type b} → Dec A → Dec B → Dec (A × B)
yes a ×? yes b = yes (a , b)
yes _ ×? no ¬b = no λ (a , b) → ¬b b
no ¬a ×? _ = no λ (a , b) → ¬a a

-- Cubical stuff

module _ {ℓ} {A : Type ℓ} where

  infixr 30 _∙↕_

  diag36 : {a b c : A} (p : a ≡ b) (q : b ≡ c) → Square p q p q
  diag36 {a = a} {b} {c} p q =
    top-face (diag3 p) (diag6 (sym q)) (diag3 p) (diag6 (sym q)) (λ _ _ → b)

  isSet⇒squareFull : isSet A →
                     {a0 a1 b0 b1 : A} (aa : a0 ≡ a1) (bb : b0 ≡ b1)
                     (ab0 : a0 ≡ b0) (ab1 : a1 ≡ b1) → Square aa bb ab0 ab1
  isSet⇒squareFull is aa bb ab0 ab1 = toPathP (is _ _ _ _)

  reface-Square : {a0 a1 b0 b1 : A} {aa aa′ : a0 ≡ a1} {bb bb′ : b0 ≡ b1}
                  {ab0 ab0′ : a0 ≡ b0} {ab1 ab1′ : a1 ≡ b1} →
                  aa ≡ aa′ → bb ≡ bb′ → ab0 ≡ ab0′ → ab1 ≡ ab1′ →
                  Square aa′ bb′ ab0′ ab1′ → Square aa bb ab0 ab1
  reface-Square aaq bbq ab0q ab1q sq =
    top-face (λ i j → aaq j i) (λ i j → bbq j i)
             (λ i j → ab0q j i) (λ i j → ab1q j i) sq

  _∙↕_ : ∀ {a0 a1 b0 b1 c0 c1 : A} {aa : a0 ≡ a1} {bb : b0 ≡ b1} {cc : c0 ≡ c1}
         {ab0 : a0 ≡ b0} {bc0 : b0 ≡ c0} {ab1 : a1 ≡ b1} {bc1 : b1 ≡ c1} →
         Square aa bb ab0 ab1 → Square bb cc bc0 bc1 →
         Square aa cc (ab0 ∙ bc0) (ab1 ∙ bc1)
  (α ∙↕ β) i = α i ∙ β i

-- Integers as differences of two natural numbers

infix 6 _-_ _-ℤ_

data ℤq : Type 0ℓ where
  _-_ : (m n : ℕ) → ℤq
  reduce : ∀ m n → suc m - suc n ≡ m - n

-- Normal forms: differences where at least one is 0

record 𝕫q : Type 0ℓ where
  constructor _-_[_]
  field
    pos : ℕ
    neg : ℕ
    either0 : ∥ pos ≡ 0 ⊎ neg ≡ 0 ∥
open 𝕫q public

reflect′ : ℕ × ℕ → 𝕫q
reflect′ (0 , n) = 0 - n [ ∣ inl refl ∣ ]
reflect′ (m@(suc _) , 0) = m - 0 [ ∣ inr refl ∣ ]
reflect′ (suc m , suc n) = reflect′ (m , n)

reflect : ℤq → 𝕫q
reflect (m - n) = reflect′ (m , n)
reflect (reduce m n i) = reflect′ (m , n)

reify : 𝕫q → ℤq
reify (m - n [ prf ]) = m - n

reflect-reify : ∀ z → reflect (reify z) ≡ z
reflect-reify (0 - n [ prf ]) =
  λ i → 0 - n [ squash ∣ inl refl ∣ prf i ]
reflect-reify (m@(suc _) - 0 [ prf ]) =
  λ i → m - 0 [ squash ∣ inr refl ∣ prf i ]
reflect-reify (suc m - suc n [ prf ]) = ⊥.rec
  (Tr.rec {P = ⊥} (λ ()) (λ { (inl q) → snotz q ; (inr q) → snotz q }) prf)

reify-reflect′ : (mn@(m , n) : ℕ × ℕ) → reify (reflect′ mn) ≡ m - n
reify-reflect′ (0 , n) = refl
reify-reflect′ (m@(suc _) , 0) = refl
reify-reflect′ (suc m , suc n) = reify-reflect′ (m , n) ∙ sym (reduce m n)

reify-reflect : ∀ z → reify (reflect z) ≡ z
reify-reflect (m - n) = reify-reflect′ (m , n)
reify-reflect (reduce m n i) j =
  reface-Square refl refl refl (rUnit _)
    ((λ _ j → reify-reflect′ (m , n) j) ∙↕ diag2 (reduce m n))
    i j

ℤqis𝕫q : ℤq ≃ 𝕫q
ℤqis𝕫q = isoToEquiv record
  { fun = reflect; inv = reify
  ; rightInv = reflect-reify; leftInv = reify-reflect
  }

-- 𝕫q is a set, so ℤq is too.

to-𝕫q≡ : ∀ {mx my nx ny ex ey} → mx ≡ my × nx ≡ ny →
      mx - nx [ ex ] ≡ my - ny [ ey ]
to-𝕫q≡ {mx} {_} {nx} {_} {ex} {ey} (p , q)
  with reflp ← ctop p | reflp ← ctop q = λ i → mx - nx [ squash ex ey i ]

from-𝕫q≡ : ∀ {x y} → x ≡ y → x .pos ≡ y .pos × x .neg ≡ y .neg
from-𝕫q≡ q .fst i = q i .pos
from-𝕫q≡ q .snd i = q i .neg

_≟𝕫q_ : Discrete 𝕫q
x@(mx - nx [ ex ]) ≟𝕫q y@(my - ny [ ey ]) =
  mapDec to-𝕫q≡ (_∘ from-𝕫q≡) (discreteℕ mx my ×? discreteℕ nx ny)

𝕫q-isSet : isSet 𝕫q
𝕫q-isSet = Discrete→isSet _≟𝕫q_

ℤq-isSet : isSet ℤq
ℤq-isSet = subst isSet (sym (ua ℤqis𝕫q)) 𝕫q-isSet

-- ℤq is also equivalent to the bi-invertible maps definition.
-- Note: we rely on ℤ and ℤq being sets.

-- ℤ → ℤq

zeroℤq : ℤq
zeroℤq = 0 - 0

succℤq : ℤq → ℤq
succℤq (m - n) = suc m - n
succℤq (reduce m n i) = reduce (suc m) n i

predℤq : ℤq → ℤq
predℤq (m - n) = m - suc n
predℤq (reduce m n i) = reduce m (suc n) i

pred-succℤq : ∀ z → predℤq (succℤq z) ≡ z
pred-succℤq (m - n) = reduce m n
pred-succℤq (reduce m n i) j = diag36 (reduce (suc m) (suc n)) (reduce m n) i j

succ-predℤq : ∀ z → succℤq (predℤq z) ≡ z
succ-predℤq (m - n) = reduce m n
succ-predℤq (reduce m n i) j = diag36 (reduce (suc m) (suc n)) (reduce m n) i j

ℤtoℤq : ℤ → ℤq
ℤtoℤq zero = zeroℤq
ℤtoℤq (succ z) = succℤq (ℤtoℤq z)
ℤtoℤq (pred1 z) = predℤq (ℤtoℤq z)
ℤtoℤq (pred2 z) = predℤq (ℤtoℤq z)
ℤtoℤq (s z i) = pred-succℤq (ℤtoℤq z) i
ℤtoℤq (r z i) = succ-predℤq (ℤtoℤq z) i

-- ℤq → ℤ

ℕtoℤ : ℕ → ℤ
ℕtoℤ zero = zero
ℕtoℤ (suc m) = succ (ℕtoℤ m)

_-ℤ_ : (m n : ℕ) → ℤ
m -ℤ zero = ℕtoℤ m
m -ℤ suc n = pred1 (m -ℤ n)

suc‿-ℤ : ∀ m n → suc m -ℤ n ≡ succ (m -ℤ n)
suc‿-ℤ m zero = refl
suc‿-ℤ m (suc n) = cong pred1 (suc‿-ℤ m n) ∙ s _ ∙ sym (r' _)

ℤqtoℤ : ℤq → ℤ
ℤqtoℤ (m - n) = m -ℤ n
ℤqtoℤ (reduce m n i) = (cong pred1 (suc‿-ℤ m n) ∙ s (m -ℤ n)) i

-- Equivalence to ℤ

ℕtoℤtoℤq : ∀ m → ℤtoℤq (ℕtoℤ m) ≡ m - 0
ℕtoℤtoℤq zero = refl
ℕtoℤtoℤq (suc m) = cong succℤq (ℕtoℤtoℤq m)

⟦-ℤ⟧ : ∀ m n → ℤtoℤq (m -ℤ n) ≡ m - n
⟦-ℤ⟧ m zero = ℕtoℤtoℤq m
⟦-ℤ⟧ m (suc n) = cong predℤq (⟦-ℤ⟧ m n)

⟦succℤq⟧ : ∀ z → ℤqtoℤ (succℤq z) ≡ succ (ℤqtoℤ z)
⟦succℤq⟧ (m - n) = suc‿-ℤ m n
⟦succℤq⟧ (reduce m n i) j =
  isSet⇒squareFull ℤ-isSet
    (cong ℤqtoℤ (reduce (suc m) n))
    (cong succ (cong ℤqtoℤ (reduce m n)))
    (suc‿-ℤ (suc m) (suc n))
    (suc‿-ℤ m n) i j

⟦pred1ℤq⟧ : ∀ z → ℤqtoℤ (predℤq z) ≡ pred1 (ℤqtoℤ z)
⟦pred1ℤq⟧ (m - n) = refl
⟦pred1ℤq⟧ (reduce m n i) j =
  ℤ-isSet _ _
    (cong pred1 (suc‿-ℤ m (suc n)) ∙ s (pred1 (m -ℤ n)))
    (cong pred1 (cong ℤqtoℤ (reduce m n))) j i

⟦pred2ℤq⟧ : ∀ z → ℤqtoℤ (predℤq z) ≡ pred2 (ℤqtoℤ z)
⟦pred2ℤq⟧ z = ⟦pred1ℤq⟧ z ∙ coh _

ℤqtoℤtoℤq : ∀ z → ℤtoℤq (ℤqtoℤ z) ≡ z
ℤqtoℤtoℤq (m - n) = ⟦-ℤ⟧ m n
ℤqtoℤtoℤq (reduce m n i) j =
  isSet⇒squareFull ℤq-isSet
    (cong ℤtoℤq (cong ℤqtoℤ (reduce m n)))
    (reduce m n)
    (ℤqtoℤtoℤq (suc m - suc n))
    (ℤqtoℤtoℤq (m - n)) i j

ℤtoℤqtoℤ : ∀ z → ℤqtoℤ (ℤtoℤq z) ≡ z
ℤtoℤqtoℤ zero = refl
ℤtoℤqtoℤ (succ z) = ⟦succℤq⟧ (ℤtoℤq z) ∙ cong succ (ℤtoℤqtoℤ z)
ℤtoℤqtoℤ (pred1 z) = ⟦pred1ℤq⟧ (ℤtoℤq z) ∙ cong pred1 (ℤtoℤqtoℤ z)
ℤtoℤqtoℤ (pred2 z) = ⟦pred2ℤq⟧ (ℤtoℤq z) ∙ cong pred2 (ℤtoℤqtoℤ z)
ℤtoℤqtoℤ (s z i) j =
  let z′ = ℤtoℤq z in
  isSet⇒squareFull ℤ-isSet
    (cong ℤqtoℤ (cong ℤtoℤq (s z)))
    (s z)
    (⟦pred1ℤq⟧ (succℤq z′)
      ∙ cong pred1 (⟦succℤq⟧ z′ ∙ cong succ (ℤtoℤqtoℤ z)))
    (ℤtoℤqtoℤ z) i j
ℤtoℤqtoℤ (r z i) j =
  isSet⇒squareFull ℤ-isSet
    (cong ℤqtoℤ (cong ℤtoℤq (r z)))
    (r z)
    (⟦succℤq⟧ (ℤtoℤq (pred2 z))
      ∙ cong succ (⟦pred2ℤq⟧ (ℤtoℤq z) ∙ cong pred2 (ℤtoℤqtoℤ z)))
    (ℤtoℤqtoℤ z) i j

ℤ≃ℤq : ℤ ≃ ℤq
ℤ≃ℤq = isoToEquiv (iso ℤtoℤq ℤqtoℤ ℤqtoℤtoℤq ℤtoℤqtoℤ)

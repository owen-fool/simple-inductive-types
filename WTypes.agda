{-
   Implementing W-Types for my own understanding, following the development of
   the topic in the HoTT book. At the moment this file depends on Martin 
   Escardo's Type Topology library.
-}

{-# OPTIONS --safe --exact-split --without-K #-}
open import SpartanMLTT
open import UF-FunExt
open import UF-Subsingletons

module WTypes (fe : funext 𝓤₀ 𝓤₀) where

data ⊥ : 𝓤₀ ̇ where

-- I don't know whether or not function extensionality is required to prove this
-- but it feels bad that I've used it
no-function : (A : 𝓤₀ ̇) (f : ⊥ → A) → (λ ()) ≡ f
no-function A f = nfunext fe (λ ())

data ⊤ : 𝓤₀ ̇ where
 ⋆ : ⊤

data _+'_ (A : 𝓤₀ ̇) (B : 𝓤₀ ̇) : 𝓤₀ ̇ where
 inl' : A → A +' B
 inr' : B → A +' B

data ℕ' : 𝓤₀ ̇ where
 zero_ : ℕ'
 succ_ : ℕ' → ℕ'

data W (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) : 𝓤₀ ̇ where
 sup : (a : A) → (B a → W A B) → W A B

data 𝔹 : 𝓤₀ ̇ where
 b₀ : 𝔹
 b₁ : 𝔹

rec₂ : 𝓤₀ ̇ → 𝓤₀ ̇ → 𝔹 → 𝓤₀ ̇
rec₂ bot top b₀ = bot
rec₂ bot top b₁ = top

ℕʷ : 𝓤₀ ̇
ℕʷ = W 𝔹 (rec₂ ⊥ ⊤)

rec₊ : (A B : 𝓤₀ ̇) → (A → 𝓤₀ ̇) → (B → 𝓤₀ ̇) → (A + B) → 𝓤₀ ̇
rec₊ A B fA fB (inl x) = fA x
rec₊ A B fA fB (inr x) = fB x

Listʷ : 𝓤₀ ̇ → 𝓤₀ ̇
Listʷ A = W (⊤ + A) (rec₊ ⊤ A (λ _ → ⊥) (λ _ → ⊤))

0ʷ : ℕʷ
0ʷ = sup b₀ λ ()

1ʷ : ℕʷ
1ʷ = sup b₁ λ x → 0ʷ

succʷ : ℕʷ → ℕʷ
succʷ = λ n → sup b₁ (λ x → n)

module W-Induction (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) (E : W A B → 𝓤₀ ̇) where

 e-Type : 𝓤₀ ̇
 e-Type = (a : A) (f : B a → W A B) (g : (b : B a) → E (f b)) → E (sup a f)

 Induction : e-Type → (w : W A B) → E w
 Induction e (sup a f) = e a f (λ b → Induction e (f b))

module W-Induction₂ (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇)
                    (E : W A B → W A B → 𝓤₀ ̇) where

 e-Type₂ : 𝓤₀ ̇
 e-Type₂ = (a1 a2 : A) (f1 : B a1 → W A B) (f2 : B a2 → W A B)
            (g : (b1 : B a1) (b2 : B a2) → E (f1 b1) (f2 b2))
            → E (sup a1 f1) (sup a2 f2)

 Induction₂ : e-Type₂ → (w1 w2 : W A B) → E w1 w2
 Induction₂ e (sup a1 f1) (sup a2 f2) =
  e a1 a2 f1 f2 λ b1 b2 → Induction₂ e (f1 b1) (f2 b2)

open W-Induction

module W-Recursion (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) (E : W A B → 𝓤₀ ̇) where

 recʷ : (e-Type A B E) → (w : W A B) → E w
 recʷ = Induction A B E

 computation-rule : (e : e-Type A B E) (a : A) (f : B a → W A B) →
                    recʷ e (sup a f) ≡ e a f (λ b → recʷ e (f b))
 computation-rule e a f = refl

open W-Recursion

doubleʷ-aux : e-Type 𝔹 (rec₂ ⊥ ⊤) (λ _ → ℕʷ)
doubleʷ-aux b₀ f g = 0ʷ
doubleʷ-aux b₁ f g = succʷ (succʷ (g ⋆))

doubleʷ : ℕʷ → ℕʷ
doubleʷ = recʷ 𝔹 (rec₂ ⊥ ⊤) (λ _ → ℕʷ) doubleʷ-aux

2ʷ : ℕʷ
2ʷ = succʷ 1ʷ

4ʷ : ℕʷ
4ʷ = succʷ (succʷ 2ʷ)

module testing-doubleʷ where
 test1 : doubleʷ 0ʷ ≡ 0ʷ
 test1 = refl

 test2 : doubleʷ 1ʷ ≡ 2ʷ
 test2 = refl

 test3 : doubleʷ 2ʷ ≡ 4ʷ
 test3 = refl

+ʷ-aux : e-Type 𝔹 (rec₂ ⊥ ⊤) (λ _ → ℕʷ → ℕʷ)
+ʷ-aux b₀ f g n = n
+ʷ-aux b₁ f g (sup b₀ h) = sup b₁ f
+ʷ-aux b₁ f g (sup b₁ h) = succʷ (succʷ (g ⋆ (h ⋆)))

+ʷ : ℕʷ → ℕʷ → ℕʷ
+ʷ = Induction 𝔹 (rec₂ ⊥ ⊤) (λ _ → ℕʷ → ℕʷ) +ʷ-aux

3ʷ : ℕʷ
3ʷ = succʷ 2ʷ

module testing-+ʷ where
 
 test1 : (n : ℕʷ) → +ʷ 0ʷ n ≡ n
 test1 n = refl

 test2-aux : e-Type 𝔹 (rec₂ ⊥ ⊤) (λ m → (n : ℕʷ) → +ʷ m n ≡ +ʷ n m)
 test2-aux b₀ f g (sup b₀ h) = ap (sup b₀) (nfunext fe (λ ()))
 test2-aux b₀ f g (sup b₁ h) = refl
 test2-aux b₁ f g (sup b₀ h) = refl
 test2-aux b₁ f g (sup b₁ h) = ap (sup b₁)
  (nfunext fe λ _ → ap (sup b₁) (nfunext fe (λ _ → g ⋆ (h ⋆))))

-- again, heavy reliance on function extensionality feels innapropriate

 test2 : (m n : ℕʷ) → +ʷ m n ≡ +ʷ n m
 test2 = Induction 𝔹 (rec₂ ⊥ ⊤) (λ m → (n : ℕʷ) → +ʷ m n ≡ +ʷ n m) test2-aux

 test5-aux : e-Type 𝔹 (rec₂ ⊥ ⊤) (λ n → +ʷ 1ʷ n ≡ succʷ n)
 test5-aux b₀ f g = ap (sup b₁)
  (nfunext fe (λ _ → ap (sup b₀) (no-function ℕʷ f)))
 test5-aux b₁ f g = ap (sup b₁)
  (nfunext fe λ _ → ap (sup b₁) (nfunext fe γ))
  where
   γ : _
   γ ⋆ = refl

 test5 : (n : ℕʷ) → +ʷ 1ʷ n ≡ succʷ n
 test5 = Induction 𝔹 (rec₂ ⊥ ⊤) (λ n → +ʷ 1ʷ n ≡ succʷ n) test5-aux

 test3-aux-aux : e-Type 𝔹 (rec₂ ⊥ ⊤)
                 (λ m → (n : ℕʷ) → +ʷ 1ʷ (+ʷ m n) ≡ +ʷ (+ʷ 1ʷ m) n)
 test3-aux-aux b₀ f g n = refl
 test3-aux-aux b₁ f g (sup b₀ h) = refl
 test3-aux-aux b₁ f g (sup b₁ h) =
  ap (sup b₁) (nfunext fe (λ _ → ap (sup b₁)
              (nfunext fe λ _ → ((test5 (+ʷ (f ⋆) (h ⋆))) ⁻¹) ∙
               ((g ⋆ (h ⋆)) ∙ ap (λ - → +ʷ - (h ⋆)) (test5 (f ⋆))))))

 test3-aux-prim : (w : W 𝔹 (rec₂ ⊥ ⊤)) → _
 test3-aux-prim = Induction 𝔹 (rec₂ ⊥ ⊤)
                  ((λ m → (n : ℕʷ) → +ʷ 1ʷ (+ʷ m n) ≡ +ʷ (+ʷ 1ʷ m) n))
                  test3-aux-aux

 test3-aux : e-Type 𝔹 (rec₂ ⊥ ⊤)
             (λ l → (m n : ℕʷ) → +ʷ l (+ʷ m n) ≡ +ʷ (+ʷ l m) n)
 test3-aux b₀ f g (sup b₀ h) (sup b₀ i) = refl
 test3-aux b₀ f g (sup b₀ h) (sup b₁ i) = refl
 test3-aux b₀ f g (sup b₁ h) (sup b₀ i) = refl
 test3-aux b₀ f g (sup b₁ h) (sup b₁ i) = refl
 test3-aux b₁ f g (sup b₀ h) (sup b₀ i) = refl
 test3-aux b₁ f g (sup b₀ h) (sup b₁ i) = refl
 test3-aux b₁ f g (sup b₁ h) (sup b₀ i) = refl
 test3-aux b₁ f g (sup b₁ h) (sup b₁ i) = ap (sup b₁)
  (nfunext fe λ _ → ap (sup b₁)
  (nfunext fe λ _ →
                    (ap (Induction 𝔹 (rec₂ ⊥ ⊤) (λ _ → ℕʷ → ℕʷ) +ʷ-aux (f ⋆))
   ((test5 (Induction 𝔹 (rec₂ ⊥ ⊤) (λ _ → ℕʷ → ℕʷ) +ʷ-aux (h ⋆) (i ⋆))) ⁻¹))
   ∙ ((ap (+ʷ (f ⋆)) (test3-aux-prim (h ⋆) (i ⋆)))
   ∙ (g ⋆ (+ʷ 1ʷ (h ⋆)) (i ⋆)
   ∙ ((ap (λ - → +ʷ - (i ⋆)) (g ⋆ 1ʷ (h ⋆)))
   ∙ ((ap (λ - → +ʷ (+ʷ - (h ⋆)) (i ⋆)) (test2 (f ⋆) 1ʷ))
   ∙ ap (λ - → +ʷ - (i ⋆)) ((test3-aux-prim (f ⋆) (h ⋆))⁻¹))))
   ∙ ap (λ - → +ʷ - (i ⋆))
     (test5 (Induction 𝔹 (rec₂ ⊥ ⊤) (λ _ → ℕʷ → ℕʷ) +ʷ-aux (f ⋆) (h ⋆))))))

 test3 : (l m n : ℕʷ) → +ʷ l (+ʷ m n) ≡ +ʷ (+ʷ l m) n
 test3 = Induction 𝔹 (rec₂ ⊥ ⊤)
         (λ z → (m n : ℕʷ) → +ʷ z (+ʷ m n) ≡ +ʷ (+ʷ z m) n) test3-aux

 test4 : (n : ℕʷ) → +ʷ n 0ʷ ≡ n
 test4 = λ n → test2 n 0ʷ ∙ test1 n

 test6 : (n : ℕʷ) → +ʷ n 1ʷ ≡ succʷ n
 test6 = λ n → test2 n 1ʷ ∙ test5 n

 --test7 : (n : ℕʷ) → doubleʷ (succʷ n) ≡ +ʷ (doubleʷ n) 2ʷ
 --test7 n = {!!}
 -- TODO: Prove this!

module Uniqueness-Theorem (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) (E : W A B → 𝓤₀ ̇)
                          (e : e-Type A B E)
                          (g h : (w : W A B) → E w)
                          (p : (a : A) (f : B a → W A B) →
                               (g (sup a f) ≡ e a f (λ b → g (f b))))
                          (q : (a : A) (f : B a → W A B) → 
                               (h (sup a f) ≡ e a f (λ b → h (f b)))) where

 Uniqueness : g ≡ h
 Uniqueness = dfunext fe γ
  where
   γ-aux : e-Type A B (λ w → g w ≡ h w)
   γ-aux a f g₁ = (p a f)
                ∙ ((ap (λ - → e a f -) (dfunext fe λ b → g₁ b))
                ∙ (q a f) ⁻¹)

   γ : _
   γ = Induction A B (λ w → g w ≡ h w) γ-aux


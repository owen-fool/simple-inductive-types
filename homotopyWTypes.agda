{-# OPTIONS --safe --exact-split --without-K #-}
open import SpartanMLTT
open import UF-Base
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-Univalence
open import UF-EquivalenceExamples

open import WTypes
import W-Algebra
open import W-Algebra-Extended

module homotopyWTypes (fe : funext 𝓤₀ 𝓤₀) (ua : is-univalent 𝓤₀)
                      (fe' : funext (𝓤₀ ⁺) 𝓤₀) where

module projections (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) where
 prWj1 : W fe A B → A
 prWj2 : (w : W fe A B) → (B (prWj1 w) → W fe A B)
 prWj1 (sup a f) = a
 prWj2 (sup a f) = f

 prW-p : ∀ w → sup (prWj1 w) (prWj2 w) ≡ w
 prW-p (sup a f) = refl

Wd : (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) → 𝓤₁ ̇
Wd A B = Σ λ (W : 𝓤₀ ̇) →
         Σ λ (sup : ∀ a → (B a → W) → W) →
         ∀ (E : W → 𝓤₀ ̇) →
         ∀ (e : ∀ (a : A) (f : B a → W) → (∀ b → E (f b)) → E (sup a f)) →
         Σ λ (ind : ∀ (w : W) → E w) →
         ∀ a f → ind (sup a f) ≡ e a f (ind ∘ f)

module induction-eq (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) (E : W fe A B → 𝓤₀ ̇)
                    (e : ∀ a f → (∀ b → E (f b)) → E (sup a f)) where
 open W-Induction fe A B
 open projections A B

 open W-Algebra A B fe
 ret-prim : (ind : ∀ w → E w) → (∀ a f → ind (sup a f) ≡ e a f (ind ∘ f))
                                ◁ ((λ w → ind w) ≋ λ w →
                          transport (λ w → E w) (prW-p w) (e (prWj1 w) (prWj2 w) (ind ∘ prWj2 w)))
 ret-prim ind = r , (s , η)
  where
   r : _
   r p = λ a f → p (sup a f)

   s : _
   s p (sup a f) = p a f

   η : _
   η p = dfunext fe (λ a → dfunext fe (λ f → refl))

 ret1 : (ind : ∀ w → E w) → ((λ w → ind w) ≋ λ w →
                          transport (λ w → E w) (prW-p w) (e (prWj1 w) (prWj2 w) (ind ∘ prWj2 w)))
                            ◁ (ind ≋ Induction E e)
 ret1 ind = r , (s , η)
  where
   r : _
   r p (sup a f) = p (sup a f) ∙ (ap (e a f) ((dfunext fe (p ∘ f)) ⁻¹))

   s-aux : (p : ind ≋ λ w → transport E (prW-p w) (e (prWj1 w) (prWj2 w) (ind ∘ prWj2 w)))
           → e-Type (λ w → ind w ≡ Induction E e w)
   s-aux p a f g = p (sup a f) ∙ ap (e a f) (dfunext fe g)

   s : _
   s p = Induction _ (s-aux p)

   η-aux : (p : ind ≋ λ w → transport E (prW-p w) (e (prWj1 w) (prWj2 w) (ind ∘ prWj2 w)))
           → (r ∘ s) p ≋ p
   η-aux p (sup a f) = (r ∘ s) p (sup a f) ≡⟨ refl ⟩
                       (r (s p)) (sup a f) ≡⟨ refl ⟩
                       r (s p) (sup a f) ≡⟨ refl ⟩
                       (s p) (sup a f) ∙ ap (e a f) ((dfunext fe ((s p) ∘ f)) ⁻¹) ≡⟨ refl ⟩
                       p (sup a f) ∙ ap (e a f) (dfunext fe ((s p) ∘ f))
                       ∙ ap (e a f) ((dfunext fe ((s p) ∘ f)) ⁻¹)
                        ≡⟨ ∙assoc (p (sup a f)) (ap (e a f) (dfunext fe ((s p) ∘ f)))
                                  (ap (e a f) ((dfunext fe ((s p) ∘ f)) ⁻¹)) ⟩
                       p (sup a f) ∙ (ap (e a f) (dfunext fe ((s p) ∘ f))
                       ∙ ap (e a f) ((dfunext fe ((s p) ∘ f)) ⁻¹))
                        ≡⟨ ap (λ q → p (sup a f) ∙ (ap (e a f) (dfunext fe ((s p) ∘ f)) ∙ q))
                           (ap-sym (e a f) (dfunext fe ((s p) ∘ f)) ⁻¹) ⟩
                       p (sup a f) ∙ (ap (e a f) (dfunext fe ((s p) ∘ f))
                       ∙ (ap (e a f) (dfunext fe ((s p) ∘ f))) ⁻¹)
                        ≡⟨ ap (p (sup a f) ∙_)
                              ((right-inverse (ap (e a f) (dfunext fe ((s p) ∘ f)))) ⁻¹) ⟩
                       p (sup a f) ∙ refl ≡⟨ refl-right-neutral (p (sup a f)) ⟩
                       p (sup a f) ∎

   η : _
   η p = dfunext fe (η-aux p)

 ret2 : (ind : ∀ w → E w) → (ind ≋ Induction E e) ◁ (ind ≡ Induction E e)
 ret2 ind = r , (s , η)
  where
   r : _
   r p = happly p

   s : _
   s p = dfunext fe p

   η : _
   η p = happly-funext fe _ _ p

 ret3 : (ind : ∀ w → E w) → (∀ a f → ind (sup a f) ≡ e a f (ind ∘ f)) ◁
                              (ind ≡ Induction E e)
 ret3 ind = (∀ a f → ind (sup a f) ≡ e a f (ind ∘ f)) ◁⟨ ret-prim ind ⟩
            (((λ w → ind w) ≋ λ w →
            transport (λ w → E w) (prW-p w) (e (prWj1 w) (prWj2 w) (ind ∘ prWj2 w))) ◁⟨ ret1 ind ⟩
            ((ind ≋ Induction E e) ◁⟨ ret2 ind ⟩
            ((ind ≡ Induction E e) ◀)))

 ret4 : (Σ (λ (ind : ∀ w → E w) → (∀ a f → ind (sup a f) ≡ e a f (ind ∘ f)))) ◁
        (Σ (λ (ind : ∀ w → E w) → ind ≡ Induction E e))
 ret4 = Σ-retract ret3

 contr : is-contr (Σ (λ (ind : ∀ w → E w) → (∀ a f → ind (sup a f) ≡ e a f (ind ∘ f))))
 contr = retract-of-singleton ret4 (singleton-types-are-singletons! _ (Induction E e))

open W-Induction fe

open induction-eq

ρ : (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) → is-contr ((E : W fe A B → 𝓤₀ ̇)
              (e : (a : A) (f : B a → W fe A B) → (∀ b → E (f b)) → E (sup a f))
              → Σ (λ (ind : (w : W fe A B) → E w) →
                   (a : A) (f : B a → W fe A B) → ind (sup a f) ≡ e a f (ind ∘ f)))
ρ A B = Π-is-singleton fe' (λ E → Π-is-singleton fe (λ e → contr A B E e))

Wd' : (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) → 𝓤₁ ̇
Wd' A B = Σ λ (𝑾 : Σ λ (W : 𝓤₀ ̇) → ∀ a → (B a → W) → W) →
         ∀ (E : pr₁ 𝑾 → 𝓤₀ ̇) →
         ∀ (e : ∀ (a : A) (f : B a → (pr₁ 𝑾)) → (∀ b → E (f b)) → E ((pr₂ 𝑾) a f)) →
         Σ λ (ind : ∀ (w : pr₁ 𝑾) → E w) →
         ∀ a f → ind ((pr₂ 𝑾) a f) ≡ e a f (ind ∘ f)

𝕎 : (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) → (Wd' A B)
𝕎 A B = (W fe A B , sup) , (λ E e → Induction A B E e , λ a f → refl)

Wd≃Wd' : (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) → (Wd A B) ≃ Wd' A B
Wd≃Wd' A B = ≃-sym Σ-assoc

-- The type of homotopy W-Types (for some A, B) is contractible
-- This follows from the proof, in another file, that homotopy W-Types are initial W-Algebras, and
-- the fact that initial objects are always equal, and from ρ above which proves there is only one
-- induction function for the standard W, with the supremum.
contr-Wd : (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) → is-contr (Wd A B)
contr-Wd A B = equiv-to-singleton (Wd≃Wd' A B) γ
 where
  γ : _
  γ = (𝕎 A B) , p
   where
    p : _
    p ((𝒲 , 𝓈𝓊𝓅) , ℐ𝓃𝒹) = (to-Σ-≡ (γ1 , γ2)) ⁻¹
     where
      𝒲𝕀 : W-Algebra.isHinitᵂ A B fe (𝒲 , 𝓈𝓊𝓅)
      𝒲𝕀 = W-Algebra.homotopy-inductive-types.hindWisHinit A B fe 𝒲 𝓈𝓊𝓅
            (λ E e → pr₁ (ℐ𝓃𝒹 E e)) λ E e → pr₂ (ℐ𝓃𝒹 E e)
      
      γ1 : _
      γ2 : _
      γ1 = MainResult A B fe ua (𝒲 , 𝓈𝓊𝓅) (W fe A B , sup) 𝒲𝕀
           (W-Algebra.WTypeisHinitᵂ A B fe)
      γ2 = (pr₂ (ρ A B) _) ⁻¹ ∙ pr₂ (ρ A B) λ E e → Induction A B E e , λ a f → refl




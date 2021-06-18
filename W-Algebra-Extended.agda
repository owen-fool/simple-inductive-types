{-
   Proving a theorem from `Homotopy Initial Algebras in Type Theory' by Steve Awodey, Nicola 
   Gambino and Kristina Sojakova. Using Structural Identity Principle. This is used in the proof 
   that the type of W-Types with induction given only up to propositional equality is 
   contractible.
-}
{-# OPTIONS --safe --exact-split #-}
{-# OPTIONS --without-K #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-Subsingletons
open import UF-Equiv
open import UF-Base
open import UF-Univalence
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-SIP
open import UF-Retracts

open import WTypes
open import dfunext-lemmas

import W-Algebra

module W-Algebra-Extended (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) (fe : funext 𝓤₀ 𝓤₀)
                          (ua : is-univalent 𝓤₀) where
open W-Algebra A B fe
open sip

is-whom : (C D : WAlg) (f : pr₁ C → pr₁ D) → 𝓤₀ ̇
is-whom C D f = (λ (a : A) (h : B a → (pr₁ C)) → f (pr₂ C a h)) ≡ λ a h → pr₂ D a (f ∘ h)

whom : (C D : WAlg) → 𝓤₀ ̇
whom C D = Σ (λ (f : pr₁ C → pr₁ D) → (is-whom C D f))

𝟏 : (C : WAlg) → whom C C
𝟏 C = id , refl

whomComp : (C D E : WAlg) → whom D E → whom C D → whom C E
whomComp C D E (g , gₚ) (f , fₚ) = (g ∘ f) ,
 (dfunext fe (λ a → dfunext fe λ h →
 g (f (pr₂ C a h)) ≡⟨ ap g (happly (happly fₚ a) h) ⟩
 g (pr₂ D a (f ∘ h)) ≡⟨ happly (happly gₚ a) (f ∘ h) ⟩
 pr₂ E a (g ∘ f ∘ h) ∎))

Wι : (A₁ B₁ : WAlg) →
     ⟨ A₁ ⟩ ≃ ⟨ B₁ ⟩ → 𝓤₀ ̇
Wι A₁ B₁ (f , (g , fgₚ) , h , hfₚ) = is-whom A₁ B₁ f

whom-refl : (C : WAlg) → whomComp C C C (id , refl) (id , refl) ≡ (id , refl)
whom-refl C = to-Σ-≡ (refl ,
 (dfunext fe (λ a → dfunext fe λ h → refl)
   ≡⟨ ap (λ - → dfunext fe -) (dfunext fe (λ _ → dfunext-refl fe _)) ⟩
  dfunext fe (λ a → refl) ≡⟨ dfunext-refl fe _ ⟩
  refl ∎))

Wρ : (A₁ : Σ (λ X → (a : A) → (B a → X) → X)) → Wι A₁ A₁ (≃-refl ⟨ A₁ ⟩)
Wρ A₁ = refl

helpe : (X : 𝓤₀ ̇) → (s t : (a : A) → (B a → X) → X) →
        Wι (X , s) (X , t) (≃-refl X) UF-Retracts.◁ (s ≡ t) 
helpe X s t = r , (q , η)
 where
  r : _
  r refl = Wρ _

  q : _
  q refl = refl

  η : _
  η refl = refl

Wσ : {X : 𝓤₀ ̇} → (s t : (a : A) → (B a → X) → X) → is-equiv (canonical-map Wι Wρ s t)
Wσ {X} = canonical-map-equiv-criterion' Wι Wρ (helpe X)


SNS-for-Ws : SNS (λ (X : 𝓤₀ ̇) → (a : A) → (B a → X) → X) 𝓤₀
SNS-for-Ws = Wι , Wρ , Wσ

characterisation-of-W-≡ : (A₁ B₁ : Σ (λ X → (a : A) → (B a → X) → X)) →
                            (A₁ ≡ B₁) ≃ (A₁ ≃[ SNS-for-Ws ] B₁)
characterisation-of-W-≡ = characterization-of-≡ ua SNS-for-Ws

is-whom≃is-WHom : (C D : WAlg) (f : pr₁ C → pr₁ D) →
                  is-whom C D f ≃ (∀ a h → f (pr₂ C a h) ≡ pr₂ D a (f ∘ h))
is-whom≃is-WHom C D f = r , (s , η) , (s , ζ)
 where
  r : _
  r p a h = happly (happly p a) h

  s : _
  s p = dfunext fe (λ a → dfunext fe λ h → p a h)

  η : _
  η p = dfunext fe (λ a → dfunext fe λ h →
        happly (happly (dfunext fe (λ a₁ → dfunext fe λ h₁ → p a₁ h₁)) a) h
         ≡⟨ ap (λ - → happly (- a) h)
           (happly-funext fe (λ x x₁ → f (pr₂ C x x₁)) (λ x x₁ → pr₂ D x (f ∘ x₁))
                             (λ a₁ → dfunext fe λ h₁ → p a₁ h₁)) ⟩
        happly (dfunext fe λ h₁ → p a h₁) h ≡⟨ ap (λ - → - h)
               (happly-funext fe (λ x → f (pr₂ C a x)) (λ x → pr₂ D a (f ∘ x)) (p a)) ⟩
        p a h ∎)

  ζ : _
  ζ p = dfunext fe (λ a → dfunext fe λ h → (happly (happly p a) h))
         ≡⟨ ap (λ - → dfunext fe (λ a → - a))
            (dfunext fe (λ a → funext-happly fe (λ h → f (pr₂ C a h)) (λ h → pr₂ D a (f ∘ h))
            (happly p a))) ⟩  
        dfunext fe (λ a → happly p a) ≡⟨ funext-happly fe (λ x h → f (pr₂ C x h))
                                         (λ x h → pr₂ D x (f ∘ h)) p ⟩
        p ∎

whom≃WHom : (C D : WAlg) → whom C D ≃ WHom C D
whom≃WHom C D = Σ-cong (is-whom≃is-WHom C D)

whom-initiality : (C D : WAlg) → isHinitᵂ C → is-contr (whom C D)
whom-initiality C D C𝕀 = equiv-to-singleton (whom≃WHom C D) (C𝕀 D)

whom-center : (C D : WAlg) → isHinitᵂ C → whom C D
whom-center C D C𝕀 = center (whom-initiality C D C𝕀)

whom-center-𝟏 : (C : WAlg) (C𝕀 : isHinitᵂ C) → whom-center C C C𝕀 ≡ 𝟏 C
whom-center-𝟏 C C𝕀 = centrality (whom-initiality C C C𝕀) (𝟏 C)

initial-whom-comp : (C D : WAlg) (C𝕀 : isHinitᵂ C) (D𝕀 : isHinitᵂ D)
                 → whomComp C D C (whom-center D C D𝕀) (whom-center C D C𝕀) ≡ whom-center C C C𝕀
initial-whom-comp C D C𝕀 D𝕀 = centrality (whom-initiality C C C𝕀) _ ⁻¹

𝟏-initial-whom-comp : (C D : WAlg) (C𝕀 : isHinitᵂ C) (D𝕀 : isHinitᵂ D)
                  → whomComp C D C (whom-center D C D𝕀) (whom-center C D C𝕀) ≡ 𝟏 C
𝟏-initial-whom-comp C D C𝕀 D𝕀 = initial-whom-comp C D C𝕀 D𝕀 ∙ whom-center-𝟏 C C𝕀

MainResult : (C D : WAlg) → isHinitᵂ C → isHinitᵂ D → C ≡ D
MainResult C D C𝕀 D𝕀 = eqtofun (≃-sym (characterisation-of-W-≡ C D))
  ((pr₁ (whom-center C D C𝕀)) ,
  ((((pr₁ (whom-center D C D𝕀)) ,
  happly (pr₁ (from-Σ-≡ (𝟏-initial-whom-comp D C D𝕀 C𝕀)))) ,
  (pr₁ (whom-center D C D𝕀)) ,
  happly (pr₁ (from-Σ-≡ (𝟏-initial-whom-comp C D C𝕀 D𝕀)))) ,
  pr₂ (whom-center C D C𝕀)))

{-# OPTIONS --safe --exact-split --without-K #-}
open import SpartanMLTT
open import UF-Base
open import UF-FunExt
open import UF-Equiv
open import UF-Univalence
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-hlevels
open import UF-EquivalenceExamples
import WTypes
import W-Algebra
import W-Algebra-Extended

module homotopyWTypesTwo (fe : funext 𝓤₀ 𝓤₀) (ua : is-univalent 𝓤₀) 
                         (fe' : funext (𝓤₀ ⁺) 𝓤₀)
                         (UA : Univalence) where
open WTypes fe

moresilly : (X : 𝓤₀ ̇) (a b : X) → (λ (p : a ≡ b) → p ∙ refl) ∼ id
moresilly X a b p = refl-right-neutral p

moresilly' : (X : 𝓤₀ ̇) (a b : X) → (λ (p : a ≡ b) → p ∙ refl) ≡ id
moresilly' X a b = dfunext fe (moresilly X a b)

moresilly'' : (X : 𝓤₀ ̇) (a b : X) (p q : a ≡ b) (ρ : p ≡ q)→
              ap (λ (r : a ≡ b) → r ∙ refl) ρ ≡ ρ
moresilly'' X a b p .p refl = refl


silly100 : (X : 𝓤₀ ̇) (a b c : X) (p : a ≡ b) (q : c ≡ b) → p ∙ q ⁻¹ ∙ q ≡ p
silly100 X a b .b p refl = refl

silly200 : (X : 𝓤₀ ̇) (a b c : X) (p : a ≡ b) (q : b ≡ c) → p ∙ q ∙ q ⁻¹ ≡ p
silly200 X a b .b p refl = refl

sillycoherence : ∀ X a b c p q r → (ap (_∙ q) (silly200 X a b c p q) ⁻¹)
                                    ∙ ap (λ - → - ∙ q ⁻¹ ∙ q) r
                                    ∙ silly100 X a c b (p ∙ q) q ≡ r
sillycoherence X a b .b p refl r = ap (_∙ refl) refl ⁻¹ ∙ ap (λ - → - ∙ refl ⁻¹ ∙ refl) r ∙ refl
                                                         ≡⟨ refl-right-neutral _ ⟩
                                   ap (_∙ refl) refl ⁻¹ ∙ ap (λ - → - ∙ refl ⁻¹ ∙ refl) r
                                                         ≡⟨ ap
                                                            (_∙ ap (λ - → - ∙ refl ⁻¹ ∙ refl) r)
                                                            (moresilly'' _ _ _ _ _ refl ⁻¹) ⟩
                                   refl ⁻¹ ∙ ap (λ - → - ∙ refl ⁻¹ ∙ refl) r
                                                         ≡⟨ refl-left-neutral ⟩
                                   ap (λ - → - ∙ refl ⁻¹ ∙ refl) r ≡⟨ moresilly'' _ _ _ _ _ r ⟩
                                   r ∎

sillycoherence' : (X : 𝓤₀ ̇) (a b c : X) (p : a ≡ b) (q : b ≡ c) (r : a ≡ c) (R : p ∙ q ≡ r)
               → (ap (_∙ q) (silly200 X a b c p q) ⁻¹)
                ∙ ap (λ - → - ∙ q ⁻¹ ∙ q) R
                ∙ silly100 X a c b r q ≡ R
sillycoherence' X a b c p q .(p ∙ q) refl = sillycoherence X a b c p q refl

-- first, here's just some stuff for fun


silly : (Σ λ (b : 𝔹) → b ≡ b₀) ≃ (Σ λ (b : 𝔹) → b ≡ b₁)
silly = f , (g , fg) , (g , gf)
 where
  f : _
  f (.b₀ , refl) = b₁ , refl

  g : _
  g (.b₁ , refl) = b₀ , refl

  fg : _
  fg (.b₁ , refl) = refl

  gf : _
  gf (.b₀ , refl) = refl

silly₂ : (b₀ ≡ b₁) → ⊥
silly₂ p = transport (rec₂ ⊤ ⊥) p ⋆

-- initially i thought the below would not be false, that was dumb. Hence 'silly'
silly₃ : (∀ (A : 𝓤₀ ̇) (a b : A) → (Σ λ (c : A) → c ≡ a) ≃ (Σ λ (c : A) → c ≡ b) → a ≡ b) →
         ⊥
silly₃ f = silly₂ (f 𝔹 b₀ b₁ silly)

silly₄ : (∀ (A : 𝓤₀ ̇) (a b : A) → (Σ λ (c : A) → c ≡ a) ≡ (Σ λ (c : A) → c ≡ b) → a ≡ b) →
         ⊥
silly₄ f = silly₃ (λ A a b e →
           f A a b (eqtoid ua (Σ λ (c : A) → c ≡ a) (Σ λ (c : A) → c ≡ b) e))
-- this is, i guess, an interesting elementary property of identity types in HoTT

Ws : (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) → 𝓤₁ ̇
Ws A B = Σ λ (W₀ : 𝓤₀ ̇) →
         Σ λ (sup₀ : ∀ (a : A) → ((B a) → W₀) → W₀) →
         ∀ (C : 𝓤₀ ̇) →
         ∀ (c : ∀ (a : A) → ((B a) → C) → C) →
         Σ λ (rec₀ : W₀ → C) →
         Σ λ (β : ∀ (a : A) (f : B a → W₀) → rec₀ (sup₀ a f) ≡ c a (λ b → rec₀ (f b))) →
         ∀ (g h : W₀ → C) →
         ∀ (βg : ∀ (a : A) (f : B a → W₀) → g (sup₀ a f) ≡ c a (λ b → g (f b))) →
         ∀ (βh : ∀ (a : A) (f : B a → W₀) → h (sup₀ a f) ≡ c a (λ b → h (f b))) →
         Σ λ (α : ∀ (w : W₀) → g w ≡ h w) →
         ∀ a f → α (sup₀ a f) ∙ βh a f ≡ βg a f ∙ ap (c a) (dfunext fe (λ b → α (f b)))

module initiality (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) (W* : Ws A B) where

 open W-Algebra A B fe

 Wx : 𝓤₀ ̇
 Wx = pr₁ W*

 supx : ∀ (a : A) → ((B a) → Wx) → Wx
 supx = pr₁ (pr₂ W*)

 Wx* : WAlg
 Wx* = Wx , supx

 Wx-Iteration : (X : 𝓤₀ ̇) → ((a : A) (f : B a → X) → X) → Wx → X
 Wx-Iteration X e = pr₁ ((pr₂ (pr₂ W*)) X e)

 Wx-Iteration-path : (X : 𝓤₀ ̇) → (e : (a : A) (f : B a → X) → X) →
                     ∀ (a : A) (f : B a → Wx) →
                       Wx-Iteration X e (supx a f) ≡ e a (λ b → Wx-Iteration X e (f b))
 Wx-Iteration-path X e = pr₁ (pr₂ ((pr₂ (pr₂ W*)) X e))

 Wx-α-Induction : (X : 𝓤₀ ̇) (e : (a : A) (f : B a → X) → X) (g h : Wx → X)
                  (βg : ∀ (a : A) (f : B a → Wx) → g (supx a f) ≡ e a (λ b → g (f b)))
                  (βh : ∀ (a : A) (f : B a → Wx) → h (supx a f) ≡ e a (λ b → h (f b)))
               → ∀ (w : Wx) → g w ≡ h w
 Wx-α-Induction X e g h βg βh = pr₁ ((pr₂ (pr₂ ((pr₂ (pr₂ W*)) X e))) g h βg βh)

 Wx-α-Induction-path : (X : 𝓤₀ ̇) (e : (a : A) (f : B a → X) → X) (g h : Wx → X)
                  (βg : ∀ (a : A) (f : B a → Wx) → g (supx a f) ≡ e a (λ b → g (f b)))
                  (βh : ∀ (a : A) (f : B a → Wx) → h (supx a f) ≡ e a (λ b → h (f b)))
               → ∀ a f → (Wx-α-Induction X e g h βg βh) (supx a f) ∙ βh a f ≡
                           βg a f ∙ ap (e a) (dfunext fe ((Wx-α-Induction X e g h βg βh) ∘ f))
 Wx-α-Induction-path X e g h βg βh = pr₂ ((pr₂ (pr₂ ((pr₂ (pr₂ W*)) X e))) g h βg βh)

 module retractioning (C : 𝓤₀ ̇) (c : (a : A) (f : B a → C) → C) where

  -- see W-Algebra file for detailed attribution for this proof

  first-retraction : (h : Wx → C) → ((∀ a f → (h (supx a f)) ≡ c a (h ∘ f)))
                                    ◁ (h ≋ Wx-Iteration C c)
  first-retraction h = r , (s , η)
   where
    r : h ≋ Wx-Iteration C c →
          (a : A) (f : B a → Wx) → h (supx a f) ≡ c a (h ∘ f)
    s : (∀ a f → (h (supx a f)) ≡ c a (h ∘ f)) → h ≋ Wx-Iteration C c
    η : ∀ p → r (s p) ≡ p
    r p a f = h (supx a f) ≡⟨ p (supx a f) ⟩
              Wx-Iteration C c (supx a f) ≡⟨ Wx-Iteration-path C c a f ⟩
              c a (λ b → Wx-Iteration C c (f b)) ≡⟨ ap (c a) ((dfunext fe (p ∘ f)) ⁻¹) ⟩
              c a (h ∘ f) ∎
    s p = Wx-α-Induction C c h (Wx-Iteration C c) p (Wx-Iteration-path C c)
    η p = dfunext fe q
     where
      q : r (s p) ∼ p
      q a = dfunext fe q'
       where
        q' : r (s p) a ∼ p a
        q' f = r (s p) a f ≡⟨ refl ⟩
               (s p) (supx a f) ∙ (Wx-Iteration-path C c a f ∙
               ap (c a) ((dfunext fe ((s p) ∘ f)) ⁻¹))
                ≡⟨ (∙assoc ((s p) (supx a f)) (Wx-Iteration-path C c a f)
                   (ap (c a) (dfunext fe ((s p) ∘ f) ⁻¹))) ⁻¹ ⟩
               ((s p) (supx a f) ∙ (Wx-Iteration-path C c a f)) ∙
               ap (c a) ((dfunext fe ((s p) ∘ f)) ⁻¹)
                ≡⟨ ap (_∙ ap (c a) (dfunext fe (s p ∘ f) ⁻¹))
                   (Wx-α-Induction-path C c h (Wx-Iteration C c) p (Wx-Iteration-path C c) a f) ⟩
               p a f ∙ ap (c a) (dfunext fe ((s p) ∘ f)) ∙
               ap (c a) ((dfunext fe ((s p) ∘ f)) ⁻¹)
                ≡⟨ ∙assoc (p a f) (ap (c a) (dfunext fe ((s p) ∘ f)))
                                  (ap (c a) ((dfunext fe ((s p) ∘ f)) ⁻¹)) ⟩
               p a f ∙ (ap (c a) (dfunext fe ((s p) ∘ f)) ∙
               ap (c a) ((dfunext fe ((s p) ∘ f)) ⁻¹))
                ≡⟨ ap (λ - → p a f ∙ (ap (c a) (dfunext fe ((s p) ∘ f)) ∙ -))
                   ((ap-sym (c a) (dfunext fe ((s p) ∘ f))) ⁻¹) ⟩
               p a f ∙ (ap (c a) (dfunext fe ((s p) ∘ f)) ∙
               ((ap (c a) (dfunext fe ((s p) ∘ f))) ⁻¹))
                ≡⟨ ap (p a f ∙_) ((sym-is-inverse' (ap (c a) (dfunext fe ((s p) ∘ f)))) ⁻¹) ⟩
               p a f ∎

  second-retraction : (h : Wx → C) → (∀ a f → h (supx a f) ≡ c a (h ∘ f))
                                     ◁ (h ≡ Wx-Iteration C c)
  second-retraction h = (∀ a f → h (supx a f) ≡ c a (h ∘ f)) ◁⟨ first-retraction h ⟩
                        ((h ≋ Wx-Iteration C c) ◁⟨ ≃-gives-◁ (≃-sym (happly , (fe _ _))) ⟩
                        ((h ≡ Wx-Iteration C c) ◀))

  final-retraction : WHom (Wx , supx) (C , c) ◁ Σ λ h → h ≡ Wx-Iteration C c
  final-retraction = Σ-retract second-retraction

 isHinitWx* : isHinitᵂ Wx*
 isHinitWx* C = γ
  where
   open retractioning (pr₁ C) (pr₂ C)

   γ : _
   γ = retract-of-singleton final-retraction
       (singleton-types-are-singletons! _ (Wx-Iteration _ _))

module hinit→uniquenessetc (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) where

 open W-Algebra A B fe
 open W-Induction A B

 onlyonehinitproof : (pr qr : isHinitᵂ (W A B , sup)) → pr ≡ qr
 onlyonehinitproof pr qr = γ
  where
   γaux : pr ∼ qr
   γaux (C , sC) = to-Σ-≡ ((pr₂ (pr (C , sC))) (pr₁ (qr (C , sC))) ,
                   (dfunext fe (λ x → props-are-sets (singletons-are-props (qr (C , sC))) _ _)))
   γ : _
   γ = dfunext fe' γaux


Wh : ∀ (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) → 𝓤₁ ̇
Wh A B = Σ λ (W₀ : 𝓤₀ ̇) →
         Σ λ (sup₀ : (a : A) → (B a → W₀) → W₀)
         → W-Algebra.isHinitᵂ A B fe (W₀ , sup₀)

Wh' : ∀ (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) → 𝓤₁ ̇
Wh' A B = Σ λ (𝕎 : W-Algebra.WAlg A B fe) → W-Algebra.isHinitᵂ A B fe 𝕎

CANONWh' : ∀ A B → Wh' A B
CANONWh' A B = (W A B , sup) , (W-Algebra.WTypeisHinitᵂ A B fe)

is-centralCANONWh' : ∀ A B → is-central (Wh' A B) (CANONWh' A B)
is-centralCANONWh' A B (𝕎 , isHinit𝕎) =
 (to-Σ-≡ (W-Algebra-Extended.MainResult A B fe ua 𝕎 (W A B , sup)
          isHinit𝕎 (W-Algebra.WTypeisHinitᵂ A B fe) ,
          hinit→uniquenessetc.onlyonehinitproof A B _ _)) ⁻¹

isSingletonWh' : ∀ A B → is-singleton (Wh' A B)
isSingletonWh' A B = (CANONWh' A B) , (is-centralCANONWh' A B)

Wh≃Wh' : ∀ A B → (Wh A B) ≃ (Wh' A B)
Wh≃Wh' A B = ≃-sym Σ-assoc

isSingletonWh : ∀ A B → is-singleton (Wh A B)
isSingletonWh A B = equiv-to-singleton (Wh≃Wh' A B) (isSingletonWh' A B)

module singletonWs (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇)
                   (C : 𝓤₀ ̇) (c : ∀ (a : A) → ((B a) → C) → C) where

 open W-Algebra A B fe
 open initiality A B
 open hinit→uniquenessetc A B
 open W-Algebra-Extended A B fe ua
 open W-Induction A B


 massage : (g : W A B → C)
           (β : ∀ (a : A) (f : B a → W A B) → g (sup a f) ≡ c a (λ b → g (f b)))
        → ∀ (w : W A B) → g w ≡ c (W-proj₁ w) (λ b → g ((W-proj₂ w) b))
 massage g β (WTypes.sup a f) = β a f

 canonαAux : (g h : WHom (W A B , sup) (C , c)) → e-Type (λ w → ((pr₁ g) w ≡ (pr₁ h) w))
 canonαAux (g , βg) (h , βh) a f i = (βg a f ∙ ap (c a) (dfunext fe i)) ∙ (βh a f) ⁻¹

 canonα : (g h : WHom (W A B , sup) (C , c)) (w : W A B) → ((pr₁ g) w ≡ (pr₁ h) w)
 canonα g h = Induction _ (canonαAux g h)

 canonuniqueness : ∀ (g h : WHom (W A B , sup) (C , c)) a f →
                     canonα g h (sup a f) ∙ (pr₂ h) a f ≡
                     (pr₂ g) a f ∙ ap (c a)
                            (dfunext fe (λ b → canonα g h (f b)))
 canonuniqueness (g , βg) (h , βh) a f = silly100 _ _ _ _ _ (βh a f)

 

 module singletonα (g h : W A B → C)
                   (βg : ∀ (a : A) (f : B a → W A B) → g (sup a f) ≡ c a (λ b → g (f b)))
                   (βh : ∀ (a : A) (f : B a → W A B) → h (sup a f) ≡ c a (λ b → h (f b))) where

  zerothretract : (α : ∀ w → g w ≡ h w) →
                  ((∀ a f → α (sup a f) ∙ βh a f ≡ βg a f ∙ ap (c a) (dfunext fe (α ∘ f)))
                  ◁
                  (∀ w → α w ≡
                          massage g βg w ∙ ap (c (W-proj₁ w)) (dfunext fe (α ∘ (W-proj₂ w)))
                        ∙ (massage h βh w ⁻¹)))
  zerothretract α = r , s , η
   where
    r : _
    s : _
    η : _
    η₁ : ∀ (q : codomain r) (a : A) → ((r ∘ s) q) a ≡ q a
    η₂ : ∀ (q : codomain r) (a : A) f → (((r ∘ s) q) a) f ≡ q a f
    r p a f = ap (_∙ βh a f) (p (sup a f)) ∙ silly100 _ _ _ _ _ (βh a f)
    s q (sup a f) = (ap (_∙ βh a f ⁻¹) ((q a f) ⁻¹) ∙ silly200 _ _ _ _ _ (βh a f)) ⁻¹
    η₂ q a f = (r (s q)) a f ≡⟨ refl ⟩
               ap (_∙ βh a f) ((s q) (sup a f)) ∙ silly100 _ _ _ _ _ (βh a f) ≡⟨ refl ⟩
               ap (_∙ βh a f) ((ap (_∙ βh a f ⁻¹) (q a f ⁻¹) ∙ silly200 _ _ _ _ _ (βh a f)) ⁻¹)
               ∙ silly100 _ _ _ _ _ (βh a f) ≡⟨ ap (λ - → (ap (_∙ βh a f) -)
                                                           ∙ silly100 _ _ _ _ _ (βh a f))
                                                   (⁻¹-contravariant
                                                   (ap (_∙ βh a f ⁻¹) (q a f ⁻¹))
                                                   (silly200 _ _ _ _ _ (βh a f)) ⁻¹) ⟩
               ap (_∙ βh a f) (silly200 _ _ _ _ _ (βh a f) ⁻¹ ∙
                               ap (_∙ βh a f ⁻¹) (q a f ⁻¹) ⁻¹)
               ∙ silly100 _ _ _ _ _ (βh a f) ≡⟨ ap (_∙ silly100 _ _ _ _ _ (βh a f))
                                                   (ap-∙ (_∙ βh a f)
                                                         (silly200 _ _ _ _ _ (βh a f) ⁻¹)
                                                         (ap (_∙ βh a f ⁻¹) (q a f ⁻¹) ⁻¹)) ⟩
               ap (_∙ βh a f) (silly200 _ _ _ _ _ (βh a f) ⁻¹)
               ∙ ap (_∙ βh a f) (ap (_∙ βh a f ⁻¹) (q a f ⁻¹) ⁻¹)
               ∙ silly100 _ _ _ _ _ (βh a f) ≡⟨ ap
                                                (λ - → ap (_∙ βh a f)
                                                       (silly200 _ _ _ _ _ (βh a f) ⁻¹)
                                                       ∙ ap (_∙ βh a f) -
                                                       ∙ silly100 _ _ _ _ _ (βh a f))
                                                (ap-sym (_∙ βh a f ⁻¹) (q a f ⁻¹)) ⟩
               ap (_∙ βh a f) (silly200 _ _ _ _ _ (βh a f) ⁻¹)
               ∙ ap (_∙ βh a f) (ap (_∙ βh a f ⁻¹) ((q a f ⁻¹) ⁻¹))
               ∙ silly100 _ _ _ _ _ (βh a f) ≡⟨ ap
                                                (λ - → ap (_∙ βh a f)
                                                        (silly200 _ _ _ _ _ (βh a f) ⁻¹)
                                                        ∙ - ∙ silly100 _ _ _ _ _ (βh a f))
                                                (ap-ap (_∙ βh a f ⁻¹) (_∙ βh a f) ((q a f ⁻¹) ⁻¹)) ⟩
               ap (_∙ βh a f) (silly200 _ _ _ _ _ (βh a f) ⁻¹)
               ∙ ap (λ - → - ∙ βh a f ⁻¹ ∙ βh a f) ((q a f ⁻¹) ⁻¹)
               ∙ silly100 _ _ _ _ _ (βh a f) ≡⟨ ap
                                                (λ - → - ∙ ap (λ - → - ∙ βh a f ⁻¹ ∙ βh a f)
                                                               ((q a f ⁻¹) ⁻¹)
                                                          ∙ silly100 _ _ _ _ _ (βh a f))
                                                ((ap-sym (_∙ βh a f)
                                                         (silly200 _ _ _ _ _ (βh a f))) ⁻¹) ⟩
               (ap (_∙ βh a f) (silly200 _ _ _ _ _ (βh a f)) ⁻¹)
               ∙ ap (λ - → - ∙ βh a f ⁻¹ ∙ βh a f) ((q a f ⁻¹) ⁻¹)
               ∙ silly100 _ _ _ _ (βg a f ∙ ap (c a) (dfunext fe (α ∘ f))) (βh a f) ≡⟨
                                                sillycoherence' C (g (sup a f)) (h (sup a f))
                                                                (c a (λ b → h (f b)))
                                                                (α (sup a f)) (βh a f)
                                                                (βg a f ∙ ap (c a )
                                                                (dfunext fe (α ∘ f)))
                                                                ((q a f ⁻¹) ⁻¹) ⟩
               ((q a f ⁻¹) ⁻¹) ≡⟨ ⁻¹-involutive (q a f) ⟩
               q a f ∎
    η₁ q a = dfunext fe (η₂ q a)
    η q = dfunext fe (η₁ q)

  firstretract : (α : ∀ w → g w ≡ h w) →
                ((∀ w → α w ≡
                         massage g βg w ∙ ap (c (W-proj₁ w)) (dfunext fe (λ b → α (W-proj₂ w b)))
                         ∙ (massage h βh w ⁻¹))
                 ◁ ((λ w → α w)
                  ≋ λ w → canonα (g , βg) (h , βh) w)) 
  firstretract α = r , (s , η)
   where

    -- 14/05/21 maybe what i want for the first retraction is really:
    -- ((∀ a f → α (sup a f) ∙ βh a f ≡ βg a f ∙ ap (c a) (dfunext fe (λ b → α (f b))))
    --  ◁ (α ∙ βh a f ≋ canonα (C , c) (g , βg) (h , βh) ‌∙ βh a f)
    -- 10/06/21 you see the solution was to move all the multiplication onto one side only
    r : (λ w → α w)
       ≋ (λ w → canonα (g , βg) (h , βh) w) →
          (w : W A B) →
          α w ≡
          massage g βg w ∙ ap (c (W-proj₁ w)) (dfunext fe (λ b → α (W-proj₂ w b)))
          ∙ (massage h βh w ⁻¹)
    r p (WTypes.sup a f) = p (sup a f)
                         ∙ (ap (λ - → βg a f ∙ ap (c a) (dfunext fe -) ∙ βh a f ⁻¹)
                              (dfunext fe (p ∘ f)) ⁻¹)
    
    saux : (∀ w → α w ≡
                         massage g βg w ∙ ap (c (W-proj₁ w)) (dfunext fe (λ b → α (W-proj₂ w b)))
                         ∙ (massage h βh w ⁻¹))
         → e-Type (λ w → α w ≡ canonα (g , βg) (h , βh) w)
    saux q a f g' = q (sup a f) ∙ ap (λ - → βg a f ∙ ap (c a) (dfunext fe -) ∙ βh a f ⁻¹)
                                     (dfunext fe g')

    s : (∀ w → α w ≡
                      massage g βg w ∙ ap (c (W-proj₁ w)) (dfunext fe (λ b → α (W-proj₂ w b)))
                      ∙ (massage h βh w ⁻¹))
        → (λ w → α w)
          ≋ λ w → canonα (g , βg) (h , βh) w
    s q = Induction _ (saux q)

    η : (r ∘ s) ∼ id
    η q = dfunext fe η₁
     where
      η₁ : _
      η₁ (sup a f) = r (s q) (sup a f) ≡⟨ refl ⟩
                     (s q) (sup a f)
                     ∙ (ap (λ - → βg a f ∙ ap (c a) (dfunext fe -) ∙ βh a f ⁻¹)
                       (dfunext fe (s q ∘ f)) ⁻¹) ≡⟨ refl ⟩
                     q (sup a f) ∙ ap (λ - → βg a f ∙ ap (c a) (dfunext fe -) ∙ βh a f ⁻¹)
                                       (dfunext fe (s q ∘ f))
                     ∙  (ap (λ - → βg a f ∙ ap (c a) (dfunext fe -) ∙ βh a f ⁻¹)
                              (dfunext fe (s q ∘ f)) ⁻¹) ≡⟨
                               silly200 _ _ _ _ _
                               (ap (λ - → βg a f ∙ ap (c a) (dfunext fe -) ∙ βh a f ⁻¹)
                               (dfunext fe (s q ∘ f))) ⟩
                     q (sup a f) ∎

  ret3 : (α : ∀ w → g w ≡ h w)
       → (∀ a f → α (sup a f) ∙ βh a f ≡ βg a f ∙ ap (c a) (dfunext fe (α ∘ f)))
        ◁ (α ≡ canonα (g , βg) (h , βh))
  ret3 α = (∀ a f → α (sup a f) ∙ βh a f ≡ βg a f ∙ ap (c a) (dfunext fe (α ∘ f))) ◁⟨
                                                                                  zerothretract α ⟩
           ((∀ w → α w ≡ massage g βg w ∙ ap (c (W-proj₁ w)) (dfunext fe (α ∘ (W-proj₂ w)))
                                         ∙ massage h βh w ⁻¹) ◁⟨ firstretract α ⟩
           ((α ≋ canonα (g , βg) (h , βh)) ◁⟨ happly , ((dfunext fe) ,
                                              (happly-funext fe α (canonα (g , βg) (h , βh)))) ⟩
           ((α ≡ canonα (g , βg) (h , βh)) ◀)))

  finalretraction : (Σ λ (α : ∀ (w : W A B) → g w ≡ h w) →
                     ∀ a f → α (sup a f) ∙ βh a f ≡
                              βg a f ∙ ap (c a) (dfunext fe (λ b → α (f b))))
                    ◁ (Σ λ (α : ∀ w → g w ≡ h w) → α ≡ canonα (g , βg) (h , βh))
  finalretraction = Σ-retract ret3

  αsingl : is-singleton (Σ λ (α : ∀ (w : W A B) → g w ≡ h w) →
                         ∀ a f → α (sup a f) ∙ βh a f ≡
                                  βg a f ∙ ap (c a) (dfunext fe (λ b → α (f b))))
  αsingl = retract-of-singleton finalretraction (singleton-types-are-singletons! _ _) 

open singletonWs
open W-Algebra
open W-Algebra-Extended
open initiality

Ws' : (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) → 𝓤₁ ̇
Ws' A B = Σ λ (𝕎 : W-Algebra.WAlg A B fe) →
          ∀ (ℂ : W-Algebra.WAlg A B fe) →
          Σ λ (𝕣ec : W-Algebra.WHom A B fe 𝕎 ℂ) →
          ∀ (𝕘 𝕙 : W-Algebra.WHom A B fe 𝕎 ℂ) →
          Σ λ (α : ∀ (w : pr₁ 𝕎) → (pr₁ 𝕘) w ≡ (pr₁ 𝕙) w) →
          ∀ a f → α ((pr₂ 𝕎) a f) ∙ (pr₂ 𝕙) a f
                ≡ (pr₂ 𝕘) a f ∙ ap ((pr₂ ℂ) a) (dfunext fe (α ∘ f))


CANONWs' : ∀ A B → Ws' A B
CANONWs' A B = (W A B , sup) , (λ ℂ → ((W-Iteration' A B fe (pr₁ ℂ) (pr₂ ℂ)) , λ a f → refl) ,
               λ 𝕘 𝕙 → (canonα A B (pr₁ ℂ) (pr₂ ℂ) 𝕘 𝕙) ,
                         canonuniqueness A B (pr₁ ℂ) (pr₂ ℂ) 𝕘 𝕙)

is-centralCANONWs' : ∀ A B → is-central (Ws' A B) (CANONWs' A B)
is-centralCANONWs' A B 𝕎𝕤' = (to-Σ-≡ (γ₁ , Π-is-prop fe' γ₂ _ _)) ⁻¹
 where
  WsMap : Ws A B
  WsMap = (pr₁ (pr₁ 𝕎𝕤')) , ((pr₂ (pr₁ 𝕎𝕤')) , (λ C c → (pr₁ (pr₁ ((pr₂ 𝕎𝕤') (C , c)))) ,
          (pr₂ (pr₁ ((pr₂ 𝕎𝕤') (C , c)))) ,
          (λ g h βg βh → pr₂ (pr₂ 𝕎𝕤' (C , c)) (g , βg) (h , βh))))

  γ₁ : _
  γ₁ =
    (MainResult A B fe ua (W A B , sup) (pr₁ 𝕎𝕤') (WTypeisHinitᵂ A B fe) (isHinitWx* A B WsMap))
    ⁻¹

  γ₂ : _
  γ₂ (C , c) = Σ-is-prop (singletons-are-props (WTypeisHinitᵂ A B fe (C , c)))
               λ 𝕗 → Π-is-prop fe
               (λ 𝕘 → Π-is-prop fe
               λ 𝕙 → singletons-are-props
                      (singletonα.αsingl A B C c (pr₁ 𝕘) (pr₁ 𝕙) (pr₂ 𝕘) (pr₂ 𝕙)))

isSingletonWs' : ∀ A B → is-singleton (Ws' A B)
isSingletonWs' A B = CANONWs' A B , is-centralCANONWs' A B

Ws≃Ws' : ∀ A B → (Ws A B) ≃ (Ws' A B)
Ws≃Ws' A B = r , ((s , η₁) , (s , η₂))
 where
  r : _
  s : _
  η₁ : _
  η₂ : _
  r (𝒲 , sup𝒲 , Wsfun𝒲) = (𝒲 , sup𝒲) ,
                              λ ℂ → ((pr₁ (Wsfun𝒲 (pr₁ ℂ) (pr₂ ℂ))) ,
                              pr₁ (pr₂ (Wsfun𝒲 (pr₁ ℂ) (pr₂ ℂ)))) ,
                              λ 𝕘 𝕙 → pr₂ (pr₂ (Wsfun𝒲 (pr₁ ℂ) (pr₂ ℂ))) (pr₁ 𝕘) (pr₁ 𝕙)
                                                                             (pr₂ 𝕘) (pr₂ 𝕙)
  s (𝓦 , Ws'fun𝓦) = (pr₁ 𝓦) , ((pr₂ 𝓦) ,
                        λ C c → (pr₁ (pr₁ (Ws'fun𝓦 (C , c)))) ,
                                 ((pr₂ (pr₁ (Ws'fun𝓦 (C , c)))) ,
                        λ g h βg βh → pr₂ (Ws'fun𝓦 (C , c)) (g , βg) (h , βh)))
  η₁ x = refl
  η₂ x = refl

isSingletonWs : ∀ A B → is-singleton (Ws A B)
isSingletonWs A B = equiv-to-singleton (Ws≃Ws' A B) (isSingletonWs' A B)

module Equivalent! (A : 𝓤₀ ̇) (B : A → 𝓤₀ ̇) where

 
 open hinit→uniquenessetc A B
 
 
 Ws→Wh : Ws A B → Wh A B
 Ws→Wh Ws = (pr₁ Ws) , ((pr₁ (pr₂ Ws)) , isHinitWx* A B Ws)

 Wh→Ws : Wh A B → Ws A B
 Wh→Ws Wh = (pr₁ Wh) , (pr₁ (pr₂ Wh) ,
             λ C c → pr₁ (pr₁ (pr₂ (pr₂ Wh) (C , c))) ,
                      (pr₂ (pr₁ (pr₂ (pr₂ Wh) (C , c))) ,
             transport (λ (W* : WAlg A B fe) → (g h : pr₁ W* → C)
      (βg
       : (a : A) (f : B a → pr₁ W*) →
         g ((pr₂ W*) a f) ≡ c a (λ b → g (f b)))
      (βh
       : (a : A) (f : B a → pr₁ W*) →
         h ((pr₂ W*) a f) ≡ c a (λ b → h (f b))) →
      Σ
      (λ (α : ∀ w → g w ≡ h w) →
         (a : A) (f : B a → pr₁ W*) →
         α ((pr₂ W*) a f) ∙ βh a f ≡
         βg a f ∙ ap (c a) (dfunext fe (λ b → α (f b)))))
         (MainResult A B fe ua (W A B , sup) (pr₁ Wh , pr₁ (pr₂ Wh))
                               (WTypeisHinitᵂ A B fe) (pr₂ (pr₂ Wh)))
         λ g h βg βh → (λ w → canonα A B C c (g , βg) (h , βh) w) ,
                         canonuniqueness A B _ _ (g , βg) (h , βh)))


 finalè : (Wh A B) ≃ (Ws A B)
 finalè = Wh→Ws , (Ws→Wh , λ x → singletons-are-props (isSingletonWs A B) _ _) ,
                   Ws→Wh , λ x → singletons-are-props (isSingletonWh A B) _ _

 -- obviously there is a very similar proof that weak/homotopy W-types defined in the other
 -- way is equivalent to both these notions

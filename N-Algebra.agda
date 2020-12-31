{-
   Following the development of initial algebras in the HoTT book, for my own 
   understanding. At the moment this file depends on the experimental cubical 
   library.
-}

{-# OPTIONS --safe --no-import-sorts --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma

module N-Algebra where

ℕAlg : Type₁
ℕAlg = Σ Type (λ C → C × (C → C))

[_]Type : ℕAlg → Type
[ 𝒞 ]Type = fst 𝒞

[_]₀ : (𝒞 : ℕAlg) → [ 𝒞 ]Type
[ 𝒞 ]₀ = fst (snd 𝒞)

[_]ₛ : (𝒞 : ℕAlg) → [ 𝒞 ]Type → [ 𝒞 ]Type
[ 𝒞 ]ₛ = snd (snd 𝒞)

ℕHom : ℕAlg → ℕAlg → Type
ℕHom 𝒞 𝒟 = Σ ([ 𝒞 ]Type → [ 𝒟 ]Type)
              (λ h → (h [ 𝒞 ]₀ ≡ [ 𝒟 ]₀) ×
              ((c : [ 𝒞 ]Type) → (h ([ 𝒞 ]ₛ c) ≡ [ 𝒟 ]ₛ (h c))))

[[_][_]_]ₕ : (𝒞 𝒟 : ℕAlg) → (ℕHom 𝒞 𝒟) → [ 𝒞 ]Type → [ 𝒟 ]Type
[[ 𝒞 ][ 𝒟 ] h ]ₕ = fst h

[[_][_]_]₀ : (𝒞 𝒟 : ℕAlg) (h : ℕHom 𝒞 𝒟) →
             ([[ 𝒞 ][ 𝒟 ] h ]ₕ [ 𝒞 ]₀ ≡ [ 𝒟 ]₀)
[[ 𝒞 ][ 𝒟 ] h ]₀ = fst (snd h)

[[_][_]_]ₛ : (𝒞 𝒟 : ℕAlg) (h : ℕHom 𝒞 𝒟) (c : [ 𝒞 ]Type) → 
             ([[ 𝒞 ][ 𝒟 ] h ]ₕ ([ 𝒞 ]ₛ c) ≡ [ 𝒟 ]ₛ ([[ 𝒞 ][ 𝒟 ] h ]ₕ c))
[[ 𝒞 ][ 𝒟 ] h ]ₛ = snd (snd h)

isHinitℕ : ℕAlg → Type₁
isHinitℕ 𝕀 = (𝒞 : ℕAlg) → isContr (ℕHom 𝕀 𝒞)

ℕHomComp : (𝕀 𝕁 : ℕAlg) → ℕHom 𝕀 𝕁 → ℕHom 𝕁 𝕀 → ℕHom 𝕀 𝕀
ℕHomComp 𝕀 𝕁 f g = [[ 𝕁 ][ 𝕀 ] g ]ₕ ∘ [[ 𝕀 ][ 𝕁 ] f ]ₕ ,
                   (cong [[ 𝕁 ][ 𝕀 ] g ]ₕ [[ 𝕀 ][ 𝕁 ] f ]₀)
                    ∙ [[ 𝕁 ][ 𝕀 ] g ]₀ ,
                   λ c → (cong [[ 𝕁 ][ 𝕀 ] g ]ₕ ([[ 𝕀 ][ 𝕁 ] f ]ₛ c))
                           ∙ [[ 𝕁 ][ 𝕀 ] g ]ₛ ([[ 𝕀 ][ 𝕁 ] f ]ₕ c)

ℕHomid : (𝕀 : ℕAlg) → ℕHom 𝕀 𝕀
ℕHomid 𝕀 = (λ x → x) , (refl , (λ _ → refl))

Hinitℕcenter : (𝕀 𝕁 : ℕAlg) → isHinitℕ 𝕀 → ℕHom 𝕀 𝕁
Hinitℕcenter 𝕀 𝕁 𝕀I = fst (𝕀I 𝕁)

Hinitℕiden : (𝕀 𝕁 : ℕAlg) (𝕀I : isHinitℕ 𝕀) (f : ℕHom 𝕀 𝕁) →
             Hinitℕcenter 𝕀 𝕁 𝕀I ≡ f
Hinitℕiden 𝕀 𝕁 𝕀I = snd (𝕀I 𝕁)

Hinitℕid-iden : (𝕀 : ℕAlg) (f : ℕHom 𝕀 𝕀) → isHinitℕ 𝕀 → ℕHomid 𝕀 ≡ f
Hinitℕid-iden 𝕀 f 𝕀I = (sym (Hinitℕiden 𝕀 𝕀 𝕀I (ℕHomid 𝕀)))
                       ∙ Hinitℕiden 𝕀 𝕀 𝕀I f

ℕHomStrEquiv : StrEquiv {ℓ-zero} (λ C → C × (C → C)) ℓ-zero
ℕHomStrEquiv 𝒞 𝒟 (f , feq) =
 (f [ 𝒞 ]₀ ≡ [ 𝒟 ]₀) × ((c : [ 𝒞 ]Type) → f ([ 𝒞 ]ₛ c) ≡ [ 𝒟 ]ₛ (f c))

ℕHomMap : {X : Type} (s t : X × (X → X))
          → (ℕHomStrEquiv (X , s) (X , t) (idEquiv X))
          → s ≡ t
ℕHomMap s t = (λ e → ΣPathP ((fst e) , funExt (λ c → snd e c)))

ℕHomMap⁻ : {X : Type} (s t : X × (X → X))
           → s ≡ t
           → (ℕHomStrEquiv (X , s) (X , t) (idEquiv X))
ℕHomMap⁻ s t p = (λ i → fst (p i)) , λ c → (λ i → (snd (p i) c))

ℕHomMapSec : {X : Type} (s t : X × (X → X))
             → section (ℕHomMap s t) (ℕHomMap⁻ s t)
ℕHomMapSec s t b = refl

ℕHomMapRet : {X : Type} (s t : X × (X → X))
             → retract (ℕHomMap s t) (ℕHomMap⁻ s t)
ℕHomMapRet s t a = refl

ℕHomSNS : SNS (λ C → C × (C → C)) ℕHomStrEquiv
ℕHomSNS s t = ℕHomMap s t ,
              isoToIsEquiv (iso (ℕHomMap s t) (ℕHomMap⁻ s t)
                                (ℕHomMapSec s t) (ℕHomMapRet s t))

ℕHomUnivStr : UnivalentStr (λ C → C × (C → C)) ℕHomStrEquiv
ℕHomUnivStr {𝒞} {𝒟} (e , e-eq) =
 SNS→UnivalentStr ℕHomStrEquiv ℕHomSNS (e , e-eq)

ℕHom≡ₕ : (𝒞 𝒟 : ℕAlg) (f g : ℕHom 𝒞 𝒟) → f ≡ g
       → [[ 𝒞 ][ 𝒟 ] f ]ₕ ≡ [[ 𝒞 ][ 𝒟 ] g ]ₕ
ℕHom≡ₕ 𝒞 𝒟 f g p = λ i → fst (p i)

ℕHomiden : (𝕀 𝕁 : ℕAlg) (f : ℕHom 𝕀 𝕁) (g : ℕHom 𝕁 𝕀) →
           (ℕHomComp 𝕀 𝕁 f g ≡ ℕHomid 𝕀) × (ℕHomComp 𝕁 𝕀 g f ≡ ℕHomid 𝕁) →
           𝕀 ≡ 𝕁
ℕHomiden 𝕀 𝕁 f g (fg≡id , gf≡id) =
 sip {ℓ-zero} {ℓ-zero} {ℓ-zero} {λ C → C × (C → C)} ℕHomUnivStr 𝕀 𝕁 γ
 where
  γ : 𝕀 ≃[ (λ A B z → ℕHomStrEquiv (fst A , snd A) (fst B , snd B) z) ] 𝕁
  γ = isoToEquiv (iso [[ 𝕀 ][ 𝕁 ] f ]ₕ [[ 𝕁 ][ 𝕀 ] g ]ₕ
   (λ j^ → cong (λ - → - j^)
           (ℕHom≡ₕ 𝕁 𝕁 (ℕHomComp 𝕁 𝕀 g f) (ℕHomid 𝕁) gf≡id))
   λ i^ → cong (λ - → - i^)
           (ℕHom≡ₕ 𝕀 𝕀 (ℕHomComp 𝕀 𝕁 f g) (ℕHomid 𝕀) fg≡id)) , snd f

isHinitℕEq : (𝕀 𝕁 : ℕAlg) → isHinitℕ 𝕀 → isHinitℕ 𝕁 → 𝕀 ≡ 𝕁
isHinitℕEq 𝕀 𝕁 𝕀I 𝕁I = ℕHomiden 𝕀 𝕁 (Hinitℕcenter 𝕀 𝕁 𝕀I) (Hinitℕcenter 𝕁 𝕀 𝕁I)
                       ((sym (Hinitℕid-iden 𝕀
                             (ℕHomComp 𝕀 𝕁 (Hinitℕcenter 𝕀 𝕁 𝕀I)
                                           (Hinitℕcenter 𝕁 𝕀 𝕁I)) 𝕀I)) ,
                         sym (Hinitℕid-iden 𝕁
                             (ℕHomComp 𝕁 𝕀 (Hinitℕcenter 𝕁 𝕀 𝕁I)
                                           (Hinitℕcenter 𝕀 𝕁 𝕀I)) 𝕁I))

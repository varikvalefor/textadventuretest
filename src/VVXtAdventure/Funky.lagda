\documentclass{report}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb{N}}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb{Z}}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb{Q}}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_s}}}
\newunicodechar{ₜ}{\ensuremath{\mathnormal{_t}}}
\newunicodechar{ᵤ}{\ensuremath{\mathnormal{_u}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_i}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_o}}}
\newunicodechar{ₙ}{\ensuremath{\mathnormal{_n}}}
\newunicodechar{ᵘ}{\ensuremath{\mathnormal{^u}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}
\newunicodechar{≡}{\ensuremath{\mathnormal{\equiv}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\land}}}
\newunicodechar{≤}{\ensuremath{\mathnormal{\leq}}}
\newunicodechar{≥}{\ensuremath{\mathnormal{\geq}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^b}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{∸}{\ensuremath{\mathnormal{\divdot}}}
\newunicodechar{⍨}{\ensuremath{\mathnormal{\raisebox{-0.25ex}{$\ddot\sim$}}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal{\ell}}}
\newunicodechar{∋}{\ensuremath{\mathnormal{\ni}}}
\newunicodechar{∈}{\ensuremath{\mathnormal{\in}}}
\newunicodechar{∉}{\ensuremath{\mathnormal{\notin}}}
\newunicodechar{∎}{\ensuremath{\mathnormal{\blacksquare}}}
\newunicodechar{⟨}{\ensuremath{\mathnormal{\langle}}}
\newunicodechar{⟩}{\ensuremath{\mathnormal{\rangle}}}
\newunicodechar{𝔦}{\ensuremath{\mathnormal{mathfrak{i}}}}
\newunicodechar{𝔪}{\ensuremath{\mathnormal{\mathfrak{m}}}}
\newunicodechar{𝓁}{\ensuremath{\mathnormal{\mathcal{l}}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal{\ell}}}
\newunicodechar{⊃}{\ensuremath{\mathnormal{\supset}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\newcommand\cmene{VVXtAdventure.Funky}

\title{la'o zoi.\ \texttt{\cmene}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\begin{abstract}
	\noindent ni'o la'o zoi.\ \texttt{\cmene}\ .zoi.\ vasru le velcki be lo fancu be fi la'oi .\F{GameData}.\ ja zo'e
\end{abstract}

\section{le me'oi .preamble.\ ja co'e}

\begin{code}
{-# OPTIONS --safe #-}

module VVXtAdventure.Funky where

open import Data.Fin
  using (
    Fin;
    suc;
    toℕ;
    zero
  )
open import Data.Nat
  using (
    _∸_;
    _+_;
    ℕ
  )
open import Data.Sum
  using (
    [_,_];
    inj₁;
    inj₂;
    _⊎_
  )
open import Function
open import Data.Bool
  using (
    false;
    Bool;
    true
  )
  renaming (
    if_then_else_ to if
  )
open import Data.List
  using (
    intersperse;
    mapMaybe;
    allFin;
    List;
    _∷_;
    []
  )
  renaming (
    take to _↑_;
    drop to _↓_;
    lookup to _!_;
    filter to filterₗ
  )
open import Data.Maybe
  using (
    is-just;
    fromMaybe;
    maybe;
    Maybe;
    just;
    nothing
  )
open import Data.String
  using (
    String;
    concat
  )
open import Data.Product
  using (
    Σ;
    map₂;
    dmap;
    proj₁;
    proj₂;
    _×_;
    _,_
  )
open import Data.Rational
  using (
    0ℚ
  )
open import Relation.Unary
  using (
    Pred
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    no
  )
open import VVXtAdventure.Base
open import Truthbrary.Data.Fin
  using (
    tomindus;
    mindus;
    mink
  )
open import Truthbrary.Record.Eq
  using (
    _≡ᵇ_;
    _≟_;
    Eq
  )
open import Truthbrary.Record.LLC
  using (
    nu,iork;
    length;
    _++_;
    _∉_;
    map
  )
open import Truthbrary.Category.Monad
  using (
    _>>=_
  )
open import Truthbrary.Data.List.Loom
  using (
    ualmapkonk;
    ualkonk;
    ualmap;
    ual;
    lum
  )
open import Truthbrary.Category.Monad
  using (
  )
open import Truthbrary.Data.List.Loom
  using (
    mapimplant;
    ual
  )
open import Data.List.Relation.Unary.Any
  using (
    any?
  )
open import Relation.Binary.PropositionalEquality

import Data.Fin.Properties as DFP
import Data.Nat.Properties as DNP
import Data.List.Properties as DLP
import Data.Maybe.Properties as DMP

open ≡-Reasoning
\end{code}

\chapter{le mu'oi glibau.\ low-level .glibau.}
ni'o la'au le mu'oi glibau.\ low-level .glibau.\ li'u vasru le velcki be le fancu poi ke'a pruce ja co'e zo'e je lo ctaipe be la'oi .\F{GameData}.\ lo ctaipe be la'oi .\F{GameData}.\ je lo ctaipe be zo'e ja lo su'u dunli

\section{la'o zoi.\ \F{movePawn} .zoi.}
ni'o tu'a la'o zoi.\ \F{movePawn} \B q \B m \B n .zoi.\ .indika lo du'u lo selsni be la'o zoi.\ \AgdaField{GameData.haters} \B q \OpF !\ \B h .zoi.\ cu zvati ko'a goi lo selsni be la'o zoi.\ \AgdaField{GameData.rooms} \B q) \OpF !\ \B n .zoi.

\begin{code}
movePawn : (q : GameData)
         → (i : Fin $ length $ GameData.haters q)
         → (j : Fin $ length $ GameData.rooms q)
         → let 𝓁 = length in
           let x = GameData.haters in
           let k = Character.room in
           let gek = GameData.rooms in
           Σ GameData $ λ q'
           → Σ (𝓁 (gek q) ≡ 𝓁 (gek q')) $ λ ℓ
           → Σ (𝓁 (x q) ≡ 𝓁 (x q')) $ λ ℓ₂
           → let uil = ual (x q) i $ λ x → record x {room = j} in
             (j ≡ mink (k $ x q' ! mink i ℓ₂) (sym ℓ))
             -- | .i xu ti ronsa
           × let uil₂ = proj₁ $ proj₂ uil in
             (_≡_
               q'
               record q {
                 haters = proj₁ uil;
                 player' = mink (GameData.player' q) uil₂
                 })
movePawn gd h r = gd' , refl , proj₁ (proj₂ xat) , rudus , refl
  where
  xat = ual (GameData.haters gd) h $ λ x → record x {room = r}
  player'' = mink (GameData.player' gd) $ proj₁ $ proj₂ xat
  rudus = sym $ cong Character.room $ proj₂ $ proj₂ xat
  gd' = record gd {haters = proj₁ xat; player' = player''}
\end{code}
 
\section{la'o zoi.\ \F{wieldPawn}\ .zoi.}
ni'o tu'a la'o zoi.\ \F{wieldPawn} \B q \B m \B n \AgdaInductiveConstructor{refl}\ .zoi.\ .indika lo du'u zo'e ja lo selsni be la'o zoi.\ \AgdaField{GameData.haters} \B q \OpF !\ \B m .zoi.\ cu me'oi .wield.\ lo selsni be la'o zoi.\ \AgdaField{Character.inventory} \Sym(\AgdaField{GameData.haters} \B q \OpF !\ \B m\Sym) \OpF !\ \B n .zoi.

\begin{code}
wieldPawn : (q : GameData)
          → let x = GameData.haters in
            let 𝓁 = length in
            let iv = Character.inventory in
            let ifinc = GameData.yourfloorisnowclean in
            (j : Fin $ 𝓁 $ x q)
          → (i : Fin $ 𝓁 $ iv $ x q ! j)
          → (_≡_ true $ is-just $ Item.weapwn $ iv (x q ! j) ! i)
          → Σ GameData $ λ q'
            → Σ (𝓁 (x q) ≡ 𝓁 (x q')) $ λ ℓ
            → Σ (iv (x q ! j) ≡ iv (x q' ! mink j ℓ)) $ λ ℓ₂
            → Σ ((_≡_ on GameData.rooms) q q') $ λ rud
            → (_≡_
                (just $ toℕ i)
                (Data.Maybe.map
                  (toℕ ∘ proj₁)
                  (Character.wieldedct $ x q' ! mink j ℓ)))
            × (_≡_
                q'
                (record q {
                   rooms = GameData.rooms q';
                   haters = GameData.haters q';
                   player' = mink (GameData.player' q) ℓ;
                   yourfloorisnowclean = ifinc q'}))
            × (_≡_
                (_++_
                  (toℕ j ↑ x q)
                  (ℕ.suc (toℕ j) ↓ x q))
                (subst
                  (List ∘ Character)
                  (sym rud)
                  (_++_
                    (toℕ j ↑ x q')
                    (ℕ.suc (toℕ j) ↓ x q'))))
wieldPawn gd j i t = gd' , xenlen , xendj , refl , sym uidus , refl , skrud
  where
  ⊃ = Data.List.head
  𝓁 = length

  xen = GameData.haters gd
  x₁ = toℕ j ↑ xen
  x₂ = record (xen ! j) {wieldedct = just $ i , t}
  x₃ = ℕ.suc (toℕ j) ↓ xen
  xen' = x₁ ++ x₂ ∷ x₃

  dropkat : ∀ {a} → {A : Set a}
          → (xs ys : List A)
          → ys ≡ 𝓁 xs ↓ (xs ++ ys)
  dropkat [] _ = refl
  dropkat (_ ∷ xs) = dropkat xs

  xenlen = begin
    𝓁 xen ≡⟨ cong 𝓁 $ sym $ DLP.take++drop (toℕ j) xen ⟩
    𝓁 (x₁ ++ d₂) ≡⟨ DLP.length-++ x₁ ⟩
    𝓁 x₁ + 𝓁 d₂ ≡⟨ cong (𝓁 x₁ +_) $ DLP.length-drop (toℕ j) xen ⟩
    𝓁 x₁ + (𝓁 xen ∸ toℕ j) ≡⟨ cong (𝓁 x₁ +_) $ sym xex ⟩
    𝓁 x₁ + ℕ.suc (𝓁 x₃) ≡⟨ sym $ DLP.length-++ x₁ ⟩
    𝓁 xen' ∎
    where
    d₂ = toℕ j ↓ xen
    xex = begin
      ℕ.suc (𝓁 x₃) ≡⟨ refl ⟩
      𝓁 (x₂ ∷ x₃) ≡⟨ refl ⟩
      ℕ.suc (𝓁 $ ℕ.suc (toℕ j) ↓ xen) ≡⟨ dropsuc xen j ⟩
      𝓁 (toℕ j ↓ xen) ≡⟨ DLP.length-drop (toℕ j) xen ⟩
      𝓁 xen ∸ toℕ j ∎
      where
      dropsuc : ∀ {a} → {A : Set a}
              → (x : List A)
              → (n : Fin $ 𝓁 x)
              → let n' = toℕ n in
                ℕ.suc (𝓁 $ ℕ.suc n' ↓ x) ≡ 𝓁 (n' ↓ x)
      dropsuc (_ ∷ _) zero = refl
      dropsuc (_ ∷ xs) (suc n) = dropsuc xs n

  xent : ⊃ (𝓁 x₁ ↓ xen') ≡ just (xen' ! mink j xenlen)
  xent = sym $ subkon $ dropind xen' $ mink j xenlen
    where
    _≤_ = Data.Nat._≤_
    dropind : ∀ {a} → {A : Set a}
            → (xs : List A)
            → (n : Fin $ 𝓁 xs)
            → just (xs ! n) ≡ ⊃ (toℕ n ↓ xs)
    dropind (_ ∷ _) zero = refl
    dropind (_ ∷ xs) (suc n) = dropind xs n
    jelis : toℕ j ≤ 𝓁 xen
    jelis = subst₂ _≤_ mijd kix $ DNP.≤-step j'
      where
      lisuc : ∀ {a} → {A : Set a}
            → (xs : List A)
            → Fin $ 𝓁 xs
            → Σ ℕ $ _≡_ (𝓁 xs) ∘ ℕ.suc
      lisuc (_ ∷ xs) _ = 𝓁 xs , refl
      j' = DFP.≤fromℕ $ mink j $ proj₂ $ lisuc xen j
      mijd = sym $ tomindus j $ proj₂ $ lisuc xen j
      kix : ℕ.suc (toℕ $ Data.Fin.fromℕ _) ≡ 𝓁 xen
      kix = tondus $ sym $ proj₂ $ lisuc xen j
        where
        tondus : {m n : ℕ}
               → m ≡ n
               → toℕ (Data.Fin.fromℕ m) ≡ n
        tondus x = subst (_≡_ _) x $ DFP.toℕ-fromℕ _
    xil = begin
      toℕ (mink j xenlen) ≡⟨ sym $ tomindus j xenlen ⟩
      toℕ j ≡⟨ teiklendus xen (toℕ j) jelis ⟩
      𝓁 x₁ ∎
      where
      teiklendus : ∀ {a} → {A : Set a}
                 → (xs : List A)
                 → (n : ℕ)
                 → n ≤ 𝓁 xs
                 → n ≡ 𝓁 (n ↑ xs)
      teiklendus _ 0 _ = refl
      teiklendus (_ ∷ xs) (ℕ.suc n) (Data.Nat.s≤s q) = ret
        where
        ret = cong ℕ.suc $ teiklendus xs n q
    subkon = subst (_≡_ _) $ cong (⊃ ∘ _↓ xen') xil

  xendj : let iv = Character.inventory in
          iv (xen ! j) ≡ iv (xen' ! mink j xenlen)
  xendj = DMP.just-injective x₂d
    where
    iv = Character.inventory
    x₂d = begin
      just (iv $ xen ! j) ≡⟨ refl ⟩
      just (iv x₂) ≡⟨ refl ⟩
      mapₘ iv (⊃ $ x₂ ∷ x₃) ≡⟨ cong (mapₘ iv ∘ ⊃) $ dropkat x₁ _ ⟩
      mapₘ iv (⊃ $ 𝓁 x₁ ↓ xen') ≡⟨ cong (mapₘ iv) xent ⟩
      just (iv $ xen' ! mink j xenlen) ∎
      where
      mapₘ = Data.Maybe.map

  uidus = cong u₁ $ sym $ DMP.just-injective $ begin
    just x₂ ≡⟨ refl ⟩
    ⊃ (x₂ ∷ x₃) ≡⟨ cong ⊃ $ dropkat x₁ $ x₂ ∷ x₃ ⟩
    ⊃ (𝓁 x₁ ↓ xen') ≡⟨ xent ⟩
    just (xen' ! mink j xenlen) ∎
    where
    u₁ = Data.Maybe.map (toℕ ∘ proj₁) ∘ Character.wieldedct

  -- | ni'o zo .kond. binxo ja co'e zo .skrud.
  skrud = begin
    (toℕ j ↑ xen) ++ (ℕ.suc (toℕ j) ↓ xen) ≡⟨ refl ⟩
    x₁ ++ x₃ ≡⟨ cong (_++ x₃) $ takedus xen j ⟩
    x₁' ++ x₃ ≡⟨ cong (_++_ x₁') $ dropydus xen (x₂ ∷ x₃) j ⟩
    x₁' ++ x₃' ∎
    where
    x₁' = toℕ j ↑ xen'
    x₃' = ℕ.suc (toℕ j) ↓ xen'
    takedus : ∀ {a} → {A : Set a}
            → (a : List A)
            → {b : List A}
            → (n : Fin $ 𝓁 a)
            → let n' = toℕ n in
              n' ↑ a ≡ n' ↑ (_++ b $ n' ↑ a)
    takedus (_ ∷ xs) zero = refl
    takedus (x ∷ xs) (suc n) = cong (_∷_ x) $ takedus xs n
    dropydus : ∀ {a} → {A : Set a}
             → (a b : List A)
             → {x : A}
             → (n : Fin $ 𝓁 a)
             → let n' = toℕ n in
               let s = ℕ.suc n' in
               s ↓ a ≡ s ↓ _++_ (n' ↑ a) (x ∷ s ↓ a)
    dropydus (_ ∷ _) _ zero = refl
    dropydus (_ ∷ xs) b (suc n) = dropydus xs b n

  gd' = record gd {haters = xen'; player' = p'}
    where
    p' = mink (GameData.player' gd) xenlen
\end{code}

\section{la'o zoi.\ \F{takePawn}\ .zoi.}
ni'o tu'a la'o zoi.\ \F{takePawn} \B q \B m \B n .zoi.\ cu .indika lo du'u zo'e ja lo me'oi .inventory.\ be lo selsni be la'o zoi.\ \F{GameData.haters} \B q \OpF !\ \B m\ .zoi.\ cu vasru zo'e ja lo selsni be la'o zoi.\ \Sym(\F{GameData.itemsInRoomOf} \B q \B m\Sym) \F !\ n\ .zoi... kei je zo'e

ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu la .varik.\ cu ciksi le me'oi .\AgdaKeyword{private}.\ bau la .lojban.

\begin{code}
private
  _⍨ = flip

  kumfybi'o : (q q' : GameData)
            → let rooms = GameData.rooms in
              length (rooms q) ≡ length (rooms q')
            → Character $ rooms q
            → Character $ rooms q'
  kumfybi'o _ _ g x = record {
    room = mink (Character.room x) g;
    forename = Character.forename x;
    surname = Character.surname x;
    cname = Character.cname x;
    nicknames = Character.nicknames x;
    inventory = Character.inventory x;
    health = Character.health x;
    wieldedct =  Character.wieldedct x;
    yourfloorisnowclean = Character.yourfloorisnowclean x}

takePawn : (q : GameData)
         → (m : Fin $ length $ GameData.haters q)
         → (n : Fin $ length $ GameData.itemsInRoomOf q m)
         → Σ GameData $ λ q'
           → Σ ((_≡_ on length ∘ GameData.rooms) q q') $ λ r
           → Σ ((_≡_ on length ∘ GameData.haters) q q') $ λ x
           → let xen = GameData.haters in
             let room = Character.room in
             (Σ (Character $ GameData.rooms q') $ λ k
              → ((_≡_ ⍨)
                  (xen q')
                  (Data.List.map
                    (kumfybi'o q q' r)
                    (_++_
                      (toℕ m ↑ xen q)
                      (_∷_
                        (kumfybi'o q' q (sym r) k)
                        (ℕ.suc (toℕ m) ↓ xen q))))))
           × (Σ Room $ λ r'
              → let kit = toℕ $ room $ xen q ! m in
                (_≡_
                  (GameData.rooms q')
                  (_++_
                    (kit ↑ GameData.rooms q)
                    (r' ∷ ℕ.suc kit ↓ GameData.rooms q))))
           × let iofink = GameData.yourfloorisnowclean in
             (_≡_
               q'
               record q {
                 rooms = GameData.rooms q';
                 haters = GameData.haters q';
                 player' = mink (GameData.player' q) x;
                 yourfloorisnowclean = iofink q'})
           × (_≡_
               (GameData.inventOf q' $ mink m x)
               ((_∷_ ⍨)
                 (GameData.inventOf q m)
                 (GameData.itemsInRoomOf q m ! n)))
takePawn q m n = q' , dus , dis , xendus , kumdus , refl , nyfin
  where
  lb = GameData.haters q ! m
  sl = Room.items (GameData.rooms q ! Character.room lb) ! n
  vimcu = λ x → record x {items = filterₗ nadu $ Room.items x}
    where
    nadu = _≟_ false ∘ _≡ᵇ_ (Item.cname sl) ∘ Item.cname
  k'' : Σ (List Room) $ λ l
        → Σ (length (GameData.rooms q) ≡ length l) _
  k'' = ual (GameData.rooms q) (Character.room lb) vimcu
  k' = proj₁ k''
  kumbi'o = λ x → record {
    forename = Character.forename x;
    surname = Character.surname x;
    cname = Character.cname x;
    nicknames = Character.nicknames x;
    room = mink (Character.room x) $ proj₁ $ proj₂ k'';
    inventory = Character.inventory x;
    wieldedct = Character.wieldedct x;
    yourfloorisnowclean = Character.yourfloorisnowclean x
    }
  lb! : Character k' → Character k'
  lb! x = record x {
    inventory = sl ∷ Character.inventory x;
    wieldedct = Data.Maybe.map (dmap suc id) $ Character.wieldedct x;
    yourfloorisnowclean = iofink
    }
    where
    iofink = f i (Item.cname sl) n₁ {!!}
      where
      n₁ = Character.yourfloorisnowclean x
      i = Data.List.map Item.cname $ Character.inventory x
      f : ∀ {a} → {A : Set a}
        → ⦃ _ : Eq A ⦄
        → (x : List A)
        → (s : A)
        → nu,iork x
        → s ∉ x
        → nu,iork $ s ∷ x
      f x s n nin = {!!}
  x'' : Σ (List $ Character k') $ λ x'
        → Σ (length (GameData.haters q) ≡ length x') _
  x'' = ualmap (GameData.haters q) kumbi'o lb! m
  q' = record {
    epicwin = GameData.epicwin q;
    rooms = k';
    haters = proj₁ x'';
    yourfloorisnowclean = subst nu,iork entydut iofink;
    player' = mink (GameData.player' q) $ proj₁ $ proj₂ x''
    }
    where
    iofink = GameData.yourfloorisnowclean q
    mapₗ = Data.List.map
    k = GameData.rooms q
    entydut = begin
      mapₗ cname k ≡⟨ madek k libek cname ⟩
      konk b₁ (cname kₗ) b₂ ≡⟨ cong (flip (konk b₁) b₂) entydus ⟩
      konk b₁ (cname kₗ') b₂ ≡⟨ cong konk₁ $ ualteikym k libek vimcu ⟩
      konk b₁' (cname kₗ') b₂ ≡⟨ cong konk₂ $ ualdropym k libek vimcu ⟩
      konk b₁' (cname kₗ') b₂' ≡⟨ sym $ madek k' libek' cname ⟩
      mapₗ cname k' ∎
      where
      cname = Room.cname
      libek = Character.room lb
      libek' = mink libek $ proj₁ $ proj₂ k''
      kₗ = k ! libek
      kₗ' = k' ! libek'
      b₁ = mapₗ cname $ toℕ libek ↑ k
      b₂ = mapₗ cname $ ℕ.suc (toℕ libek) ↓ k
      b₁' = mapₗ cname $ toℕ libek' ↑ k'
      b₂' = mapₗ cname $ ℕ.suc (toℕ libek') ↓ k'
      konk : ∀ {a} → {A : Set a}
           → List A → A → List A → List A
      konk a = _++_ a ∘₂ _∷_
      konk₁ = λ b1 → konk (mapₗ cname b1) (cname kₗ') b₂
      konk₂ = konk b₁' (cname kₗ') ∘ mapₗ cname
      entydus : cname kₗ ≡ cname kₗ'
      entydus = sym $ cong cname $ proj₂ $ proj₂ k''
      madek : ∀ {a b} → {A : Set a} → {B : Set b}
            → (x : List A)
            → (n : Fin $ length x)
            → (f : A → B)
            → (_≡_
                (mapₗ f x)
                (_++_
                  (mapₗ f $ toℕ n ↑ x)
                  (_∷_
                    (f $ x ! n)
                    (mapₗ f $ (ℕ.suc $ toℕ n) ↓ x))))
      madek (_ ∷ _) zero _ = refl
      madek (x ∷ xs) (suc n) f = cong (_∷_ $ f x) $ madek xs n f
      ualteikym : ∀ {a} → {A : Set a}
                → (x : List A)
                → (n : Fin $ length x)
                → (f : A → A)
                → let u = ual x n f in
                  (_≡_
                    (toℕ n ↑ x)
                    (toℕ (mink n $ proj₁ $ proj₂ u) ↑ proj₁ u))
      ualteikym x n f = subst (_≡_ _) kong utz
        where
        kong = cong (flip _↑_ $ proj₁ u) $ tomindus n u₂
          where
          u = ual x n f
          u₂ = proj₁ $ proj₂ u
        utz = Truthbrary.Data.List.Loom.ualteik x n f
      ualdropym : ∀ {a} → {A : Set a}
                → (x : List A)
                → (n : Fin $ length x)
                → (f : A → A)
                → let n' = mink n $ proj₁ $ proj₂ $ ual x n f in
                  (_≡_
                    (ℕ.suc (toℕ n) ↓ x)
                    (ℕ.suc (toℕ n') ↓ proj₁ (ual x n f)))
      ualdropym (_ ∷ _) zero _ = refl
      ualdropym (x ∷ xs) (suc n) f = subst (_≡_ _) c ud
        where
        u = ual xs n f
        c = cong (flip _↓_ $ proj₁ u) $ tomindus (suc n) uresuk
          where
          uresuk = cong ℕ.suc $ proj₁ $ proj₂ u
        ud = Truthbrary.Data.List.Loom.ualdrop (x ∷ xs) (suc n) f

  dus = proj₁ $ proj₂ k''
  dis = proj₁ $ proj₂ x''

  nyfin = sym $ cong Character.inventory $ proj₂ $ proj₂ x''

  kumdus = xenku'a , ualkonk kumste (Character.room lb) vimcu
    where
    kumste = GameData.rooms q
    xenku'a = vimcu $ kumste ! Character.room lb

  xendus = lb! (kumbi'o lb) , kibyduxen
    where
    xen = GameData.haters q
    xen' = GameData.haters q'
    kibyduxen = begin
      kib ¨ (konk xenim likil' xensim) ≡⟨ mapinj xenim xensim kib ⟩
      konk xenkim (kib likil') xenksim ≡⟨ midkonklikil  ⟩
      konk xenkim likil xenksim ≡⟨ refl ⟩
      klonk xenkim xenksim ≡⟨ sym $ mapimplant xen likil kib m ⟩
      klonk xenim' xensim' ≡⟨ cong (flip _++_ _) xenteik ⟩
      klonk (m:ℕ ↑ xen') xensim' ≡⟨ cong (klonk $ m:ℕ ↑ xen') xendrop ⟩
      klonk (m:ℕ ↑ xen') (ℕ.suc m:ℕ ↓ xen') ≡⟨ refl ⟩
      konk _ likil _ ≡⟨ cong (flip (konk _) _) $ proj₂ $ proj₂ x'' ⟩
      konk (m:ℕ ↑ xen') (xen' ! m'') (ℕ.suc m:ℕ ↓ xen') ≡⟨ refl ⟩
      koxonk (m:ℕ ↑ xen') (ℕ.suc m:ℕ ↓ xen') ≡⟨ koxonkdus ⟩
      koxonk (m'':ℕ ↑ xen') (ℕ.suc m'':ℕ ↓ xen') ≡⟨ xokonkyxen ⟩
      xen' ∎
      where
      _¨_ = Data.List.map
      likil = lb! $ kumbi'o lb
      likil' = kumfybi'o q' q (sym dus) likil
      konk : ∀ {a} → {A : Set a}
           → List A → A → List A → List A
      konk a b c = a ++ (b ∷ c)
      klonk = flip konk likil
      koxonk = flip konk $ xen' ! mink m dis
      kib = kumfybi'o q q' dus
      m:ℕ = toℕ m
      m' = mink m $ sym $ DLP.length-map kumbi'o xen
      m'' = mink m dis
      m'':ℕ = toℕ m''
      xenim = m:ℕ ↑ xen
      xensim = ℕ.suc m:ℕ ↓ xen
      xenkim = kib ¨ xenim
      xenksim = kib ¨ xensim
      xenbis = kumbi'o ¨ xen
      xenim' = m:ℕ ↑ xenbis
      xensim' = ℕ.suc m:ℕ ↓ xenbis
      koxonkdus : (_≡_
                    (koxonk (m:ℕ ↑ xen') (ℕ.suc m:ℕ ↓ xen'))
                    (koxonk (m'':ℕ ↑ xen') (ℕ.suc m'':ℕ ↓ xen')))
      koxonkdus = cong f $ tomindus m dis
        where
        f = λ a → koxonk (a ↑ xen') (ℕ.suc a ↓ xen')
      midkonklikil : (_≡_
                       (konk xenkim (kib likil') xenksim)
                       (konk xenkim likil xenksim))
      midkonklikil = cong (flip (konk xenkim) xenksim) midju
        where
        room = Character.room
        cninykumfa = λ n → record likil {room = n}
        midju : kib likil' ≡ likil
        midju = cong cninykumfa $ mindus (room likil) (sym dus) dus
      m≡m' : toℕ m ≡ toℕ m'
      m≡m' = tomindus m $ sym $ DLP.length-map kumbi'o xen
      xenteik = begin
        xenim' ≡⟨ refl ⟩
        toℕ m ↑ xenbis ≡⟨ cong (flip _↑_ xenbis) m≡m' ⟩
        toℕ m' ↑ xenbis ≡⟨ ualteik xenbis m' lb! ⟩
        toℕ m' ↑ (proj₁ $ ual xenbis m' lb!) ≡⟨ refl ⟩
        toℕ m' ↑ xen' ≡⟨ cong (flip _↑_ xen') $ sym m≡m' ⟩
        toℕ m ↑ xen' ∎
        where
        ualteik = Truthbrary.Data.List.Loom.ualteik
      xendrop = begin
        xensim' ≡⟨ refl ⟩
        ℕ.suc (toℕ m) ↓ xenbis ≡⟨ cong (zunbas xenbis) m≡m' ⟩
        ℕ.suc (toℕ m') ↓ xenbis ≡⟨ ualdrop xenbis m' lb! ⟩
        ℕ.suc (toℕ m') ↓ (proj₁ $ ual xenbis m' lb!) ≡⟨ refl ⟩
        ℕ.suc (toℕ m') ↓ xen' ≡⟨ cong (zunbas xen') $ sym m≡m' ⟩
        ℕ.suc (toℕ m) ↓ xen' ∎
        where
        -- | .i zo .zunbas. cmavlaka'i lu zunle basti
        -- li'u ja zo'e
        zunbas = λ a → flip _↓_ a ∘ ℕ.suc
        ualdrop = Truthbrary.Data.List.Loom.ualdrop
      mapinj : ∀ {a b} → {A : Set a} → {B : Set b}
             → (xs ys : List A)
             → {x : A}
             → (f : A → B)
             → (_≡_
                 (f ¨ (xs ++ x ∷ ys))
                 (f ¨ xs ++ f x ∷ f ¨ ys))
      mapinj [] _ _ = refl
      mapinj (x ∷ xs) ys f = cong (_∷_ $ f x) $ mapinj xs ys f
      xokonkyxen = sym $ konkdus xen' m''
        where
        konkdus : ∀ {a} → {A : Set a}
                → (x : List A)
                → (n : Fin $ length x)
                → let n' = toℕ n in
                  (_≡_
                    x
                    (_++_
                      (n' ↑ x)
                      (_∷_
                        (x ! n)
                        (ℕ.suc n' ↓ x))))
        konkdus (_ ∷ _) zero = refl
        konkdus (x ∷ z) (suc n) = cong (_∷_ x) $ konkdus z n
\end{code}

\chapter{le mu'oi glibau.\ high-level .glibau.}

\section{le fancu poi ke'a pruce ja co'e zo'e je ko'a goi lo ctaipe be la'oi .GameData.\ ko'a je zo'e}

\subsection{la'oi .\F{epicwin?}.}
ni'o ga jonai la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'a goi la'o zoi.\ \F{epicwin?} \B m \B a .zoi.\ gi ga je tu'a la'o zoi.\ \B a .zoi.\ .indika lo du'u lo kelci cu jinga gi ko'a du la'o zoi.\ \AgdaInductiveConstructor{just} \OpF \$ \B m \OpF , \B a .zoi.

\begin{code}
epicwin? : String → GameData → COut
epicwin? m g = if (GameData.epicwin g) (just $ m , g) nothing
\end{code}

\subsection{la'oi .\F{inspect?}.}
ni'o ga jonai ga je ga je la'oi .\F{inspect?}.\ djuno pe'a ru'e lo du'u tu'a la'o zoi.\ \B a .zoi.\ .indika lo du'u djica lo nu skicu la'o zoi.\ B b .zoi.\ gi cumki fa lo nu skicu la'o zoi.\ \B b .zoi.\ gi
\begin{itemize}
	\item ga je la'o zoi.\ \B q .zoi.\ velski la'o zoi.\ \B b .zoi.\ gi ko'a goi la'o zoi.\ \F{inspect?} \B a \B{godDamn} .zoi.\ du la'o zoi.\ \AgdaInductiveConstructor{just} \OpF \$ \B q \OpF , \B{godDamn} .zoi.\ gi
	\item ga jonai ga je la'oi .\F{inspect?}.\ djuno pe'a ru'e lo du'u la'o zoi.\ \B a .zoi.\ mabla gi\ldots
	\begin{itemize}
		\item ga je la'o zoi.\ \B i .zoi.\ te skuxai gi ko'a du la'o zoi.\ \AgdaInductiveConstructor{just} \OpF \$ \B i \OpF , \B{godDamn} .zoi.\ gi
		\item ko'a du la'oi .\AgdaInductiveConstructor{nothing}.
	\end{itemize}
\end{itemize}

\begin{code}
inspect? : Com
inspect? (c ∷ f) dang = if methch (getDown f) nothing
  where
  methch = c ≡ᵇ "INSPECT"
  getDown : List String → COut
  getDown (_ ∷ _ ∷ _) = just $ m , dang
    where
    m = "I can't handle any more of your inane \
        \gibberish.\n\
        \If you want to search for multiple things, \
        \then individually state the shortnames of \
        \the things.\n\
        \Alternatively, you might have tried to \
        \search for a cname which contains \
        \multiple spaces.  But illegal is that a \
        \cname contains multiple spaces.\
        \Do it $n$ more times, and I will send the \
        \police to your doorstep.  I'm trying to \
        \help you, but you're really testing my \
        \patience now."
  getDown [] = just $ m , dang
    where
    m = "nothing : ∀ {a} → {A : Set a} → Maybe A"
  getDown (n ∷ []) with filterₗ (_≟_ n ∘ Item.cname) inv
    where
    inv = Character.inventory $ GameData.player dang
  ... | [] = just $ "I'm not seeing it." , dang
  ... | (q ∷ []) = just $ Item.hlDescr q , dang
  ... | (_ ∷ _ ∷ _) = just $ m , dang
    where
    m = "You're going to have to be more specific.  \
        \Sure, I could choose some arbitrary matching \
        \item, but that would probably piss you off, \
        \and I'm already insulting you right and left."
inspect? [] _ = nothing
\end{code}

\subsection{la'oi .\F{invent?}.}
ni'o ga jonai la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'e goi la'o zoi.\ \F{invent?} \B \B g\ .zoi.\ gi ga je tu'a la'o zoi.\ \B m\ .zoi.\ .indika lo du'u lo kelci cu djica lo nu skicu lo selvau be ko'a goi lo me'oi .inventory.\ be lo kelci ke xarpre ja co'e gi ga je la'o zoi.\ \B s\ .zoi.\ vasru lo velski be lo ro selvau be ko'a gi ko'e du la'o zoi.\ \AgdaInductiveConstructor{just} \OpF \$ \B s \OpF , \B g .zoi.

\begin{code}
invent? : Com
invent? ("LIST" ∷ "INVENTORY" ∷ []) g = just $ desks , g
  where
  desks = concat $ intersperse "\n\n" $ map desk items
    where
    items = Character.inventory $ GameData.player g
    desk = λ a → Item.cname a ++ ": " ++ Item.hlDescr a
invent? _ _ = nothing
\end{code}

\subsection{la'oi .\F{kumski?}.}

ni'o ga jonai la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'e goi la'o zoi.\ \F{kumski?} \B a \B b\ .zoi.\ gi ga je la'o zoi.\ \B v .zoi.\ vasru lo velcki be ko'a gi ga je ko'e du la'o zoi.\ \AgdaInductiveConstructor{just} \OpF \$ \B v \OpF , \B b\ .zoi.\ gi la'oi .\F{kumski?}.\ djuno pe'a ru'e lo du'u tu'a la'o zoi.\ \B a .zoi.\ .indika lo du'u lo kelci cu djica lo nu tcidu ko'a goi lo velski be lo selvau be lo kumfa poi la'o zoi.\ \B b\ .zoi.\ .indika lo du'u ke'a zasti

\begin{code}
kumski? : Com
kumski? m g = if mapti (just $ le'i-velski , g) nothing
  where
  mapti = _↑_ 3 m ≡ᵇ ("LOOK" ∷ "AROUND" ∷ "YOU" ∷ [])
  le'i-velski = concatₛ $ intersperse "\n\n" le'i-lerpinsle
    where
    kumfa = GameData.rooms g ! Character.room (GameData.player g)
    concatₛ = Data.String.concat
    le'i-lerpinsle = jaiv ∷ map velski (Room.items kumfa)
      where
      velski : Item → String
      velski z with filterₗ methch $ Item.rmDescr z
        where
        methch = _≟_ (Room.cname kumfa) ∘ proj₁
      ... | [] = Item.cname z ++ ": " ++ Item.dfDescr z
      ... | (x ∷ _) = Item.cname z ++ ": " ++ proj₂ x
      jaiv : String
      jaiv with Room.travis kumfa
      ... | [] = "This room is completely isolated.  GFL."
      ... | x@(_ ∷ _) = "CONNECTED ROOMS: " ++ concatₛ liste
        where
        liste = intersperse ", " x
\end{code}

\subsection{la'oi .\F{scream?}.}
ni'o ga jonai ga je la'oi .\F{scream?}.\ djuno pe'a ru'e lo du'u tu'a la'o zoi.\ \B a .zoi.\ .indika lo du'u lo kelci cu djica lo nu krixa fa ko'a goi lo krixa ke xarpre ja co'e po la'o zoi.\ \B b .zoi.\ gi ga je tu'a la'o zoi.\ \B c .zoi.\ .indika lo du'u ko'a krixa gi ko'e goi la'o zoi.\ \F{scream?} \B a \B b .zoi.\ du la'o zoi.\ \AgdaInductiveConstructor{just} \OpF \$ c \OpF , b .zoi.\ gi ko'e du la'oi .\AgdaInductiveConstructor{nothing}.

\begin{code}
scream? : Com
scream? ("SCREAM" ∷ []) = just ∘ _,_ "AARGH!!!"
scream? _ _ = nothing
\end{code}

\subsection{la'oi .\F{sayless?}.}
ni'o ga jonai la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'a goi la'o zoi.\ \F{sayless?} \B a \B b .zoi.\ gi ga je co'e gi la'o zoi.\ \B a .zoi.\ kunti gi ga je tu'a la'o zoi.\ \B c .zoi.\ .indika le du'u mabla fa lo nu samci'a lo kunti ja zo'e gi ko'a du la'o zoi.\ \AgdaInductiveConstructor{just} \OpF \$ \B c \OpF , \B b .zoi.

\begin{code}
sayless? : List String → GameData → COut
sayless? [] = just ∘ _,_ "The silent treatment won't work here."
sayless? ("" ∷ "" ∷ "" ∷ "" ∷ []) = just ∘ _,_ m
  where
  m = "Man, what the fuck?"
sayless? _ _ = nothing
\end{code}

\subsection{la'oi .\F{lp?}.}
ni'o ga jonai la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'a goi la'o zoi.\ \F{lp?} \B a \B b .zoi.\ gi ga je ga je la'o zoi.\ \B c .zoi.\ na vajni gi ko'a du la'o zoi.\ \AgdaInductiveConstructor{nothing} \B c \B b .zoi.

\begin{code}
lp? : Com
lp? ("WHO" ∷ "ARE" ∷ "YOU?" ∷ []) = just ∘ _,_ m
  where
  m = "I really want to know."
lp? ("I'M" ∷ "A" ∷ "WINNER" ∷ []) q = just $ m , q
  where
  m = if (GameData.epicwin q) m₁ m₂
    where
    m₁ = "I just can't argue with that."
    m₂ = "Actually, refl is a proof of GameData.epicwin \
         \q ≡ false.  You have not won The Game.\n\n\
         \You were probably expecting something else."
lp? _ _ = nothing
\end{code}

\section{le fancu poi cumki fa lo nu ke'a pruce ja co'e zo'e je ko'a goi lo ctaipe be la'oi .GameData.\ zo'e je lo na du be ko'a}
ni'o la .varik.\ cu jinvi le du'u zabna fa le su'u cmene ko'a goi la'u le fancu poi cumki fa lo nu ke'a pruce ja co'e zo'e je ko'a goi lo ctaipe be la'oi .GameData.\ zo'e je lo na du be ko'a li'u kei kei je le du'u tu'a ko'a filri'a lo nu jimpe fi ko'e goi le se cmene be ko'a  .i ku'i ga naja na jimpe fi ko'e gi cumki fa lo nu filri'a lo nu jimpe fi ko'e kei fa tu'a le se du'u ko'e vasru le velcki be le fancu poi lo nu zabna fa lo se pruce be ke'a cu se cumki lo nu tu'a lo te pruce ja co'e be ke'a cu .indika lo na se .indika tu'a lo se pruce be ke'a

\subsection{la'oi .\F{travel?}.}
ni'o ga jonai ga je la'o zoi.\ \F{travel?} .zoi.\ djuno ja co'e lo du'u tu'a ko'a goi zoi zoi.\ \F{travel?} \B r \B g .zoi.\ cu nu cpedu lo nu ko'e goi lo kelci ke xarpre ja co'e cu klama lo kumfa poi la'o zoi.\ \B K .zoi.\ sinxa ke'a gi\ldots
\begin{itemize}
	\item ga jonai ga je la'o zoi.\ \AgdaField{Room.travis} \OpF \$ \AgdaField{Character.room} \OpF \$ \AgdaField{GameData.player} \B g .zoi.\ vasru lo mu'oi glibau.\ \AgdaField{Room.cname}\ .glibau.\ be la'o zoi.\ \B K .zoi.\ gi\ldots
	\begin{itemize}
		\item ko'a du lo me'oi .product.\ be lo velski be lo nu klama bei zo'e poi tu'a ke'a .indika lo du'u ko'e zvati zo'e poi djica lo nu zvati ke'a xi re gi
		\item ko'a me'oi .product.\ lo te skuxai ja zo'e la'o zoi.\ \B g .zoi.
	\end{itemize}
	\item gi ko'a du la'oi .\AgdaInductiveConstructor{nothing}.
\end{itemize}

\begin{code}
travel? : Com
travel? [] _ = nothing
travel? (x₁ ∷ xs₁) = if realShit (travel' xs₁) $ const nothing
  where
  realShit = x₁ ≡ᵇ "TRAVEL"
  travel' : Com
  travel' [] = just ∘ _,_ m
    where
    m = "Don't tell me to break the rules, fucker!"
  travel' (_ ∷ _ ∷ _) = just ∘ _,_ m
    where
    m = "I strongly doubt that the concept of \"super\
        \position\" applies to a creature of your mass."
  travel' (cname ∷ []) q = maybe just faktoi $ alreadythere?
    where
    F = Fin $ length $ GameData.rooms q
    cur = GameData.rooms q ! Character.room (GameData.player q)
    alreadythere? = if atRoom (just $ m , q) nothing
      where
      atRoom = cname ≡ᵇ Room.cname cur
      m = "Damn, that's some fast travel.  \
          \You're already there!"
    faktoi = [_,_] (just ∘ (_, q)) iusyf mathch
      where
      -- | We'll just have to live with that possibility.
      iusyf = maybe youse fail ∘ Data.List.head
        where
        fail = just $ m , q
          where
          m = "That room is not in your immediate vicinity."
        youse = just ∘ _,_ m ∘ proj₁ ∘ q'
          where
          q' = movePawn q $ GameData.player' q
          m = "You travel successfully."
      mathch : String ⊎ List F
      mathch with methching $ indice $ GameData.rooms q
        where
        indice = λ l → flip Data.List.zip l $ allFin $ length l
        methching = filterₗ $ _≟_ cname ∘ Room.cname ∘ proj₂
      ... | [] = inj₁ m
        where
        m = "Did you take your pills this morning?  \
            \I don't think that that room exists."
      ... | (x ∷ xs) = inj₂ $ map proj₁ $ filterₗ tr $ x ∷ xs
        where
        tr = flip any? (Room.travis cur) ∘ _≟_ ∘ Room.cname ∘ proj₂
\end{code}

\subsection{la'oi .\F{wield?}.}
ni'o ga jonai la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'i goi la'o zoi.\ \F{wield?} \B a \B b\ .zoi.\ gi ga je la'oi .\F{wield?}.\ djuno pe'a ru'e lo du'u tu'a la'o zoi.\ \B a .zoi.\ .indika lo du'u lo kelci cu djica lo nu ko'a goi lo kelci ke xarpre ja co'e cu me'oi .wield.\ ko'e goi zo'e poi la'o zoi.\ \B c .zoi.\ mu'oi glibau.\ \AgdaField{Item.cname} .glibau.\ lo sinxa be ke'a gi ga jonai ga je skuxai ja co'e la'o zoi.\ \B x .zoi.\ gi ko'i du la'o zoi.\ \AgdaInductiveConstructor{just} \OpF \$ \B x \OpF , \B b .zoi.\ gi ga je li pa nilzilcmi lo'i selvau be lo me'oi .inventory.\ be ko'a be'o be'o poi la'o zoi.\ \B c .zoi.\ mu'oi glibau.\ \AgdaField{Item.cname} .glibau.\ ke'a je poi curmi lo nu me'oi .wield.\ ke'a gi ga je tu'a la'o zoi.\ \B x .zoi.\ lu'u je tu'a la'o zoi.\ \B y .zoi.\ cu .indika lo du'u ko'a me'oi .wield.\ ko'e gi ko'i du la'o zoi.\ \AgdaInductiveConstructor{just} \OpF \$ \B x \OpF , \B y .zoi.

\begin{code}
wield? : Com
wield? [] = const nothing
wield? (x ∷ xs) dang = if (realShit x) (troci xs) nothing
  where
  inv = Character.inventory $ GameData.player dang
  wisyj = Data.Maybe.is-just ∘ Item.weapwn ∘ _!_ inv
  realShit = _≡ᵇ_ "WIELD"
  troci : List String → Maybe $ String × GameData
  troci [] = just $ m , dang
    where m = "Bitch, you'd best tell me what you \
              \want to wield, or I'll wield \
              \your bones as clubs."
  troci (_ ∷ _ ∷ _) = just $ m , dang
    where
    m = "You are giving me useless information."
  troci (y ∷ []) with flt $ mapMaybe mapti? $ allFin _
    where
    flt = filterₗ $ _≟_ y ∘ Item.cname ∘ _!_ inv ∘ proj₁
    mapti? : _ → Maybe $ Σ (Fin _) $ _≡_ true ∘ wisyj
    mapti? n with true ≟ wisyj n
    ... | yes x = just $ n , x
    ... | no _ = nothing
  ... | [] = just $ m , dang
    where
    m = "You need to stop chugging PCP or whatever.  \
        \Your hallucinations are pissing me off."
  ... | (_ ∷ _ ∷ _) = just $ m , dang
    where
    m = "Your query matches multiple items, although \
        \a proof of that your bag only contains items \
        \which have unique names exists.\n\
        \Something is mad fucked, and you might \
        \actually be innocent this time."
  ... | (selpli ∷ []) = just $ wieldMsg , proj₁ wieldData
    where
    wieldMsg = fromMaybe "You wield the weapon." xarcynotci
      where
      xarci = Item.weapwn $ inv ! proj₁ selpli
      xarcynotci = xarci Data.Maybe.>>= WeaponInfo.wieldMsg
    wieldData = wieldPawn dang p (proj₁ selpli) $ proj₂ selpli
      where
      p = GameData.player' dang
\end{code}

\section{la'oi .\F{take?}.}
ni'o ga jonai ga je djuno pe'a lo du'u tu'a la'o zoi.\ \B s\ .zoi.\ .indika lo du'u lo kelci cu djica lo nu lo me'oi .inventory.\ be ko'a goi lo kelci ke xarpre ja co'e cu vasru ko'e goi lo se mu'oi fancu.\ \F{Item.cname}\ .fancu.\ be la'o zoi.\ \B C\ .zoi.\ gi\ldots
\begin{itemize}
	\item ga jonai ga je ko'e zasti gi\ldots
	\begin{itemize}
		\item ga jonai ga je tu'a la'o zoi.\ \B g\ .zoi.\ .indika lo du'u lo me'oi .inventory. be ko'a cu vasru ko'e gi fo'a goi la'o zoi.\ \F{take?} \B s \B g\ .zoi.\ me'oi .\F{just}.\ lo .orsi be lo te skuxai ja co'e bei la'o zoi.\ \B g\ .zoi.\ gi fo'a me'oi .\F{just}.\ lo .orsi be zo'e poi tu'a ke'a .indika ko'i goi lo du'u lo me'oi .inventory.\ be ko'a cu vasru ko'e ku'o bei lo smimlu be la'o zoi.\ \B g\ .zoi.\ be'o poi ku'i tu'a ke'a .indika ko'i gi
		\item fo'a me'oi .\F{just}.\ lo .orsi be lo te skuxai ja co'e bei la'o zoi.\ \B g\ .zoi.\ gi
	\end{itemize}
	\item ga jonai ga je jinvi pe'a lo du'u la'o zoi.\ \B s\ .zoi.\ mabla gi fo'a me'oi .\F{just}.\ lo .orsi be lo te skuxai bei la'o zoi.\ \B g\ .zoi.\ gi fo'a du la'oi .\F{nothing}.
\end{itemize}

\begin{code}
take? : Com
take? ("TAKE" ∷ []) = just ∘ _,_ m
  where
  m = "Take your pills, you fucking lunatic."
take? ("TAKE" ∷ _ ∷ _ ∷ _) = just ∘ _,_ m
  where
  m = "I can't permit that you take the entire room."
take? ("TAKE" ∷ x ∷ []) g with filterₗ methching itste
  where
  methching = _≟_ x ∘ Item.cname ∘ proj₁
  itste = indice $ Room.items $ GameData.rooms g ! kumfid
    where
    indice = λ t → Data.List.zip t $ allFin $ length t
    kumfid = Character.room $ GameData.player g
... | [] = just $ "You grasp the air... to no avail." , g
... | (t ∷ _) = just $ m , proj₁ (takePawn g k $ proj₂ t)
  where
  k = GameData.player' g
  m = "You take the " ++ Item.name (proj₁ t) ++ "."
take? _ _ = nothing
\end{code}

\section{la'oi .\F{hitme?}.}
ni'o ga jonai ga je tu'a la'oi .\B{s}.\ .indika lo du'u djica lo nu xrani ja co'e ko'a goi lo kelci ke xarpre ja co'e pe la'oi .\B{g}.\ gi ga je tu'a la'oi .\B{t}.\ lu'u je tu'a la'o zoi.\ \B{g'}\ .zoi.\ cu .indika lo du'u xrani ko'a gi ko'a goi la'o zoi.\ \F{hitme?} \B s \B g\ .zoi.\ du la'o zoi.\ \AgdaInductiveConstructor{just} \OpF \$ \B t \OpF , \B{g'}\ .zoi.\ gi ko'a du la'oi .\AgdaInductiveConstructor{nothing}.

\begin{code}
hitme? : Com
hitme? ("HIT" ∷ "ME!" ∷ []) g = just $ "BOOM!" , record g {
  haters = proj₁ u;
  player' = mink (GameData.player' g) $ proj₁ $ proj₂ u
  }
  where
  natsuprais = λ n → record n {health = 0ℚ}
  u = ual (GameData.haters g) (GameData.player' g) natsuprais
hitme? _ _ = nothing
\end{code}

\chapter{le zmiku}
ni'o la'au le zmiku li'u vasru le velcki be le fancu poi ke'a ctaipe lo smimlu be la'o zoi.\ \F{GameData} \Sym → \F{Maybe} \OpF \$ \F{String} \OpF × \F{GameData}\ .zoi.\ jenai poi tu'a ke'a se sarcu lo nu midnoi fi lo kelci

\section{la .\F{zmimrobi'o}.}
ni'o ga jonai ga je tu'a la'oi .\B{t}.\ .indika ko'a goi lo du'u lo kelci ke xarpre ja co'e cu morsi gi ga je tu'a la'oi .\B{s}.\ .indika ko'a gi ko'a goi la'o zoi.\ \F{zmimrobi'o} \B t\ .zoi.\ du la'o zoi.\ \AgdaInductiveConstructor{just} \OpF \$ \B s \OpF , \B t\ .zoi.\ gi ko'a du la'oi .\AgdaInductiveConstructor{nothing}.

\begin{code}
zmimrobi'o : GameData → Maybe $ String × GameData
zmimrobi'o t = if morsi (just $ "You be dead." , t) nothing
  where
  morsi = Data.Rational.ℚ.numerator lenijmive ℤ.≤ᵇ ℤ.0ℤ
    where
    import Data.Integer as ℤ
    lenijmive = Character.health $ GameData.player t
\end{code}
\end{document}

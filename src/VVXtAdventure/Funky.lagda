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
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\forall}}
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
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{∸}{\ensuremath{\mathnormal{\divdot}}}
\newunicodechar{⍨}{\raisebox{-0.25ex}{$\ddot\sim$}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal{\ell}}}
\newunicodechar{∋}{\ensuremath{\mathnormal{\ni}}}
\newunicodechar{∈}{\ensuremath{\mathnormal{\in}}}
\newunicodechar{∉}{\ensuremath{\mathnormal{\notin}}}
\newunicodechar{∎}{\ensuremath{\mathnormal{\blacksquare}}}
\newunicodechar{⟨}{\ensuremath{\mathnormal{\langle}}}
\newunicodechar{⟩}{\ensuremath{\mathnormal{\rangle}}}
\newunicodechar{𝔦}{\ensuremath{\mathfrak{i}}}
\newunicodechar{𝔪}{\ensuremath{\mathfrak{m}}}
\newunicodechar{𝓁}{\ensuremath{\mathcal{l}}}
\newunicodechar{⊃}{\ensuremath{\mathnormal{\supset}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\cmene{VVXtAdventure.Funky}

\title{la'o zoi.\ \texttt{\cmene}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.\ ja co'e}
ni'o la'o zoi.\ \texttt{\cmene}\ .zoi. vasru le velcki be lo fancu be fi la'oi .\F{GameData}.\ ja zo'e

\section{le me'oi .preamble.\ ja co'e}

\begin{code}
{-# OPTIONS --safe #-}

module VVXtAdventure.Funky where

import Level
import Agda.Builtin.Unit as ABU
import Data.List.Properties as DLP

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
    _⊎_;
    inj₁;
    inj₂;
    [_,_]
  )
open import Function
open import Data.Bool
  renaming (
    if_then_else_ to if
  )
  hiding (
    _≤_;
    _≟_
  )
open import Data.List
  using (
    mapMaybe;
    List;
    _∷_;
    []
  )
  renaming (
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
  hiding (
    length;
    _≤_;
    _≟_
  )
open import Data.Product
  using (
    Σ;
    map₂;
    proj₁;
    proj₂;
    _×_;
    _,_
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
open import Truthbrary.Record.LLC
  using (
    nu,iork;
    length;
    _∉_;
    map
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

\section{la'o zoi.\ \F{movePawn} .zoi.}
ni'o tu'a la'o zoi.\ \F{movePawn} \B q \B m \B n .zoi.\ .indika lo du'u lo selsni be la'o zoi.\ \F{GameData.haters} \B q \Sym ! \B h .zoi.\ cu zvati ko'a goi lo selsni be la'o zoi.\ \F{GameData.rooms} \B q) \Sym ! \B n .zoi.

\begin{code}
movePawn : (q : GameData)
         → (i : Fin $ Data.List.length $ GameData.haters q)
         → (j : Fin $ Data.List.length $ GameData.rooms q)
         → let 𝓁 = Data.List.length in
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
ni'o tu'a la'o zoi.\ \F{wieldPawn} \B q \B m \B n \F{refl}\ .zoi.\ .indika lo du'u zo'e ja lo selsni be la'o zoi.\ \F{GameData.haters} \B q \Sym ! \B m\ .zoi.\ cu me'oi .wield.\ lo selsni be la'o zoi.\ \F{Character.inventory} (\F{GameData.haters} \B q \Sym ! \B m) \Sym ! \B n\ .zoi.

\begin{code}
wieldPawn : (q : GameData)
          → let x = GameData.haters in
            let 𝓁 = Data.List.length in
            let iv = Character.inventory in
            let ifinc = GameData.yourfloorisnowclean in
            (j : Fin $ 𝓁 $ x q)
          → (i : Fin $ 𝓁 $ Character.inventory $ x q ! j)
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
            × let cik = Data.List._++_ in
              (_≡_
                (cik
                  (Data.List.take (toℕ j) $ x q)
                  (Data.List.drop (ℕ.suc $ toℕ j) $ x q))
                (subst (List ∘ Character) (sym rud)
                  (cik
                    (Data.List.take (toℕ j) $ x q')
                    (Data.List.drop (ℕ.suc $ toℕ j) $ x q'))))
wieldPawn gd j i t = gd' , xenlen , xendj , refl , sym tivos , refl , teid
  where
  ⊃ = Data.List.head
  𝓁 = Data.List.length
  _↓_ = Data.List.drop
  _↑_ = Data.List.take

  xen = GameData.haters gd
  x₁ = (toℕ j) ↑ xen
  x₂ = record (xen ! j) {wieldedct = just $ i , t}
  x₃ = (ℕ.suc $ toℕ j) ↓ xen
  xen' = x₁ Data.List.++ x₂ ∷ x₃

  dropkat : ∀ {a} → {A : Set a}
          → (xs ys : List A)
          → (𝓁 xs) ↓ (xs Data.List.++ ys) ≡ ys
  dropkat [] _ = refl
  dropkat (_ ∷ xs) ys = dropkat xs ys

  xenlen = begin
    𝓁 xen ≡⟨ cong 𝓁 $ sym $ DLP.take++drop j' xen ⟩
    𝓁 (x₁ Data.List.++ d₂) ≡⟨ DLP.length-++ x₁ ⟩
    𝓁 x₁ + 𝓁 d₂ ≡⟨ cong (_+_ $ 𝓁 x₁) $ DLP.length-drop j' xen ⟩
    𝓁 x₁ + (𝓁 xen ∸ j') ≡⟨ cong (_+_ $ 𝓁 x₁) $ sym xex ⟩
    𝓁 x₁ + 𝓁 (x₂ ∷ x₃) ≡⟨ cong (_+_ $ 𝓁 x₁) refl ⟩
    𝓁 x₁ + ℕ.suc (𝓁 x₃) ≡⟨ sym $ DLP.length-++ x₁ ⟩
    𝓁 xen' ∎
    where
    j' = toℕ j
    d₂ = j' ↓ xen
    xex = begin
      𝓁 (x₂ ∷ x₃) ≡⟨ refl ⟩
      ℕ.suc (𝓁 $ ℕ.suc j' ↓ xen) ≡⟨ dropsuc xen j ⟩
      𝓁 (j' ↓ xen) ≡⟨ DLP.length-drop j' xen ⟩
      𝓁 xen ∸ j' ∎
      where
      dropsuc : ∀ {a} → {A : Set a}
              → (x : List A)
              → (n : Fin $ 𝓁 x)
              → let n' = toℕ n in
                ℕ.suc (𝓁 $ ℕ.suc n' ↓ x) ≡ 𝓁 (n' ↓ x)
      dropsuc (x ∷ xs) (Fin.zero) = refl
      dropsuc (x ∷ xs) (Fin.suc n) = dropsuc xs n

  xent : ⊃ ((𝓁 x₁) ↓ xen') ≡ just (xen' ! mink j xenlen)
  xent = sym $ subkon $ dropind xen' $ mink j xenlen
    where
    _≤_ = Data.Nat._≤_
    dropind : ∀ {a} → {A : Set a}
            → (xs : List A)
            → (n : Fin $ 𝓁 xs)
            → just (xs ! n) ≡ ⊃ ((toℕ n) ↓ xs)
    dropind (x ∷ xs) Fin.zero = refl
    dropind (x ∷ xs) (Fin.suc n) = dropind xs n
    teiklendus : ∀ {a} → {A : Set a}
               → (xs : List A)
               → (n : ℕ)
               → n ≤ 𝓁 xs
               → 𝓁 (n ↑ xs) ≡ n
    teiklendus _ 0 _ = refl
    teiklendus (x ∷ xs) (ℕ.suc n) (Data.Nat.s≤s q) = ret
      where
      ret = cong ℕ.suc $ teiklendus xs n q
    mindut : {m n : ℕ}
           → (o : Fin m)
           → (x : m ≡ n)
           → toℕ (mink o x) ≡ toℕ o
    mindut o refl = refl
    lisuc : ∀ {a} → {A : Set a}
          → (xs : List A)
          → (n : Fin $ 𝓁 xs)
          → Σ ℕ $ _≡_ (𝓁 xs) ∘ ℕ.suc
    lisuc (_ ∷ xs) j = 𝓁 xs , refl
    tuik : toℕ j ≤ 𝓁 xen
    tuik = subst (_≤_ _) kix $ DNP.≤-step $ subst (_≥_ _) mijd j'
      where
      _≥_ = flip _≤_
      j' = DFP.≤fromℕ $ mink j $ proj₂ $ lisuc xen j
      mijd = mindut j $ proj₂ $ lisuc xen j
      kix : ℕ.suc (toℕ $ Data.Fin.fromℕ _) ≡ 𝓁 xen
      kix = tondus $ sym $ proj₂ $ lisuc xen j
        where
        tondus : {m n : ℕ}
               → m ≡ n
               → toℕ (Data.Fin.fromℕ m) ≡ n
        tondus {ℕ.zero} = id
        tondus {ℕ.suc m} {ℕ.suc n} refl = ret
          where
          ret = cong ℕ.suc $ tondus {m} {n} refl
    xil = begin
      toℕ (mink j xenlen) ≡⟨ mindut j xenlen ⟩
      toℕ j ≡⟨ sym $ teiklendus xen (toℕ j) tuik ⟩
      𝓁 x₁ ∎
    subkon = subst (_≡_ _) $ cong (⊃ ∘ flip _↓_ xen') xil

  xendj : let iv = Character.inventory in
          iv (xen ! j) ≡ iv (xen' ! mink j xenlen)
  xendj = DMP.just-injective x₂d
    where
    iv = Character.inventory
    x₂d = begin
      just (iv $ xen ! j) ≡⟨ refl ⟩
      just (iv x₂) ≡⟨ refl ⟩
      mapₘ iv (⊃ $ x₂ ∷ x₃) ≡⟨ cong (mapₘ iv ∘ ⊃) $ dropsim ⟩
      mapₘ iv (⊃ $ (𝓁 x₁) ↓ xen') ≡⟨ cong (mapₘ iv) xent ⟩
      just (iv $ xen' ! mink j xenlen) ∎
      where
      mapₘ = Data.Maybe.map
      dropsim = sym $ dropkat x₁ $ x₂ ∷ x₃

  tivos = cong u₁ xijre
    where
    j' = mink j xenlen
    mapₘ = Data.Maybe.map
    u₁ = mapₘ (toℕ ∘ proj₁) ∘ Character.wieldedct
    xij = xen' ! mink j xenlen
    xijre : xij ≡ x₂
    xijre = sym $ DMP.just-injective $ begin
      just x₂ ≡⟨ refl ⟩
      ⊃ (x₂ ∷ x₃) ≡⟨ cong ⊃ (sym $ dropkat x₁ $ x₂ ∷ x₃) ⟩
      ⊃ ((𝓁 x₁) ↓ xen') ≡⟨ xent ⟩
      just (xen' ! mink j xenlen) ≡⟨ refl ⟩
      just xij ∎

  teid = begin
    cik ((toℕ j) ↑ xen) (ℕ.suc (toℕ j) ↓ xen) ≡⟨ refl ⟩
    cik x₁ x₃ ≡⟨ cong (flip cik x₃) $ takedus xen j ⟩
    cik x₁' x₃ ≡⟨ cong (cik x₁') $ dropydus xen {x₂ ∷ x₃} j ⟩
    cik x₁' x₃' ∎
    where
    cik = Data.List._++_
    x₁' = (toℕ j) ↑ xen'
    x₃' = (ℕ.suc $ toℕ j) ↓ xen'
    takedus : ∀ {a} → {A : Set a}
            → (a : List A)
            → {b : List A}
            → (n : Fin $ 𝓁 a)
            → let n' = toℕ n in
              n' ↑ a ≡ n' ↑ (flip cik b $ n' ↑ a)
    takedus (_ ∷ xs) zero = refl
    takedus (x ∷ xs) (suc n) = cong (_∷_ x) $ takedus xs n
    dropydus : ∀ {a} → {A : Set a}
             → (a : List A)
             → {b : List A}
             → {x : A}
             → (n : Fin $ 𝓁 a)
             → let n' = toℕ n in
               let s = ℕ.suc n' in
               s ↓ a ≡ s ↓ cik (n' ↑ a) (x ∷ s ↓ a)
    dropydus (_ ∷ xs) zero = refl
    dropydus (_ ∷ xs) {b} (suc n) = dropydus xs {b} n

  p' = mink (GameData.player' gd) xenlen
  gd' = record gd {haters = xen'; player' = p'}
\end{code}

\section{la'o zoi.\ \F{takePawn}\ .zoi.}
ni'o tu'a la'o zoi.\ \F{takePawn} \B q \B m \B n .zoi.\ cu .indika lo du'u lo me'oi .inventory.\ be lo selsni be la'o zoi.\ \F{GameData.haters} \B q \Sym ! \B m\ .zoi.\ cu vasru lo selsni be la'o zoi.\ (\F{GameData.itemsInRoomOf} \B q \B m) \Sym ! n\ .zoi... kei je zo'e

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
    wieldedct =  Character.wieldedct x;
    yourfloorisnowclean = Character.yourfloorisnowclean x}

takePawn : (q : GameData)
         → (m : Fin $ length $ GameData.haters q)
         → (n : Fin $ length $ GameData.itemsInRoomOf q m)
         → Σ GameData $ λ q'
           → Σ ((_≡_ on length ∘ GameData.rooms) q q') $ λ r
           → Σ ((_≡_ on length ∘ GameData.haters) q q') $ λ x
             -- | lb
           → let xen = GameData.haters in
             let room = Character.room in
             (Σ (Character $ GameData.rooms q') $ λ k
              → (_≡_
                  (Data.List.map (kumfybi'o q q' r)
                    (Data.List._++_
                      (Data.List.take (toℕ m) $ xen q)
                      (_∷_
                        (kumfybi'o q' q (sym r) k)
                        (Data.List.drop
                          (ℕ.suc $ toℕ m)
                          (GameData.haters q)))))
                  (Data.List._++_
                    (Data.List.take
                      (toℕ m)
                      (GameData.haters q'))
                    (_∷_
                      k
                      (Data.List.drop
                        (ℕ.suc $ toℕ m)
                        (xen q'))))))
           × (Σ Room $ λ r'
              → let kit = toℕ $ room $ xen q ! m in
                (_≡_
                  (GameData.rooms q')
                  (Data.List._++_
                    (Data.List.take kit $ GameData.rooms q)
                    (_∷_
                      r'
                      (Data.List.drop
                        (ℕ.suc kit)
                        (GameData.rooms q))))))
           × let iofink = GameData.yourfloorisnowclean in
             (_≡_
               q'
               record q {
                 rooms = GameData.rooms q';
                 haters = GameData.haters q';
                 player' = mink (GameData.player' q) x;
                 yourfloorisnowclean = iofink q'})
           × (_≡_
               (map Item.cname $ GameData.inventOf q' $ mink m x)
               ((_∷_ ⍨)
                 (map Item.cname $ GameData.inventOf q m)
                 (Item.cname $ GameData.itemsInRoomOf q m ! n)))
takePawn q m n = q' , dus , dis , xendus , kumdus , refl , nyfin
  where
  lb = GameData.haters q ! m
  sl = Room.items (GameData.rooms q ! Character.room lb) ! n
  vimcu = λ x → record x {items = filterₗ nadu $ Room.items x}
    where
    nadu = Data.Bool._≟_ false ∘ _≡ᵇ_ (Item.cname sl) ∘ Item.cname
  vimcud : (q : Room) → Room.cname (vimcu q) ≡ Room.cname q
  vimcud _ = refl
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
    wieldedct = Data.Maybe.map f $ Character.wieldedct x;
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
    f = λ (l , k) → Fin.suc l , k
  x'' : Σ (List $ Character k') $ λ x'
        → Σ (length (GameData.haters q) ≡ length x') $ λ ℓ
        → _
  x'' = ualmap (GameData.haters q) kumbi'o lb! m
  q' = record {
    epicwin = GameData.epicwin q;
    rooms = k';
    haters = proj₁ x'';
    yourfloorisnowclean = subst nu,iork entydut iofink;
    player' = mink (GameData.player' q) $ proj₁ $ proj₂ x''
    }
    where
    mapₗ = Data.List.map
    k = GameData.rooms q
    entydut = begin
      mapₗ cname k ≡⟨ madek k libek cname ⟩
      konk b₁ (cname k₁) b₂ ≡⟨ cong (flip (konk b₁) b₂) entydus ⟩
      konk b₁ (cname k₂) b₂ ≡⟨ cong konk₁ $ ualteik k libek vimcu ⟩
      konk b₁' (cname k₂) b₂ ≡⟨ cong konk₂ $ ualdrop k libek vimcu ⟩
      konk b₁' (cname k₂) b₂' ≡⟨ sym $ madek k' libek' cname ⟩
      mapₗ cname k' ∎
      where
      cname = Room.cname
      libek = Character.room lb
      libek' = mink libek $ proj₁ $ proj₂ k''
      k₁ = k ! libek
      k₂ = k' ! libek'
      konk : ∀ {a} → {A : Set a}
           → List A → A → List A → List A
      konk = λ b₁ b₂ b₃ → b₁ Data.List.++ b₂ ∷ b₃
      _↑_ = Data.List.take
      _↓_ = Data.List.drop
      b₁ = mapₗ cname $ (toℕ libek) ↑ k
      b₂ = mapₗ cname $ (ℕ.suc $ toℕ libek) ↓ k
      b₁' = mapₗ cname $ (toℕ libek') ↑ k'
      b₂' = mapₗ cname $ (ℕ.suc $ toℕ libek') ↓ k'
      konk₁ = λ b1 → konk (mapₗ cname b1) (cname k₂) b₂
      konk₂ = konk b₁' (cname k₂) ∘ mapₗ cname
      entydus = sym $ begin
        cname k₂ ≡⟨ cong cname $ proj₂ $ proj₂ k'' ⟩
        cname (vimcu k₁) ≡⟨ vimcud k₁ ⟩
        cname k₁ ∎
      madek : ∀ {a b} → {A : Set a} → {B : Set b}
            → (x : List A)
            → (n : Fin $ length x)
            → (f : A → B)
            → (_≡_
                (mapₗ f x)
                (Data.List._++_
                  (mapₗ f $ ((toℕ n) ↑ x))
                  (_∷_
                    (f $ x ! n)
                    (mapₗ f $ ((ℕ.suc $ toℕ n) ↓ x)))))
      madek (_ ∷ _) zero _ = refl
      madek (x ∷ xs) (suc n) f = cong (_∷_ $ f x) $ madek xs n f
      misuks : {m n : ℕ}
             → (f : Fin m)
             → (d : m ≡ n)
             → ℕ.suc (toℕ f) ≡ toℕ (mink (suc f) $ cong ℕ.suc d)
      misuks f refl = refl
      ualteik : ∀ {a} → {A : Set a}
              → (x : List A)
              → (n : Fin $ length x)
              → (f : A → A)
              → let u = ual x n f in
                (_≡_
                  ((toℕ n) ↑ x)
                  ((toℕ $ mink n $ proj₁ $ proj₂ $ u) ↑ proj₁ u))
      ualteik (_ ∷ _) zero _ = refl
      ualteik (x ∷ xs) (suc n) f = subst (_≡_ _) kong utz
        where
        ualteik₁ : ∀ {a} → {A : Set a}
                 → (x : List A)
                 → (n : Fin $ length x)
                 → (f : A → A)
                 → (toℕ n) ↑ x ≡ (toℕ n) ↑ proj₁ (ual x n f)
        ualteik₁ (_ ∷ _) zero _ = refl
        ualteik₁ (x ∷ xs) (suc n) f = cong (_∷_ x) $ ualteik₁ xs n f
        kong = cong (flip _↑_ $ proj₁ $ ual (x ∷ xs) (suc n) f) misuk
          where
          misuk = misuks n $ proj₁ $ proj₂ $ ual xs n f
        utz = ualteik₁ (x ∷ xs) (suc n) f
      ualdrop : ∀ {a} → {A : Set a}
              → (x : List A)
              → (n : Fin $ length x)
              → (f : A → A)
              → let n' = mink n $ proj₁ $ proj₂ $ ual x n f in
                (_≡_
                  ((ℕ.suc $ toℕ n) ↓ x)
                  ((ℕ.suc $ toℕ n') ↓ proj₁ (ual x n f)))
      ualdrop (_ ∷ _) zero _ = refl
      ualdrop (x ∷ xs) (suc n) f = subst (_≡_ _) c ut
        where
        ualdrop₁ : ∀ {a} → {A : Set a}
                 → (x : List A)
                 → (n : Fin $ length x)
                 → (f : A → A)
                 → let n' = ℕ.suc $ toℕ n in
                   n' ↓ x ≡ n' ↓ proj₁ (ual x n f)
        ualdrop₁ (_ ∷ _) zero _ = refl
        ualdrop₁ (_ ∷ xs) (suc n) f = ualdrop₁ xs n f
        ut = ualdrop₁ (x ∷ xs) (suc n) f
        c = cong (flip _↓_ $ proj₁ u) $ misuks n $ proj₁ $ proj₂ u
          where
          u = ual xs n f
    p = GameData.player q
    kac = Data.List.map Room.cname $ GameData.rooms q
    kec = Data.List.map Room.cname k'
    iofink = GameData.yourfloorisnowclean q
  dus = proj₁ $ proj₂ k''
  dis = proj₁ $ proj₂ x''
  nyfin = f (inv lb) (inv lb') sl Item.cname $ cong inv $ proj₂ $ proj₂ x''
    where
    lb' = proj₁ x'' ! mink m (proj₁ $ proj₂ x'')
    inv = Character.inventory
    f : ∀ {a b} → {A : Set a} → {B : Set b}
      → (b c : List A) → (x : A) → (f : A → B) → x ∷ b ≡ c
      → map f c ≡ f x ∷ map f b
    f b c x g refl = refl

  xendus = lb! (kumbi'o lb) , j
    where
    xen = GameData.haters q
    xen' = GameData.haters q'
    j = begin
      kib ¨ (konk xenim likil' xensim) ≡⟨ mapinj xenim xensim kib ⟩
      konk xenkim (kib likil') xenksim ≡⟨ cong (flip (konk xenkim) xenksim) midju ⟩
      klonk xenkim xenksim ≡⟨ sym $ mapimplant xen likil kib m ⟩
      klonk xenim' xensim' ≡⟨ cong (flip Data.List._++_ _) xenteik ⟩
      klonk (m:ℕ ↑ xen') xensim' ≡⟨ cong (konk (m:ℕ ↑ xen') likil) xendrop ⟩
      klonk (m:ℕ ↑ xen') ((ℕ.suc m:ℕ) ↓ xen') ∎
      where
      _++ₗ_ = Data.List._++_
      _¨_ = Data.List.map
      _↑_ = Data.List.take
      _↓_ = Data.List.drop
      konk : ∀ {a} → {A : Set a}
           → List A → A → List A → List A
      konk = λ a b c → a ++ₗ (b ∷ c)
      likil = lb! (kumbi'o lb)
      klonk = λ a → konk a likil
      likil' = kumfybi'o q' q (sym dus) likil
      kib = kumfybi'o q q' dus
      m:ℕ = toℕ m
      m' = mink m $ sym $ DLP.length-map kumbi'o xen
      xenim = m:ℕ ↑ xen
      xensim = (ℕ.suc m:ℕ) ↓ xen
      xenkim = kib ¨ xenim
      xenksim = kib ¨ xensim
      xenbis = kumbi'o ¨ xen
      xenim' = m:ℕ ↑ xenbis
      xensim' = (ℕ.suc m:ℕ) ↓ xenbis
      m≡m' : toℕ m ≡ toℕ m'
      m≡m' = tomindus m $ sym $ DLP.length-map kumbi'o xen
      u = ual xenbis m' lb!
      xenteik = begin
        xenim' ≡⟨ refl ⟩
        (toℕ m) ↑ xenbis ≡⟨ cong (flip _↑_ xenbis) m≡m' ⟩
        (toℕ m') ↑ xenbis ≡⟨ Truthbrary.Data.List.Loom.ualteik xenbis m' lb! ⟩
        (toℕ m') ↑ (proj₁ u) ≡⟨ refl ⟩
        (toℕ m') ↑ xen' ≡⟨ cong (flip _↑_ xen') $ sym m≡m' ⟩
        (toℕ m) ↑ xen' ∎
      xendrop : xensim' ≡ (ℕ.suc $ toℕ m) ↓ xen'
      xendrop = begin
        xensim' ≡⟨ refl ⟩
        (ℕ.suc $ toℕ m) ↓ xenbis ≡⟨ cong (flip _↓_ xenbis ∘ ℕ.suc) m≡m' ⟩
        (ℕ.suc $ toℕ m') ↓ xenbis ≡⟨ Truthbrary.Data.List.Loom.ualdrop xenbis m' lb! ⟩
        (ℕ.suc $ toℕ m') ↓ (proj₁ u) ≡⟨ refl ⟩
        (ℕ.suc $ toℕ m') ↓ xen' ≡⟨ cong (flip _↓_ xen' ∘ ℕ.suc) $ sym m≡m' ⟩
        (ℕ.suc $ toℕ m) ↓ xen' ∎
      midju : kib likil' ≡ likil
      midju = cong cninykumfa $ mindus (Character.room likil) (sym dus) dus
        where
        cninykumfa = λ n → record likil {room = n}
      mapinj : ∀ {a b} → {A : Set a} → {B : Set b}
             → (xs ys : List A)
             → {x : A}
             → (f : A → B)
             → (_≡_
                 (_¨_
                   f
                   (Data.List._++_
                     xs
                     (x ∷ ys)))
                 (Data.List._++_
                   (f ¨ xs)
                   (f x ∷ f ¨ ys)))
      mapinj [] _ _ = refl
      mapinj (x ∷ xs) ys f = cong (_∷_ $ f x) $ mapinj xs ys f

  kumdus = xenku'a , ualkonk kumste (Character.room lb) vimcu
    where
    kumste = GameData.rooms q
    xenku'a = vimcu $ kumste ! Character.room lb
\end{code}

\chapter{le mu'oi glibau.\ high-level .glibau.}

\section{le fancu poi tu'a ke'a na rinka lo nu lo ctaipe be la'oi .\F{GameData}.\ cu na binxo pe'a ru'e}

\subsection{la'oi .\F{epicwin?}.}
ni'o ga jonai ga je tu'a la'o zoi.\ \B a .zoi.\ .indika le du'u jinga gi ga je la'o zoi.\ \B b .zoi.\ du lo xatra ja co'e poi tu'a ke'a cusku pe'a ru'e le du'u jinga gi ko'a goi la'o zoi.\ \F{epicwin?} \B a .zoi. du la'o zoi.\ \B b , \B a .zoi.\ gi ko'a du la'oi .\F{nothing}.

\begin{code}
epicwin? : GameData → COut
epicwin? = scrimmage GameData.epicwin
  where
  jasat = "YOU HAVE ACCOMPLISHED\n\
          \THE MISSION.\n\
          \YOU ARE THE VERY PREVAILER\n\
          \THAT PROTECT RIGHT\n\
          \AND JUSTICE.\n\
          \I WOULD EXPRESS MY SINCERE.\n\
          \THANKS TO YOU.\n\n\
          \\
          \TAKE GOOD REST !\n\n\
          \\
          \\tGENERAL KAWASAKI"
  scrimmage : (GameData → Bool) → GameData → COut
  scrimmage f g = if (f g) (just $ jasat , g) nothing
\end{code}

\subsection{la'oi .\F{inspect?}.}
ni'o ga jonai ga je ga je la'oi .\F{inspect?}.\ djuno pe'a ru'e lo du'u tu'a la'o zoi.\ \B a .zoi.\ .indika lo du'u djica lo nu skicu la'o zoi.\ B b .zoi.\ gi cumki fa lo nu skicu la'o zoi.\ \B b .zoi.\ gi ga je la'o zoi.\ \B q .zoi.\ velski la'o zoi.\ \B b .zoi.\ gi ko'a goi la'o zoi.\ \F{inspect?} \B a \B{godDamn} .zoi.\ du la'o zoi.\ \F{just} \Sym \$ \B b \Sym , \B{godDamn} .zoi.\ gi ga jonai ga je la'oi .\F{inspect?}.\ djuno pe'a ru'e lo du'u la'o zoi.\ \B a .zoi.\ mabla gi ga je la'o zoi.\ \B i .zoi.\ te skuxai gi ko'a du la'o zoi.\ \F{just} \Sym \$ \B i \Sym , \B{godDamn} .zoi.\ gi ko'a du la'oi .\F{nothing}.

\begin{code}
inspect? : Com
inspect? (c ∷ f) dang = if methch (getDown f) nothing
  where
  methch = c ≡ᵇ "INSPECT"
  getDown : List String → COut
  getDown (n ∷ []) = gd' $ filterₗ (_≟_ n ∘ Item.cname) inv
    where
    inv = Character.inventory $ GameData.player dang
    gd' : List Item → COut
    gd' (q ∷ []) = just $ Item.hlDescr q , dang
    gd' (_ ∷ _ ∷ _) = just $ m , dang
      where
      m = "You're going to have to be more specific.  \
          \Sure, I could choose some arbitrary matching \
          \item, but that would probably piss you off, \
          \and I'm already insulting you right and left."
    gd' [] = just $ "I'm not seeing it." , dang
  getDown (_ ∷ _ ∷ _) = just $ m , dang
    where
    m = "I can't handle any more of your inane \
        \gibberish.\n\
        \If you want to search for multiple things, \
        \then tell me the shortnames of the things \
        \individually.\n\
        \Alternatively, you might have tried to \
        \search for a full name which contains \
        \multiple spaces, which is illegal.  \
        \Do it $n$ more times, and I will send the \
        \police to your doorstep.  I'm trying to \
        \help you, but you're really testing my \
        \patience now."
  getDown [] = just $ m , dang
    where
    m = "nothing : ∀ {a} → {A : Set a} → Maybe A"
inspect? [] _ = nothing
\end{code}

\subsection{la'oi .\F{invent?}.}
ni'o ga jonai ga je tu'a la'o zoi.\ \B m\ .zoi.\ .indika lo du'u lo kelci cu djica lo nu skicu lo selvau be ko'a goi lo me'oi .inventory.\ be lo kelci ke xarpre ja co'e gi ga je la'o zoi.\ \B s\ .zoi.\ vasru lo velski be lo ro selvau be ko'a gi ko'e goi la'o zoi.\ \F{invent?} \B \B g\ .zoi.\ du la'o zoi.\ \F{just} \Sym \$ \B s \Sym , \B g .zoi.\ gi ko'e du la'oi .\F{nothing}.

\begin{code}
invent? : Com
invent? ("LIST" ∷ "INVENTORY" ∷ []) g = just $ desk , g
  where
  desk = concat $ Data.List.intersperse "\n\n" le'i-cname-je-velski
    where
    items = Character.inventory $ GameData.player g
    konk = λ a → Item.cname a ++ ": " ++ Item.hlDescr a
    le'i-cname-je-velski = Data.List.map konk items
invent? _ _ = nothing
\end{code}

\subsection{la'oi .\F{kumski?}.}

ni'o ga jonai ga je la'oi .\F{scream?}.\ djuno pe'a ru'e lo du'u tu'a la'o zoi.\ \B a .zoi.\ .indika lo du'u lo kelci cu djica lo nu tcidu ko'a goi lo velski be lo selvau be lo kumfa poi la'o zoi.\ \B b\ .zoi.\ .indika lo du'u ke'a zasti gi ga je la'o zoi.\ \B v .zoi.\ vasru lo velcki be ko'a gi ko'e goi la'o zoi.\ \F{kumski?} \B a \B b\ .zoi.\ du la'o zoi.\ \F{just} \Sym \$ \B v \Sym , \B b\ .zoi.\ gi ko'e du la'oi .\F{nothing}.

\begin{code}
kumski? : Com
kumski? m g = if mapti (just $ vijac , g) nothing
  where
  mapti = Data.List.take 3 m ≡ᵇ ("LOOK" ∷ "AROUND" ∷ "YOU" ∷ [])
  kumfa = GameData.rooms g ! kumfid
    where
    kumfid = Character.room $ GameData.player g
  -- | ni'o zo .vijac. cmavlaka'i lu velski ja canlu li'u
  vijac : String
  vijac = concatₛ $ intersperseₗ "\n\n" le'i-ro-velski
    where
    intersperseₗ = Data.List.intersperse
    concatₛ = Data.String.concat
    mapₗ = Data.List.map
    velski : Item → String
    velski z with filterₗ methch $ Item.rmDescr z
      where
      methch = λ a → proj₁ a ≟ Room.cname kumfa
    ... | [] = Item.cname z ++ ": " ++ Item.dfDescr z
    ... | (x ∷ _) = Item.cname z ++ ": " ++ proj₂ x
    jaiv : String
    jaiv with Room.travis kumfa
    ... | [] = "This room is completely isolated.  GFL."
    ... | (x ∷ xs) = "CONNECTED ROOMS: " ++ concatₛ liste
      where
      liste = intersperseₗ ", " $ x ∷ xs
    le'i-ro-velski = jaiv ∷ mapₗ velski (Room.items kumfa)
\end{code}

\subsection{la'oi .\F{scream?}.}
ni'o ga jonai ga je la'oi .\F{scream?}.\ djuno pe'a ru'e lo du'u tu'a la'o zoi.\ \B a .zoi.\ .indika lo du'u lo kelci cu djica lo nu krixa fa ko'a goi lo krixa ke xarpre ja co'e po la'o zoi.\ \B b .zoi.\ gi ga je tu'a la'o zoi.\ \B c .zoi.\ .indika lo du'u ko'a krixa gi ko'e goi la'o zoi.\ \F{scream?} \B a \B b .zoi.\ du la'o zoi.\ \F{just} \Sym \$ c \Sym , b .zoi.\ gi ko'e du la'oi .\F{nothing}.

\begin{code}
scream? : Com
scream? ("SCREAM" ∷ []) q = just $ "AARGH!!!" , q
scream? _ _ = nothing
\end{code}

\subsection{la'oi .\F{sayless?}.}
ni'o ga jonai ga je la'o zoi.\ \B a .zoi.\ kunti gi ga je tu'a la'o zoi.\ \B c .zoi.\ .indika le du'u mabla fa lo nu samci'a lo kunti gi ko'a goi la'o zoi.\ \F{sayless?} \B a \B b .zoi.\ du la'o zoi.\ \F{just} \Sym \$ \B c \Sym , \B b .zoi.\ gi ko'a du la'oi .\F{nothing}.

\begin{code}
sayless? : List String → GameData → COut
sayless? [] = just ∘ _,_ "The silent treatment won't work here."
sayless? _ = const nothing
\end{code}

\subsection{la'oi .\F{lp?}.}
ni'o ga jonai ga je ga je la'o zoi.\ \B c .zoi.\ na vajni gi ko'a goi la'o zoi.\ \F{lp?} \B a \B b .zoi.\ du la'o zoi.\ \F{just} \B c \B b .zoi.\ gi ko'a du la'oi .\F{nothing}.

\begin{code}
lp? : Com
lp? ("WHO" ∷ "ARE" ∷ "YOU?" ∷ []) q = just $ m , q
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

\section{la'oi .\F{travel?}.}
ni'o ga jonai ga je la'o zoi.\ \F{travel?} .zoi.\ djuno ja co'e lo du'u lo nu co'e ko'a goi zoi zoi.\ \F{travel?} \B r \B g .zoi.\ cu nu cpedu lo nu lo kelci ke xarpre ja co'e cu klama lo kumfa poi la'o zoi.\ \B K .zoi.\ sinxa ke'a gi ga jonai ga je la'o zoi.\ \F{Room.travis} \Sym \$ \F{Character.room} \Sym \$ \F{GameData.player} \B g .zoi.\ vasru la'o zoi.\ \B K .zoi.\ gi ko'a broda cei sinxa ja co'e lo me'oi .product.\ be lo velski be lo nu klama bei zo'e poi tu'a ke'a .indika lo du'u lo kelci ke xarpre ja co'e cu zvati zo'e poi djica lo nu zvati ke'a xi re gi ko'a broda lo me'oi .product.\ be lo te skuxai ja zo'e bei la'o zoi.\ \B g .zoi.\ gi ko'a broda la'oi .\F{nothing}.

\begin{code}
travel? : Com
travel? [] _ = nothing
travel? (x₁ ∷ xs₁) = if realShit (travel' xs₁) $ const nothing
  where
  realShit = x₁ ≡ᵇ "TRAVEL"
  travel' : Com
  travel' [] q = just $ m , q
    where
    m = "Don't tell me to break the rules, fucker!"
  travel' (x ∷ []) q = maybe just tryfind $ alreadythere?
    where
    F = Fin $ length $ GameData.rooms q
    cur = GameData.rooms q ! Character.room (GameData.player q)
    alreadythere? = if atRoom (just $ m , q) nothing
      where
      atRoom = x ≡ᵇ Room.cname cur
      m = "Damn, that's some fast travel.  \
          \You're already there!"
    tryfind = [_,_] (just ∘ flip _,_ q) iusyf mathch
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
      mathch = travelable $ methching $ zipfin $ GameData.rooms q
        where
        zipfin = λ l → Data.List.zip (Data.List.allFin $ length l) l
        methching = filterₗ $ _≟_ x ∘ Room.cname ∘ proj₂
        travelable : List $ F × Room → String ⊎ List F
        travelable [] = inj₁ m
          where
          m = "Did you take your pills this morning?  \
              \I don't think that that room exists."
        travelable (x ∷ xs) = inj₂ $ pj1s $ filterₗ tr $ x ∷ xs
          where
          pj1s = Data.List.map proj₁
          cnq = λ a b → Room.cname (proj₂ a) ≟ b
          tr = λ a → any? (cnq a) $ Room.travis cur
  travel' (_ ∷ _ ∷ _) q = just $ m , q
    where
    m = "I strongly doubt that the concept of \"super\
        \position\" applies to a creature of your mass."
\end{code}

\section{la'oi .\F{wield?}.}
ni'o ga jonai ga je ga je la'oi .\F{wield?}.\ djuno pe'a ru'e lo du'u tu'a la'o zoi.\ \B a .zoi.\ .indika lo du'u lo kelci cu djica lo nu ko'a goi lo kelci ke xarpre ja co'e cu me'oi .wield.\ ko'e goi zo'e poi la'o zoi.\ \B c .zoi.\ mu'oi glibau.\ \F{Item.cname} .glibau.\ lo sinxa be ke'a gi ga jonai ga je li pa nilzilcmi lo'i selvau be lo me'oi .inventory.\ be ko'a be'o be'o poi la'o zoi.\ \B c .zoi.\ mu'oi glibau.\ \F{Item.cname} .glibau.\ ke'a je poi curmi lo nu me'oi .wield.\ ke'a gi tu'a la'o zoi.\ \B x .zoi.\ lu'u je tu'a la'o zoi.\ \B y .zoi.\ cu .indika lo du'u ko'a me'oi .wield.\ ko'e gi ko'i goi la'o zoi.\ \F{wield?} \B a \B b .zoi.\ du la'o zoi.\ \F{just} \Sym \$ \B x \Sym , \B y .zoi.\ gi ga je skuxai ja co'e la'o zoi.\ \B x .zoi.\ gi ko'a du la'o zoi.\ \F{just} \Sym \$ \B x \Sym , \B b .zoi.\ gi ko'a du la'oi .\F{nothing}.

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
  troci (y ∷ []) with flt $ mapMaybe mapti? $ Data.List.allFin _
    where
    flt = filterₗ $ _≟_ y ∘ cname ∘ proj₁
      where
      cname = Item.cname ∘ Data.List.lookup inv
    mapti? : _ → Maybe $ Σ (Fin _) $ _≡_ true ∘ wisyj
    mapti? n with true Data.Bool.≟ wisyj n
    ... | yes x = just $ n , x
    ... | no _ = nothing
  ... | [] = just $ m , dang
    where
    m = "You need to stop chugging PCP or whatever.  \
        \Your hallucinations are pissing me off."
  ... | (selpli ∷ []) = just $ wieldMsg , proj₁ wieldData
    where
    wieldMsg = fromMaybe "You wield the weapon." xarcynotci
      where
      items = Character.inventory $ GameData.player dang
      xarci = Item.weapwn $ items ! proj₁ selpli
      xarcynotci = xarci Data.Maybe.>>= WeaponInfo.wieldMsg
    wieldData = wieldPawn dang p (proj₁ selpli) $ proj₂ selpli
      where
      p = GameData.player' dang
  ... | (_ ∷ _ ∷ _) = just $ m , dang
    where
    m = "Your query matches multiple items, although \
        \a proof of that your bag only contains items \
        \which have unique names exists.\n\
        \Something is mad fucked, and you might \
        \actually be innocent this time."
\end{code}
\end{document}

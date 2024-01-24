\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{selnolig}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\nolig{>>}{>|>}
\nolig{<<}{<|<}

\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{∃}{\ensuremath{\mathnormal{\exists}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_i}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_o}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\title{le me'oi .Agda.\ velcki be la .tat.\ noi ke'a samselkei je cu frafi'a le bebna}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .preamble.\ ja co'e}

\begin{code}
{-# OPTIONS --guardedness #-}

import Level
import Data.Fin
import Agda.Builtin.IO as ABIO
import Agda.Builtin.Unit as ABU

open import IO
  using (
    putStrLn;
    getLine;
    _<$>_;
    Main;
    run;
    IO
  )
  renaming (
    _>>_ to _>>ᵢₒ_;
    _>>=_ to _>>=ᵢₒ_
  )
open import Function
  using (
    _∘_;
    _$_;
    id
  )
open import Data.Char
  using (
    toUpper
  )
open import Data.List
  using (
    List;
    _∷_;
    []
  )
open import Data.Maybe
  using (
    fromMaybe;
    Maybe;
    just;
    nothing
  )
open import Data.String
  using (
    String;
    words
  )
open import Data.Product
  using (
    uncurry;
    proj₂;
    proj₁;
    _×_;
    _,_;
    ∃
  )
open import Algebra.Core
  using (
    Op₁
  )
open import TestAdventure.WYCT
open import VVXtAdventure.Base
open import VVXtAdventure.Funky
open import Data.Unit.Polymorphic
  using (
    ⊤
  )
open import Truthbrary.Record.LLC
  using (
    _++_;
    map
  )
open import Relation.Binary.PropositionalEquality
  using (
    refl
  )
\end{code}

\section{la'o zoi.\ \F{fanmo?}\ .zoi.}
ni'o ga jonai la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'a goi la'o zoi.\ \F{fanmo?}\ \B x .zoi.\ gi ga je .indika ko'e goi le du'u lo kelci ke xarpre ja co'e cu morsi ja cu co'e gi ko'a me'oi .\AgdaInductiveConstructor{just}.\ zo'e poi tu'a ke'a .indika ko'e

\begin{code}
fanmo? : ∀ {a} → GameData → Maybe $ IO {a} ⊤
fanmo? = firstJust ∘ Data.List.map mapti? ∘ fancu
  where
  firstJust : ∀ {a} → {A : Set a} → List $ Maybe A → Maybe A
  firstJust = Data.List.head ∘ Data.List.mapMaybe id
  mapti? = Data.Maybe.map $ putStrLn ∘ proj₁
  fancu : GameData → List COut
  fancu q = zmimrobi'o q ∷
            epicwin? winmsg q ∷
            []
\end{code}

\section{la'oi .\F{main}.}

\begin{code}
{-# NON_TERMINATING #-}
main : Main
main = run $ IO.lift nurtcati >>ᵢₒ lupe initialD
  where
  postulate nurtcati : ABIO.IO ABU.⊤
  {-# FOREIGN GHC import System.OpenBSD.Plegg #-}
  {-# COMPILE GHC nurtcati = plegg [Stdio] >> univac [] #-}

  lupe = λ q → fromMaybe (interact q) $ fanmo? q
    where
    interact : GameData → IO ⊤
    interact = λ q → prompt >>ᵢₒ ree >>=ᵢₒ crock q
      where
      prompt = putStrLn "What do you do?"
      ree = words ∘ map toUpper <$> getLine
      crock : GameData → List String → IO ⊤
      crock gd s = proj₂ $ chews np $ ("" , gd) , mis naj gd
        where
        mis = λ a b → putStrLn a >>ᵢₒ lupe b
        naj = "I don't understand a word you just said."
        chews : ∀ {a b} → {A : Set a} → {B : A → Set b}
              → List $ Maybe A × ((x : A) → B x)
              → Op₁ $ ∃ B
        chews [] = id
        chews ((nothing , _) ∷ xs) = chews xs
        chews ((just b , f) ∷ _) _ = b , f b
        np : List $ COut × (String × GameData → IO ⊤)
        np = map (λ f → f s gd , uncurry mis) std
          where
          std = sazycimde ++ gasnu
            where
            sazycimde = scream? ∷
                        sayless? ∷
                        inspect? ∷
                        lp? ∷
                        kumski? ∷
                        invent? ∷
                        []
            gasnu = travel? ∷
                    wield? ∷
                    hitme? ∷
                    smash? ∷
                    []
\end{code}
\end{document}

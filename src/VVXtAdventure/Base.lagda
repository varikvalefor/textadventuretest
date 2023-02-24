\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\cmene{VVXtAdventure.Base}

\title{la'o zoi.\ \texttt{\cmene}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.\ ja co'e}
ni'o la'o zoi.\ \texttt{\cmene}\ .zoi.\ vasru le velcki be vu'oi le me'oi .\AgdaKeyword{record}.\ je zo'e vu'o poi ke'a vajni la .tat.\ je poi mutce lo ka ce'u pilno ke'a

\section{le me'oi .preamble.\ ja co'e}

\begin{code}
{-# OPTIONS --safe #-}

module VVXtAdventure.Base where

open import Data.Fin
  using (
    Fin
  )
open import Data.Nat
open import Function
open import Data.Bool
open import Data.List
open import Data.Maybe
open import Data.String
open import Data.Product
\end{code}

\section{le fancu}

\subsection{la'oi .\F{\_!\_}.}
ni'o la .varik.\ cu sorpa'a lo nu na sarcu fa lo nu ciksi

\begin{code}
_!_ : ∀ {a} → {A : Set a}
    → (q : List A) → Fin $ Data.List.length q → A
_!_ (x ∷ xs) (Fin.suc n) = _!_ xs n
_!_ (x ∷ xs) (Fin.zero) = x
\end{code}

\section{le me'oi .\AgdaKeyword{record}.}

  \subsection{la'oi .\F{Item}.}

ni'o ga jo ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'oi .\F{Item}.\ gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \F{Item.name} \B a .zoi.\ mu'oi glibau.\ display name .glibau.\ ko'a gi
	\item ga je ga je ko'e goi la'o zoi.\ \F{Item.cname} \B a .zoi.\ cmene ko'a gi cadga fa lo nu lo kelci cu pilno ko'e tu'a ko'a gi
	\item la'o zoi.\ \F{Item.description} \B a .zoi.\ velski ko'a
\end{itemize}

\begin{code}
record Item : Set
  where
  field
    name : String
    cname : String
    description : String
\end{code}

\subsection{la'oi .\F{Room}.}
ni'o ga jo la'o zoi.\ \B S .zoi.\ fa'u ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'oi .\F{Set}.\ fa'u la'o zoi.\ \F{Room} \B S .zoi.\ gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \F{Room.name} \B a .zoi.\ cmene lo selsni be ko'a gi
	\item ga je cadga fa lo nu lo kelci cu pilno la'o zoi.\ \F{Room.cname} \B a .zoi.\ tu'a ko'a gi
	\item la'o zoi.\ \F{Room.items} \B a .zoi.\ liste lo'i selvau be lo selsni be ko'a be'o poi ke'a ba'e na prenu
\end{itemize}

\begin{code}
record Room : Set
  where
  field
    name : String
    cname : String
    items : List Item
\end{code}
    
\subsection{la'oi .\F{GameData}.}
ni'o ga jo ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'oi .\F{GameData} .zoi.\ gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \F{GameData.forename} \B a .zoi.\ du'acme ko'e goi lo kelci ke xarpre ja co'e po ko'a gi
        \item ga je la'o zoi.\ \F{GameData.surname} \B a .zoi.\ lazme'e ko'e gi
        \item ga je ga jo la'o zoi.\ \F{GameData.epicwin} \B a .zoi.\ du la'oi .\F{true}.\ gi ga je le kelci cu jinga gi le selkei cu mulno ja co'e gi
	\item ga je la'o zoi.\ \F{GameData.nicknames} \B a .zoi.\ liste lo'i datcme be ko'e gi
	\item ga je la'o zoi.\ \F{GameData.rooms} \B a .zoi.\ liste lo'i ro co'e poi cumki fa lo nu ke'a se zvati ko'e gi
	\item ga je tu'a ko'a indika lo du'u ko'e zvati lo selsni be la'o zoi.\ (\F{GameData.rooms} \B a) \Sym ! (\F{GameData.room} \B a) .zoi.\ gi
        \item ga je la'o zoi.\ \F{GameData.inventory} \B a .zoi.\ liste lo'i ro se ralte ko'e gi
	\item tu'a ko'a .indika lo du'u lo kelci ke xarpre ja co'e cu zvati la'o zoi.\ \F{GameData.room} \B a .zoi.
\end{itemize}

\begin{code}
record GameData : Set
  where
  field
    forename : String
    surname : String
    epicwin : Bool
    nicknames : List String
    rooms : List Room
    room : Fin $ Data.List.length rooms
    inventory : List Item
\end{code}

\section{le sampu}

\subsection{la'oi .\F{COut}.}

ni'o ro da poi ke'a midnoi ja co'e zo'u ga jonai ga je lo se pruce cu mapti da gi da me'oi .\F{just}.\ pruce fi lo ctaipe be la'o zoi.\ \F{String} \Sym × \F{GameData} .zoi.\ be'o noi cagda fa lo nu ciska lo se .orsi be ke'a lo mu'oi glibau.\ standard output .glibau.\ kei je lo nu me'oi .\F{main}.\ pilno lo te .orsi be ke'a gi da du la'oi .\F{nothing}.

.i la'oi .\F{COut}.\ na mutce lo ka ce'u smimlu la'oi .\texttt{cout}.\ po la'o zoi.\ C++ .zoi.\ fo la .varik.

\begin{code}
COut = Maybe $ String × GameData
\end{code}

\subsection{la'oi .\F{Com}.}

ni'o la'oi .\F{Com}.\ se ctaipe lo so'i midnoi fancu pe la .tat.

.i ga naja ko'a goi lo kelci cu mu'oi glibau.\ standard input .glibau.\ samci'a la'o zoi.\ \B g .zoi.\ gi lakne fa lo nu cadga fa lo nu ga je lo ctaipe be la'o zoi.\ \F{List String} .zoi.\ cu du la'o zoi.\ \F{words} \B g .zoi.\  gi lo ctaipe be la'oi .\F{GameData}.\ cu velcki lo selkei be ko'a

\begin{code}
Com = List String → GameData → COut
\end{code}
\end{document}

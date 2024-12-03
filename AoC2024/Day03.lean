import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith

-- definition of a regular expression
inductive RegExp where
  | empty : RegExp
  | char : Char → RegExp
  | concat : RegExp → RegExp → RegExp
  | star : RegExp → RegExp
  | or : RegExp → RegExp → RegExp

-- definition of how a regular expression matches a string
inductive RegExpMatch : RegExp → List Char → Prop where
  | mEmpty : RegExpMatch .empty []
  | mChar x : RegExpMatch (.char x) [x]
  | mConcat r1 r2 s1 s2
    (h1 : RegExpMatch r1 s1)
    (h2 : RegExpMatch r2 s2) :
    RegExpMatch (.concat r1 r2) (s1 ++ s2)
  | mStar0 r : RegExpMatch (.star r) []
  | mStarMore r s1 s2
    (h1 : RegExpMatch r s1)
    (h2 : RegExpMatch (.star r) s2) :
    RegExpMatch (.star r) (s1 ++ s2)
  | mOrL r1 r2 s
    (h : RegExpMatch r1 s) :
    RegExpMatch (.or r1 r2) s
  | mOrR r1 r2 s
    (h : RegExpMatch r2 s) :
    RegExpMatch (.or r1 r2) s

-- custom syntax for declaring regexes
declare_syntax_cat regex

syntax char : regex
syntax ident : regex
syntax regex "+" regex : regex
syntax regex regex : regex
syntax regex "*" : regex
syntax "(" regex ")" : regex
syntax "/" regex "/" : term

macro_rules
  | `(/ $t:ident /) => `($t)
  | `(/ $c:char /) => `(RegExp.char $c)
  | `(/ $a:regex + $b:regex /) => `(RegExp.or /$a/ /$b/)
  | `(/ $a:regex $b:regex /) => `(RegExp.concat /$a/ /$b/)
  | `(/ $a:regex * /) => `(RegExp.star /$a/)
  | `(/ ($a:regex) /) => `(/$a/)


-- the definition of the mul pattern
def nonZeroDigit : RegExp := /'1' + '2' + '3' + '4' + '5' + '6' + '7' + '8' + '9'/
def digit : RegExp := /'0' + nonZeroDigit/

def mulPattern : RegExp := /'m''u''l''('(nonZeroDigit digit*)','(nonZeroDigit digit*)')'/

-- prove that some strings are indeed matched
example : RegExpMatch mulPattern "mul(30,5)".toList := by
  unfold mulPattern
  apply RegExpMatch.mConcat _ _ ['m']
  · constructor
  · apply RegExpMatch.mConcat _ _ ['u']
    · constructor
    · apply RegExpMatch.mConcat _ _ ['l']
      · constructor
      · apply RegExpMatch.mConcat _ _ ['(']
        · constructor
        · apply RegExpMatch.mConcat _ _ ['3','0']
          · apply RegExpMatch.mConcat _ _ ['3']
            · apply RegExpMatch.mOrR
              apply RegExpMatch.mOrR
              apply RegExpMatch.mOrL
              constructor
            · apply RegExpMatch.mStarMore _ ['0']
              · apply RegExpMatch.mOrL
                constructor
              · constructor
          · apply RegExpMatch.mConcat _ _ [',']
            · constructor
            · apply RegExpMatch.mConcat _ _ ['5']
              · apply RegExpMatch.mConcat _ _ ['5']
                · apply RegExpMatch.mOrR
                  apply RegExpMatch.mOrR
                  apply RegExpMatch.mOrR
                  apply RegExpMatch.mOrR
                  apply RegExpMatch.mOrL
                  constructor
                · constructor
              · constructor

{-# LANGUAGE NoMonomorphismRestriction, FlexibleContexts #-}
module ParensParsec where

import Control.Applicative
import Text.Parsec
import Text.Parsec.Indentation
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertFailure, Assertion)
                  

data A
  = Par A   -- '(' A ')'
  | Bra A   -- '[' A ']'
  | Seq A A -- A A
  | Nil     -- epsilon
  deriving (Show, Eq)

a :: (Monad m, Stream s m (Char, Indentation)) => ParsecT (IndentStream s) () m A
a = choice [ Seq <$> a' <*> a, a', return Nil ]

a' :: (Monad m, Stream s m (Char, Indentation)) => ParsecT (IndentStream s) () m A
a' = choice
    [ Par <$>
        between (localTokenMode (const Eq) $ char '(')
                (localTokenMode (const Eq) $ char ')')
                (localIndentation Gt a)
    , Bra <$>
        between (localTokenMode (const Ge) $ char '[')
                (localTokenMode (const Ge) $ char ']')
                (localIndentation Gt a)
    ]


runParse input
  = case runParser a () "" (mkIndentStream 0 infIndentation True Gt input) of
      Left err -> Left (show err)
      Right a  -> Right a

-- conveniences for tests
parL = Par . listToSeq
braL = Bra . listToSeq

listToSeq [] = Nil
listToSeq (x:xs) = Seq x $ listToSeq xs
    
input1 = [('(', 1),
          ('[', 4),
          ('(', 5),
          (')', 5),
          (']', 7),
          (')', 1)]
output1 = runParse input1
expected1 = listToSeq [ parL [braL [parL []]]
                      ]

input2 = [('(', 1),
          ('[', 8),
          ('(', 6),
          (')', 6),
          ('[', 8),
          (']', 9),
          (']', 4),
          ('(', 3),
          (')', 3),
          (')', 1)]
output2 = runParse input2
expected2 = listToSeq [ parL [ braL [ parL []
                                    , braL []
                                    ]
                             , parL []
                             ]
                      ]

assertParsedOk :: (Show err, Show a, Eq a) => Either err a -> a -> Assertion
assertParsedOk actual expected =
  case actual of
   Right ok -> assertEqual "parsing succeeded, but " expected ok
   Left err -> assertFailure ("parse failed with " ++ show err
                              ++ ", expected" ++ show expected)

allTests :: TestTree
allTests =
  testGroup "parens (parsec)"
  [ testCase "1" $ assertParsedOk output1 expected1
  , testCase "2" $ assertParsedOk output2 expected2
  ]

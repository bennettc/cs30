{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE InstanceSigs #-}
module CS30.Exercises.ProblemsBasics.Problems where
import           CS30.Data
import           CS30.Exercises.Data
import GHC.Real -- for (%)

-- data ProbEx = ProbAsRational [Field] Rational deriving Show

--todo 改成4个branch
choiceTreeList :: [ChoiceTree ([Field], Rational)]
choiceTreeList = [Branch [nodes [andExerciseEasy a b | a <- proba , b <- proba]]
                    , Branch [nodes [orExerciseEasy a b | a <- proba , b <- proba]]
                    , Branch [nodes [andExerciseHard a b | a <- proba , b <- proba]]
                    , Branch [nodes [orExerciseHard a b | a <- proba , b <- proba]]]

--generate questions based on two numbers
andExerciseEasy :: Rational -> Rational -> ([Field], Rational)
andExerciseEasy a b = ([FMath$ "Pr[A] =" ++ show(a), FText ", ", FMath$ "Pr[B] =" ++ show(b), 
                        FText ", Events A and B are independent. What is ", FMath "Pr[A \\wedge B]?"], (a*b))

orExerciseEasy ::  Rational -> Rational -> ([Field], Rational)
orExerciseEasy a b = ([FMath$ "Pr[A] =" ++ show(a), FText ", ", FMath$ "Pr[B] =" ++ show(b), 
                        FText ", Events A and B are independent. What is ", FMath "Pr[A \\vee B]?"], (a + b - a * b))

andExerciseHard :: Rational -> Rational -> ([Field], Rational)
andExerciseHard a b = ([FMath$ "Pr[A] =" ++ show(a), FText ", ", FMath$ "Pr[A \\wedge B] =" ++ show(a * b), 
                        FText ", Events A and B are independent. What is Pr[B]?"], b)

orExerciseHard :: Rational -> Rational -> ([Field], Rational)
orExerciseHard a b = ([FMath$ "Pr[A] =" ++ show(a), FText ", ", FMath$ "Pr[A \\vee B] =" ++ show(a + b - a * b), 
                        FText ", Events A and B are independent. What is Pr[B]?"], b)

proba :: [Ratio Integer]
proba = [0.25, 0.5, 0.75, 0.2, 0.4, 0.6]

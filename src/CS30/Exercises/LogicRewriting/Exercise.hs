module CS30.Exercises.LogicRewriting.Exercise where

import           CS30.Data
import           CS30.Exercises.Data
import           CS30.Exercises.Util
import qualified Data.Map as Map
import           Data.List
import           CS30.Exercises.LogicRewriting.Parsing (laws, lawNames, Expr (..), Op (..), Law (..))
import           CS30.Exercises.LogicRewriting.ProofGeneration (getDerivation, Proof (..), Subst, rewrites', matchExpr)

-- final exercise type
logicRewritingEx :: ExerciseType
logicRewritingEx = exerciseType "Logic Rewriting" "L?.?" "Logic Rewriting"
                       logicExercises
                       logicQuer
                       logicFeedback

-- generate initial expressions to put through the prover
initialExpr :: ChoiceTree Expr -> ChoiceTree Expr
initialExpr expr = neg <$> expr
                   where neg (Neg e)   = Neg e
                         neg otherExpr = Neg otherExpr

-- 
exprOfSize :: Int -> ChoiceTree Expr
exprOfSize 1 = Branch [nodes (map Const [True,False]), 
                       nodes (map Var ['p','q','r'])]
exprOfSize 2 = Branch [Neg <$> exprOfSize 1]
exprOfSize n = Branch [Bin op <$> exprOfSize i <*> exprOfSize (n-i-1)
                       | i <- [1..(n-2)]
                       , op <- [And, Or, Implies]]

-- extracts all the variables from an expression
getVars :: Expr -> [Char]
getVars (Var v) = [v]
getVars (Const _) = []
getVars (Neg e) = getVars e
getVars (Bin _ e1 e2) = getVars e1 ++ getVars e2

-- gets the size of an expression
-- (variables have size 0, because in the case of matching laws, 
-- they will be replaced by other expressions)
getSize :: Expr -> Int
getSize (Var _)       = 0
getSize (Const _)     = 1
getSize (Neg e)       = 1 + getSize e
getSize (Bin _ e1 e2) = 1 + getSize e1 + getSize e2

-- get all the laws which have given name
getLawsByName :: String -> ChoiceTree Law
getLawsByName name = nodes [(Law nm eq) | (Law nm eq) <- laws, nm == name]

-- gives all possible ways of rewriting expression by applying the laws
-- in reverse s times
rewriteExprs :: Int -> Expr -> ChoiceTree Expr
rewriteExprs 0 e = return e
rewriteExprs s e = do rewrite <- nodes $ concat [rewrites' matchExpr' (rhs,lhs) e 
                                                | (Law nm (lhs,rhs)) <- laws,
                                                 nm /= "Double Negation Law"]
                      -- ^ use all laws except double negation, to avoid expressions
                      -- with an excess of negations 
                      rewriteExprs (s-1) rewrite

-- a list of substitions which will rewrite only the variable names
-- and leave the expression otherwise the same
switchVars :: [Subst]
switchVars = [zip vars (map Var orders) 
             | orders <- permutations vars]
             where vars = ['p', 'r', 'q']

-- an alternate matchExpr which can transform constants into expression 
-- with variables (considering every possible "renaming" of these variables) 
-- 
-- TODO: give all alternate for Var too (make switchVars func)
matchExpr' :: Expr -> Expr -> [Subst]
matchExpr' (Const i) (Const j) | i == j = switchVars
matchExpr' e1 e2 = matchExpr e1 e2

-- gives all expressions which should simplify to the provided 
-- expression after applying s different laws
forceLaw :: Int -> Expr -> ChoiceTree Expr
forceLaw s e = do exprs <- rewriteExprs s e
                  return exprs

-- contains all the exercises: the list of Fields is what we display
-- and the String is the solution (actually just the index of the right choice)
logicExercises :: [ChoiceTree ([Field], String)]
logicExercises = [do (Law testName (lhs, rhs)) <- getLawsByName name
                     e <- initialExpr (forceLaw 2 lhs)
                     let (Proof e' steps) = getDerivation ((Law testName (lhs, rhs)):laws) e
                     remStep <- nodes $ findIndices ((== testName) . fst) steps
                     let (stepName, _) = steps!!remStep
                     choices <- (getOrderedSubset (delete stepName lawNames) 2)
                     correctN <- nodes [0..2]
                     let shuffChoices = putElemIn stepName correctN choices 
                     return (showExer (Proof e' steps) remStep shuffChoices, show correctN)
                  | name <- lawNames]
                 where putElemIn :: a -> Int -> [a] -> [a]
                       putElemIn y 0 xs = y:xs
                       putElemIn y _ [] = y:[]
                       putElemIn y n (x:xs) = x:(putElemIn y (n-1) xs)
                       displayStepsExcept _ [] _  = []
                       displayStepsExcept n (s:rems) choices = [FMath "\\equiv", name, 
                                                               FIndented 1 [FMath $ show (snd s)]]
                                                              ++ displayStepsExcept (n-1) rems choices
                                                              where correct = FText ("{ "++(fst s)++" }")
                                                                    name = if n/=0 then correct
                                                                           else FChoice "choice" (map (\x -> [FText $ "{ "++x++" }"]) choices)

                       showExer (Proof e steps) remStep choices = [FIndented 1 [FMath $ show e]] 
                                                                  ++ (displayStepsExcept remStep steps choices)

-- generate the question displayed to the user
logicQuer :: ([Field], String) -> Exercise -> Exercise
logicQuer (quer, _) defExer = defExer {eQuestion = quer}

-- generate feedback
logicFeedback :: ([Field], String) -> Map.Map String String -> ProblemResponse -> ProblemResponse
logicFeedback (_, sol) mStrs defaultRsp 
    = case rsp of 
        Just v -> if v == sol then markCorrect $ defaultRsp{prFeedback = [FText "Correct"]}
                  else if v == "" then markWrong $ defaultRsp{prFeedback = [FText "Please select which law is applied"]}
                       else markWrong $ defaultRsp{prFeedback = [FText "Incorrect"]} 
        Nothing -> markWrong $ defaultRsp{prFeedback = [FText "We could not understand your answer"]}
        -- ^ TODO: give better feedback (probably need to change the solution data structure to show the correct answer)
      where rsp = Map.lookup "choice" mStrs

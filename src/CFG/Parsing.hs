module CFG.Parsing (module Parseable) where

import Control.Monad
import Text.Parsec hiding (State, label)
import Text.Parsec.String
import Text.Parsec.Number
import Data.Char hiding (DecimalNumber)
import Data.List
import Parseable

import Solidity.Solidity
import Solidity.Parsing

import CFG.CFG

--Failure-safe choice


instance Parseable State where
    parser = do no <- many alphaNum
                char '\"'
                functionCall <- parser
                char '\"'
                return (FunctionCallState no functionCall)
             <||> do no <- many alphaNum
                     spaces *> char ':' <* spaces
                     functionCall <- parser
                     return (FunctionCallState no functionCall)
            <||> do no <- many alphaNum
                    spaces *> char ':' <* spaces
                    stmt <- parser
                    return (StatementState no stmt)
           <||> do no <- many alphaNum
                   spaces *> char ':' <* spaces
                   expr <- parser
                   return (ExpressionState no expr)
             <||> do string "throw"
                     return ThrowState
             <||> do string "revert"
                     return RevertState
             <||> do string "return"
                     return ReturnState
             <||> do no <- many alphaNum
                     return (BasicState{label = no})
    display ThrowState = "throw"
    display ReturnState = "return"
    display (RevertState) = "revert"
    display (StatementState l stmt) = "\"" ++ l ++ " : " ++ display stmt ++ "\""
    display (ExpressionState l expr) = "\"" ++ l ++ " : " ++ display expr ++ "\""
    display (BasicState l) = show l
    display (FunctionCallState l functionCall) = "\"" ++ l ++ " : " ++ display functionCall ++ "\""
--    display _ = "state"
--    display (ContractCallState l contractAddress (Identifier functionName)) = show l ++ " : " ++   contractAddress ++ "." ++ functionName ++ "()"
--    display (ContractDelegateCallState l contractAddress (Identifier functionName)) = show l ++ " : " ++   contractAddress ++ "#" ++ functionName ++ "()"

instance Parseable FunctionCall where
    parser = do functionName <- manyTill alphaNum (char '(' <* spaces)
                (char ')')
                return (FunctionCall (Identifier functionName) Nothing)
             <||> do functionName <- manyTill alphaNum (char '(' <* spaces)
                     expressionList <- parser
                     (char ')')
                     return (FunctionCall (Identifier functionName) (Just (Right expressionList)))
             <||> do functionName <- manyTill alphaNum (char '(' <* spaces)
                     nameValueList <- parser
                     (char ')')
                     return (FunctionCall (Identifier functionName) (Just (Left nameValueList)))
            <||> do expression <- parser
                    char '.'
                    functionName <- manyTill alphaNum (char '(' <* spaces)
                    (char ')')
                    return (OutsideFunctionCall expression (Identifier functionName) Nothing)
            <||> do expression <- parser
                    char '.'
                    functionName <- manyTill alphaNum (char '(' <* spaces)
                    expressionList <- parser
                    (char ')')
                    return (OutsideFunctionCall expression (Identifier functionName) (Just (Right expressionList)))
            <||> do expression <- parser
                    char '.'
                    functionName <- manyTill alphaNum (char '(' <* spaces)
                    nameValueList <- parser
                    (char ')')
                    return (OutsideFunctionCall expression (Identifier functionName) (Just (Left nameValueList)))
    display (FunctionCall functionName Nothing) = display functionName
    display (FunctionCall functionName (Just (Left nameValueList))) = display functionName ++ "(" ++ (display nameValueList) ++ ")"
    display (FunctionCall functionName (Just (Right expressionList))) = display functionName ++ "(" ++ (display expressionList) ++ ")"
    display (OutsideFunctionCall expression functionName (Nothing)) = display expression ++ "." ++ display functionName
    display (OutsideFunctionCall expression functionName (Just (Left nameValueList))) = display expression ++ "." ++ display functionName ++ "(" ++ (display nameValueList) ++ ")"
    display (OutsideFunctionCall expression functionName (Just (Right expressionList))) = display expression ++ "." ++ display functionName ++ "(" ++ (display expressionList) ++ ")"

instance Parseable Condition where
    parser =     do expression <- parser
                    spaces
                    string "=="
                    spaces
                    string "true"
                    return (ConditionHolds (expression))
            <||> do expression <- parser
                    spaces
                    string "=="
                    spaces
                    string "false"
                    return (ConditionDoesNotHold (expression))
            <||> do string "false"
                    return (FF)
            <||> do string "true"
                    return (TT)
    display (ConditionDoesNotHold expression) = (display expression) ++ " == false"
    display (ConditionHolds expression) = (display expression) ++ " == true"
    display (TT) = "true"
    display (FF) = "false"


instance Parseable Transition where
    parser = do src <- parser
                spaces
                string "->"
                dst <- parser
                spaces
                char '['
                spaces
                string "label"
                spaces
                char '='
                spaces
                char '"'
                condition <- parser
                char '"'
                return (Transition (src) (dst) (condition))
    display (Transition src dst condition) = (display src) ++ " -> " ++ (display dst) ++ " [label = \"" ++ (display condition) ++ "\"];\n"


--data FunctionSignature = FunctionSignature{
--                            functionName :: Identifier,
--                            parameters :: ParameterList,
--                            returnParams :: ParameterList
--                         } deriving (Eq, Ord, Show)


instance Parseable FunctionSignature where
    parser = do name <- parser
                spaces
                char '('
                spaces
                parameterList <- parser
                spaces
                char ')'
                spaces
                visibility <- parser
                spaces
                string "returns("
                spaces
                returnParamsList <- parser
                spaces
                char ')'
                return (FunctionSignature name visibility parameterList returnParamsList)

    display (FunctionSignature name visibility parameterList returnParamsList) = display name ++ display parameterList ++ " " ++ display visibility ++ " returns" ++ display returnParamsList ++ ""

instance Parseable FunctionVisibility where
    parser = try
              (do string "private"
                  return Private)
        <|>  try
              (do string "external"
                  return FExternal)
        <|>  try
              (do string "internal"
                  return FInternal)
        <|> do return Public
    display Public = "public"
    display Private = "private"
    display FExternal = "external"
    display FInternal = "internal"


instance Parseable FunctionCFG where
    parser = do string "digraph"
                spaces
                char '"'
                spaces
                signat <- parser
                char '"'
                spaces
                char '{'
                spaces
                string "initial"
                spaces
                string "->"
                spaces
                initialState <- parser
                spaces
                char ';'
                spaces
                endStates <- many (parser <* spaces <* string "->" <* spaces <* string "end" <* spaces <* char ';')
                transitionList <- many parser
                spaces
--                try string "labelloc=\"t\";"
--                string "label=\""
--                spaces
--                signat <- parser
--                spaces
--                string "\";"
--                spaces
                char '}'
                eof
                return FunctionCFG{signature = signat, transitions = transitionList, states = statesFromTransitions transitionList [], initial = initialState, end = endStates}

    display cfg = "digraph \"" ++ display (signature cfg) ++ "\"{\n" ++
              --      "initial -> " ++ display (initial cfg) ++ ";\n" ++
                    foldr (++) "" (map display (transitions cfg)) ++
                --    foldr (++) "" [display state ++ " -> end" ++ ";\n" | state <- (nub (end cfg))] ++
                    foldr (++) "" (nub [display (ExpressionState label expr) ++ "[style=filled, color=gray]" ++ ";\n" | Transition (ExpressionState label expr) _ _ <- (transitions cfg)]) ++
                    foldr (++) "" (nub [display (ExpressionState label expr) ++ "[style=filled, color=gray]" ++ ";\n" | Transition _ (ExpressionState label expr) _ <- (transitions cfg)]) ++
                    foldr (++) "" (nub [display (FunctionCallState label expr) ++ "[style=filled, color=lightblue]" ++ ";\n" | Transition _ (FunctionCallState label expr) _ <- (transitions cfg), isOutsideFunctionCall expr])
                    ++ "\n}"

isOutsideFunctionCall :: FunctionCall -> Bool
isOutsideFunctionCall (OutsideFunctionCall _ _ _) = True
isOutsideFunctionCall _ = False

instance Parseable CFG where
    parser = do cfgList <- many parser
                return (CFG cfgList)
    display (CFG []) = ""
    display (CFG (c:cs)) = (display c) ++ "\n" ++ (display (CFG cs))

statesFromTransitions :: [Transition] -> [State] -> [State]
statesFromTransitions [] states = states
statesFromTransitions ((Transition src dst _):ts) states =
                                let newStates = statesFromTransitions ts states
                                    withSource = if(elem src states)
                                                    then newStates
                                                    else newStates ++ [src]
                                    withDest = if(elem dst states)
                                                    then withSource
                                                    else withSource ++ [dst]
                                    in withDest

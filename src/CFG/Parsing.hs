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
(<||>) :: Parser a -> Parser a -> Parser a
p <||> q =  try p <|> q


instance Parseable State where
    parser = do no <- nat
                spaces *> char ':' <* spaces
 --               address <- manyTill alphaNum (string "#")
                functionName <- manyTill alphaNum (char '(' <* spaces)
                (char ')')
                return (FunctionCallState no (FunctionCall (Identifier functionName) Nothing))
             <||> do no <- nat
                     spaces *> char ':' <* spaces
                     functionCall <- parser
                     return (FunctionCallState no functionCall)
             <||> do string "throw"
                     return ThrowState
             <||> do string "return"
                     return ReturnState
             <||> do no <- nat
                     return (BasicState{label = no})
    display ThrowState = "throw"
    display ReturnState = "return"
    display (BasicState l) = show l
    display (FunctionCallState l functionCall) = "\"" ++ (show l) ++ " : " ++ display functionCall ++ "\"" 
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
    display (FunctionCall functionName Nothing) = display functionName
    display (FunctionCall functionName (Just (Left nameValueList))) = display functionName ++ "(" ++ (display nameValueList) ++ ")" 
    display (FunctionCall functionName (Just (Right expressionList))) = display functionName ++ "(" ++ (display expressionList) ++ ")" 

instance Parseable Label where
    parser = do char '*'
                return Any
            <||> do string "tau"
                    return Tau
            <||> do string "return"
                    spaces
                    expression <- parser 
                    return (ReturnLabel expression)
            <||> do string "return"
                    return ReturnVoid
            <||> do string "uponEntry"
                    spaces
                    char '('
                    functionCall <- parser
                    spaces
                    char ')'
                    spaces
                    return (Entering functionCall)
            <||> do string "uponExit"
                    spaces
                    char '('
                    functionCall <- parser
                    spaces
                    char ')'
                    spaces
                    return (Exiting functionCall)
            <||> do string "assert"
                    spaces
                    char '('
                    expression <- parser
                    spaces
                    char ')'
                    spaces
                    return (Assert expression)
            <||> do string "require"
                    spaces
                    char '('
                    expression <- parser
                    spaces
                    char ')'
                    spaces
                    return (Require expression)
            <||> do expression <- parser
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
    display Tau = "tau"
    display Any = "*"
    display (ReturnLabel expression) = "return " ++ (display expression) ++ ""
    display ReturnVoid = "return"
    display (Entering (functionCall)) = "uponEntry(" ++ display functionCall ++ ")"
    display (Exiting (functionCall)) = "uponExit(" ++ display functionCall ++ ")"
    display (Assert expression) = "assert(" ++ display expression ++ ")"
    display (Require expression) = "require(" ++ display expression ++ ")"
    display (ConditionDoesNotHold expression) = (display expression) ++ " == false" 
    display (ConditionHolds expression) = (display expression) ++ " == true" 
    display (LabelE expression) = display expression
    display (Label statement) = display statement
    
    
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
                event <- parser
                char '"'
                return (Transition (src) (dst) (event))
    display (Transition src dst event) = (display src) ++ " -> " ++ (display dst) ++ " [label = \"" ++ (display event) ++ "\"];\n"
    
instance Parseable FunctionCFG where
    parser = do string "digraph"
                spaces
                name <- manyTill anyToken (char '{')
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
                char '}'
                eof
                return FunctionCFG{functionName = name, transitions = transitionList, states = statesFromTransitions transitionList [], initial = initialState, end = endStates}
                
    display cfg = "digraph " ++ (functionName cfg) ++ "{\n" ++
                    "initial -> " ++ display (initial cfg) ++ ";\n" ++
                    foldr (++) "" [display state ++ " -> end" ++ ";" | state <- (end cfg)] ++ 
                    foldr (++) "" (map display (transitions cfg))
                    ++ "\n}"
                    
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
                                                  
                                                        
                                            
 
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
module CFG.CFG (State(..), Label(..), Transition(..), FunctionCFG(..), CFG(..), FunctionCall(..), contractCFG, contractCFGFromContractDefinition, FunctionVisibility(..), FunctionSignature(..), prependStatementLabelsWith) where

import Solidity.Solidity
import Data.List

type SCAddress = String

data State = BasicState {
            label :: String
            }
     | StatementState {
                 label :: String,
                 stmt :: Statement
                 }
     | ExpressionState {
                 label :: String,
                 expr :: Expression
      }
     | ThrowState
     | RevertState
     | ReturnState
     | FunctionCallState {
        label :: String,
        functionCall :: FunctionCall
        }
--     | OutsideFunctionCallState {
--        label :: String,
--        functionCall :: FunctionCall,
--        smartContract :: Either SCAddress Identifier --the address of the smartContract if hardcoded or the identifier of the address
--        }
--     | ContractCallState {
--        label :: Int,
--        contractAddress :: String,
--        contractFunctionInCalled :: FunctionName--,
--        --parametersPassed :: Maybe DEA.UntypedParameterList
--     }
--     | ContractDelegateCallState {
--        label :: Int,
--        contractAddress :: String,
--        contractFunctionInDelegated :: FunctionName--,
--        --parametersPassed :: Maybe DEA.UntypedParameterList
--     }
    deriving (Eq, Ord, Show)


data Label = ConditionHolds ExpressionList | ConditionDoesNotHold ExpressionList | TT | FF deriving (Eq, Ord, Show)

data FunctionCall = FunctionCall FunctionName (Maybe (Either NameValueList ExpressionList))
                    | OutsideFunctionCall Expression FunctionName (Maybe (Either NameValueList ExpressionList))  deriving (Eq, Ord, Show)

data FunctionVisibility = Public | Private | FInternal | FExternal deriving (Eq, Ord, Show)

data FunctionSignature = FunctionSignature{
                            functionName :: Identifier,
                            functionVisibility :: Maybe FunctionVisibility,
                            parameters :: ParameterList,
                            returnParams :: ParameterList
                         } deriving (Eq, Ord, Show)

data Transition =
  Transition {
      src, dst :: State,
      event :: Label
} deriving (Eq, Ord, Show)

--add possibility that control-flow is unknown
data FunctionCFG = FunctionCFG{
    signature :: FunctionSignature,
    transitions :: [Transition],
    states :: [State],
    initial :: State,
    end :: [State]
} deriving (Eq, Ord, Show)

data CFG = CFG [FunctionCFG]

--data SequenceFunctionCFGs = SequenceFunctionCFGs{
--    cfgs :: [FunctionCFG],
--    callingTransitions = [Transition]
--}

--------------------------------------------------------------
--------------------------------------------------------------


--Replace state with given controlflow
replaceStateWith :: FunctionCFG -> State -> (State, [Transition], [State]) -> FunctionCFG
replaceStateWith cfg state (startHere, trans, endHere) = FunctionCFG{
                                                            signature = signature cfg,
                                                            transitions = [Transition s startHere label | Transition s state label <- transitions cfg]
                                                                       ++ [Transition e s label | e <- endHere, Transition state s label <- transitions cfg]
                                                                       ++ trans
                                                                       ++ [t | t <- transitions cfg, src t /= state, dst t /= state],
                                                            states = (((states cfg) \\ [state]) ++ [startHere]) ++ endHere,
                                                            initial = if state == (initial cfg)
                                                                        then startHere
                                                                        else (initial cfg),
                                                            end = if elem state (end cfg)
                                                                    then ((end cfg) \\ [state]) ++ endHere
                                                                    else (end cfg)
                                                        }


--------------------------------------------------------------
--------------------------------------------------------------


--Replace state with given controlflow
replaceStateWithCFG :: FunctionCFG -> State -> FunctionCFG -> FunctionCFG
replaceStateWithCFG cfg state cfgg = FunctionCFG{
                                            signature = signature cfg,
                                            transitions = [Transition s (initial cfgg) label | Transition s state label <- transitions cfg]
                                                                 ++ [Transition e s label | e <- end cfgg, Transition state s label <- transitions cfg]
                                                                 ++ [t | t <- transitions cfg, src t /= state, dst t /= state],
                                            states = ((states cfg) \\ [state]) ++ (states cfgg),
                                            initial = if state == (initial cfg)
                                                        then initial cfgg
                                                        else (initial cfg),
                                            end = if elem state (end cfg)
                                                    then ((end cfg) \\ [state])
                                                    else (end cfg)
                                        }

--------------------------------------------------------------
--------------------------------------------------------------

--Replace state with given controlflow
replaceStateWithState :: FunctionCFG -> State -> State -> FunctionCFG
replaceStateWithState cfg state newState =                FunctionCFG{
                                                            signature = signature cfg,
                                                            transitions = [Transition s newState label | Transition s ss label <- transitions cfg, ss == state]
                                                                       ++ [Transition newState s label | Transition ss s label <- transitions cfg, ss == state]
                                                                       ++ [t | t <- transitions cfg, src t /= state, dst t /= state],
                                                            states = ((states cfg) \\ [state]) ++ [newState],
                                                            initial = if state == (initial cfg)
                                                                        then newState
                                                                        else (initial cfg),
                                                            end = if elem state (end cfg)
                                                                    then ((end cfg) \\ [state]) ++ [newState]
                                                                    else (end cfg)
                                                        }

--------------------------------------------------------------
--------------------------------------------------------------

handleAssertAndRequires :: [FunctionCFG] -> FunctionCFG -> FunctionCFG
handleAssertAndRequires (cfgs) cfg = let requireStates = [s | s <- (states cfg), not (requireIsOverridden cfgs), functionCallIsRequire s]
                                         assertStates = [s | s <- (states cfg), not (requireIsOverridden cfgs), functionCallIsAssert s]
                                         nonFunctionCallStates = [StatementState l s | StatementState l s <- (states cfg)]
                                         newCFGWithAssertAndRequire = functionCallStatesToAssertOrRequire (requireStates ++ assertStates) cfg
                                         x = head requireStates
                                       in newCFGWithAssertAndRequire

--------------------------------------------------------------
--------------------------------------------------------------

assertIsOverridden :: [FunctionCFG] -> Bool
assertIsOverridden [] = False
assertIsOverridden (cfg:cfgs) = if((functionName (signature cfg)) == Identifier "assert")
                                    then True
                                    else assertIsOverridden cfgs

requireIsOverridden :: [FunctionCFG] -> Bool
requireIsOverridden [] = False
requireIsOverridden (cfg:cfgs) = if(functionName (signature cfg) == Identifier "require")
                                    then True
                                    else requireIsOverridden cfgs

--------------------------------------------------------------
--------------------------------------------------------------

reLabelTransition :: Transition -> Label -> Transition
reLabelTransition (Transition s d l) ll = Transition s d ll
--------------------------------------------------------------
--------------------------------------------------------------
--data FunctionCall = FunctionCall FunctionName (Maybe (Either NameValueList ExpressionList)) deriving (Eq, Ord, Show)

functionCallStatesToAssertOrRequire :: [State] -> FunctionCFG -> FunctionCFG
functionCallStatesToAssertOrRequire [] cfg = cfg
functionCallStatesToAssertOrRequire (s:ss) cfg = let newCFG = functionCallToAssertOrRequire s cfg
                                                    in functionCallStatesToAssertOrRequire ss newCFG


--    data FunctionCall = FunctionCall FunctionName (Maybe (Either NameValueList ExpressionList))
--                        | OutsideFunctionCall Expression FunctionName (Maybe (Either NameValueList ExpressionList))  deriving (Eq, Ord, Show)

functionCallToAssertOrRequire :: State -> FunctionCFG -> FunctionCFG
functionCallToAssertOrRequire (FunctionCallState label (FunctionCall (Identifier "require") (Just (Right (ExpressionList [expression]))))) cfg =
                                                    let callState = (FunctionCallState label (FunctionCall (Identifier "require") (Just (Right (ExpressionList [expression])))))
                                                        newTransitions = [reLabelTransition t (ConditionHolds (ExpressionList [expression])) | t <- (transitions cfg), src t  == callState]
                                                        falseTransition = Transition callState RevertState (ConditionDoesNotHold (ExpressionList [expression]))
                                                        otherTransitions = (transitions cfg) \\ [t | t <- (transitions cfg), src t == callState]
                                                      in FunctionCFG{
                                                                  signature = signature cfg,
                                                                  transitions = otherTransitions ++ [falseTransition] ++ newTransitions,
                                                                  states = states cfg ++ [RevertState],
                                                                  initial = initial cfg,
                                                                  end = end cfg
                                                              }
functionCallToAssertOrRequire (FunctionCallState label (FunctionCall (Identifier "assert") (Just (Right (ExpressionList [expression]))))) cfg =
                                                            let callState = (FunctionCallState label (FunctionCall (Identifier "assert") (Just (Right (ExpressionList [expression])))))
                                                                newTransitions = [Transition callState s (ConditionHolds (ExpressionList [expression])) | Transition callState s _ <- (transitions cfg)]
                                                                falseTransition = Transition callState ThrowState (ConditionDoesNotHold (ExpressionList [expression]))
                                                                otherTransitions = (transitions cfg) \\ [t | t <- (transitions cfg), src t /= callState]
                                                          in FunctionCFG{
                                                                      signature = signature cfg,
                                                                      transitions = otherTransitions ++ [falseTransition] ++ newTransitions,
                                                                      states = states cfg ++ [RevertState],
                                                                      initial = initial cfg,
                                                                      end = end cfg
                                                                    }

functionCallToAssertOrRequire _ cfg = cfg

--------------------------------------------------------------
--------------------------------------------------------------

functionCallIsRequire:: State -> Bool
functionCallIsRequire (FunctionCallState _ (FunctionCall (Identifier "require") _)) = True
functionCallIsRequire _ = False

functionCallIsAssert :: State -> Bool
functionCallIsAssert (FunctionCallState _ (FunctionCall (Identifier "assert") _)) = True
functionCallIsAssert _ = False

--------------------------------------------------------------
--------------------------------------------------------------

isFunctionCallState :: State -> Bool
isFunctionCallState (FunctionCallState _ _) = True
isFunctionCallState _ = False

--------------------------------------------------------------
--------------------------------------------------------------

isAssert :: Expression -> Bool
isAssert (Literal (PrimaryExpressionIdentifier (Identifier {unIdentifier = "assert"}))) = True
isAssert _ = False

isRequire :: Expression -> Bool
isRequire (Literal (PrimaryExpressionIdentifier (Identifier {unIdentifier = "require"}))) = True
isRequire _ = False


--------------------------------------------------------------
--------------------------------------------------------------

contractCFG :: SolidityCode -> CFG
contractCFG (SolidityCode (SourceUnit sourceUnits)) =
                                let functionCFGs = map (contractCFGFromSource) sourceUnits
                                    functionCFGsFlattened = foldr (++) [] functionCFGs
                                    in CFG functionCFGsFlattened

--------------------------------------------------------------
--------------------------------------------------------------

contractCFGFromSource :: SourceUnit1 -> [FunctionCFG]
contractCFGFromSource (SourceUnit1_ContractDefinition contractDefinition) = contractCFGFromContractDefinition contractDefinition
contractCFGFromSource _ = []
--------------------------------------------------------------
--------------------------------------------------------------

contractCFGFromContractDefinition :: ContractDefinition -> [FunctionCFG]
contractCFGFromContractDefinition contractDefinition =
                                            let contractPartss = contractParts contractDefinition
                                                modifierCFGs = justifyList (map (parseModifierCFG) contractPartss)
                                                properFunctionsCFGs = justifyList (map (parseFunctionCFG modifierCFGs) contractPartss)
                                              in map (handleAssertAndRequires properFunctionsCFGs) properFunctionsCFGs
--------------------------------------------------------------
--------------------------------------------------------------

justifyList :: [Maybe FunctionCFG] -> [FunctionCFG]
justifyList [] = []
justifyList ((Just functionCFG):rest) = functionCFG:(justifyList rest)
justifyList ((Nothing):rest) = justifyList rest

--------------------------------------------------------------
--------------------------------------------------------------

functionDefinitionTagsToFunctionVisibility :: [FunctionDefinitionTag] -> FunctionVisibility
functionDefinitionTagsToFunctionVisibility [] = Public
functionDefinitionTagsToFunctionVisibility (FunctionDefinitionTagPublic:_) = Public
functionDefinitionTagsToFunctionVisibility (FunctionDefinitionTagPrivate:_) = Private
functionDefinitionTagsToFunctionVisibility (FunctionDefinitionTagStateMutability Internal:_) = FInternal
functionDefinitionTagsToFunctionVisibility (FunctionDefinitionTagStateMutability External:_) = FExternal
functionDefinitionTagsToFunctionVisibility (_:rest) = functionDefinitionTagsToFunctionVisibility rest

--------------------------------------------------------------
--------------------------------------------------------------

parseFunctionCFG :: [FunctionCFG] -> ContractPart -> Maybe FunctionCFG
--TODO handle input parameters
parseFunctionCFG modifierCFGs (ContractPartFunctionDefinition (Just id) params functionDefinitionTags return (Just block)) =
                                        let sign = FunctionSignature{
                                                functionName = id,
                                                functionVisibility = Just (functionDefinitionTagsToFunctionVisibility functionDefinitionTags),
                                                parameters = params,
                                                returnParams = case return of
                                                                Nothing -> ParameterList []
                                                                Just par -> par
                                            }
                                            initState = BasicState (show 0)
                                            cfg = FunctionCFG{
                                                      signature = sign,
                                                      transitions = [],
                                                      states = [initState],
                                                      initial = initState,
                                                      end = []
                                                  }
                                            (newCFG, state) = (cfgStepWithStatement (BlockStatement block) cfg (initial cfg))
                                            finalCFG = (addEndState newCFG state)
                                            relevantModifierCFGs = respectiveModifierCFGs functionDefinitionTags modifierCFGs
                                            in Just (addModifiersControlFlow finalCFG relevantModifierCFGs)


parseFunctionCFG modifierCFGs (ContractPartFunctionDefinition (Nothing) _ _ (_) (Just block)) =
                                        let sign = FunctionSignature{
                                                functionName = Identifier "",
                                                functionVisibility = Just Public,
                                                parameters = ParameterList [],
                                                returnParams = ParameterList []
                                            }
                                            initState = BasicState (show 0)
                                            cfg = FunctionCFG{
                                                      signature = sign,
                                                      transitions = [],
                                                      states = [initState],
                                                      initial = initState,
                                                      end = [initState]
                                                  }
                                            --(newCFG, state) = (cfgStepWithStatement (BlockStatement block) cfg (initial cfg))
                                            --finalCFG = (addEndState newCFG state)
                                            --relevantModifierCFGs = respectiveModifierCFGs functionDefinitionTags modifierCFGs
                                            in Just cfg--Just (addModifiersControlFlow finalCFG relevantModifierCFGs)


parseFunctionCFG _ _ = Nothing

--------------------------------------------------------------
--------------------------------------------------------------

parseModifierCFG (ContractPartModifierDefinition modifierName maybeParameterList block) =
                                        let initState = BasicState (show 0)
                                            cfg = FunctionCFG{
                                                      signature = FunctionSignature{
                                                                        functionName = modifierName,
                                                                        functionVisibility = Nothing,
                                                                        parameters = case maybeParameterList of
                                                                                        Nothing -> ParameterList []
                                                                                        Just params -> params,
                                                                        returnParams = ParameterList []
                                                                    },
                                                      transitions = [],
                                                      states = [initState],
                                                      initial = initState,
                                                      end = []
                                                  }
                                            (newCFG, state) = (cfgStepWithStatement (BlockStatement block) cfg (initial cfg))
                                            in Just (addEndState newCFG state)

parseModifierCFG _ = Nothing

--------------------------------------------------------------
--------------------------------------------------------------
--FunctionDefinitionTagModifierInvocation ModifierInvocation
--data ModifierInvocation =
--  ModifierInvocation {
--    modifierInvocationIdentifier :: Identifier,
--    modifierInvocationParameters :: Maybe ExpressionList
--  } deriving (Show, Eq, Ord)

respectiveModifierCFGs :: [FunctionDefinitionTag] -> [FunctionCFG] -> [FunctionCFG]
respectiveModifierCFGs _ [] = []
respectiveModifierCFGs [] _ = []
respectiveModifierCFGs ftags cfgs = [c | c <- cfgs, (FunctionDefinitionTagModifierInvocation (ModifierInvocation id maybeParameters)) <- ftags, id == functionName (signature c)]

--------------------------------------------------------------
--------------------------------------------------------------

addModifiersControlFlow :: FunctionCFG -> [FunctionCFG] -> FunctionCFG
addModifiersControlFlow functionCFG [] = functionCFG
addModifiersControlFlow functionCFG (m:modifierCFGs) = let modifiedCFG = addModifierControlFlow (functionName (signature m)) functionCFG m
                                                           in addModifiersControlFlow modifiedCFG modifierCFGs
--------------------------------------------------------------
--------------------------------------------------------------

isPlaceholder :: State -> Bool
isPlaceholder (StatementState _ PlaceholderStatement) = True
isPlaceholder _ = False

addModifierControlFlow :: Identifier -> FunctionCFG -> FunctionCFG -> FunctionCFG
addModifierControlFlow (Identifier modifierName) functionCFG modifierCFG = let placeholderStates = [dst t | t <- transitions modifierCFG, isPlaceholder (src t)]
                                                    in addModifierControlFlowAtTransitions modifierName 0 placeholderStates functionCFG modifierCFG



addModifierControlFlowAtTransitions :: String -> Int -> [State] -> FunctionCFG -> FunctionCFG -> FunctionCFG
addModifierControlFlowAtTransitions modifierName prefix [s] functionCFG modifierCFG = addModifierControlFlowAtTransition (modifierName ++ show prefix) s functionCFG modifierCFG
addModifierControlFlowAtTransitions modifierName prefix (s:placeholderStates) functionCFG modifierCFG =
                                                            let cfg = addModifierControlFlowAtTransition (modifierName ++ (show (prefix))) s functionCFG modifierCFG
                                                            in addModifierControlFlowAtTransitions modifierName (prefix + 1) (placeholderStates) functionCFG cfg

--------------------------------------------------------------
--------------------------------------------------------------

addModifierControlFlowAtTransition :: String -> State -> FunctionCFG -> FunctionCFG -> FunctionCFG
addModifierControlFlowAtTransition prefix placeholderState functionCFG modifierCFG =
                                            let prependedCFG = prependStatementLabelsWith prefix functionCFG
                                                in replaceStateWithCFG modifierCFG placeholderState prependedCFG
                                        --        in FunctionCFG{
                                        --            signature = signature functionCFG,
                                        --            transitions = ((transitions modifierCFG) \\ [(Transition from to (Label PlaceholderStatement))])
                                        --                        ++ (transitions prependedCFG)
                                        --                        ++ [(Transition from (initial prependedCFG) TT)]
                                        --                        ++ [(Transition source to TT) | source <- (end prependedCFG)],
                                        --            states = (states modifierCFG) ++ (states prependedCFG),
                                        --            initial = initial modifierCFG,
                                        --            end = end modifierCFG
                                        --        }

--------------------------------------------------------------
--------------------------------------------------------------

prependStatementLabelsWith :: String -> FunctionCFG -> FunctionCFG
prependStatementLabelsWith prefix functionCFG = FunctionCFG{
                                                    signature = signature functionCFG,
                                                    transitions = [(Transition (prependStatementLabelWith prefix source) (prependStatementLabelWith prefix dest) ev) | Transition source dest ev <- transitions functionCFG],
                                                    states = [prependStatementLabelWith prefix state | state <- states functionCFG],
                                                    initial = prependStatementLabelWith prefix (initial functionCFG),
                                                    end = [prependStatementLabelWith prefix state | state <- end functionCFG]
                                            }
--------------------------------------------------------------
--------------------------------------------------------------

prependStatementLabelWith :: String -> State -> State
prependStatementLabelWith prefix (BasicState label) = BasicState (prefix ++ label)
prependStatementLabelWith prefix (FunctionCallState label functionName) = FunctionCallState (prefix ++ label) functionName
prependStatementLabelWith _ s = s
--------------------------------------------------------------
--------------------------------------------------------------
noStateChange (FunctionDefinitionTagStateMutability Pure) = True;
noStateChange (FunctionDefinitionTagStateMutability Constant) = True;
noStateChange (FunctionDefinitionTagStateMutability View) = True;
noStateChange _ = False;

--------------------------------------------------------------
--------------------------------------------------------------
--cfgFromFunction(Solidity.ContractPartFunctionDefinition identifier (ParameterList parameters) [FunctionDefinitionTag] _ (Just (Block statements))) =

--------------------------------------------------------------
--------------------------------------------------------------

addTransition :: FunctionCFG -> Transition -> FunctionCFG
addTransition cfg transition = FunctionCFG {
                                    signature = signature cfg,
                                    transitions = (transitions cfg) ++ [transition],
                                    states = states cfg,
                                    initial = initial cfg,
                                    end = end cfg
                                }

--------------------------------------------------------------
--------------------------------------------------------------

addTransitions :: FunctionCFG -> [Transition] -> FunctionCFG
addTransitions cfg trs = FunctionCFG {
                                    signature = signature cfg,
                                    transitions = (transitions cfg) ++ trs,
                                    states = states cfg,
                                    initial = initial cfg,
                                    end = end cfg
                                }

--------------------------------------------------------------
--------------------------------------------------------------

addState :: FunctionCFG -> State -> FunctionCFG
addState cfg state = let oldStates = states cfg
                                in FunctionCFG {
                                    signature = signature cfg,
                                    transitions = transitions cfg,
                                    states = oldStates ++ [state],
                                    initial = initial cfg,
                                    end = end cfg
                                }



--------------------------------------------------------------
--------------------------------------------------------------

addStates :: FunctionCFG -> [State] -> FunctionCFG
addStates cfg sts = let oldStates = states cfg
                                in FunctionCFG {
                                    signature = signature cfg,
                                    transitions = transitions cfg,
                                    states = oldStates ++ sts,
                                    initial = initial cfg,
                                    end = end cfg
                                }




--------------------------------------------------------------
--------------------------------------------------------------

addEndState :: FunctionCFG -> State -> FunctionCFG
addEndState cfg state = FunctionCFG {
                            signature = signature cfg,
                            transitions = transitions cfg,
                            states = states cfg,
                            initial = initial cfg,
                            end = (end cfg) ++ [state]
                        }

--------------------------------------------------------------
--------------------------------------------------------------

nextLabel :: FunctionCFG -> String
nextLabel cfg = show (length (states cfg))

--------------------------------------------------------------
--------------------------------------------------------------

currentLabel :: FunctionCFG -> String
currentLabel cfg = show ((length (states cfg)) - 1)
--------------------------------------------------------------
--------------------------------------------------------------

--Always add state to cfg in function that constructs the state

cfgStepWithExpressions :: [Expression] -> FunctionCFG -> State -> (FunctionCFG, State)
cfgStepWithExpressions [] cfg state = (cfg, state)
cfgStepWithExpressions (e:exps) cfg state = let (newCFG, newState) = cfgStepWithExpression e cfg state
                                                in cfgStepWithExpressions exps newCFG newState

--------------------------------------------------------------
--------------------------------------------------------------

cfgStepWithExpression :: Expression -> FunctionCFG -> State -> (FunctionCFG, State)
cfgStepWithExpression (Unary string expression) cfg state =
                        let expr = (Unary string expression)
                            (newCFG, newState) = cfgStepWithExpression expression cfg state
                            transition = Transition{src = newState, dst = ExpressionState (nextLabel newCFG) expr, event = TT}
                            cfgWithTransition = addTransition (addState newCFG (dst transition)) transition
                            in (cfgWithTransition, dst transition)


cfgStepWithExpression (Binary "=" expression1 expression2) cfg state =
                        let expr = Binary "=" expression1 expression2
                            (newCFG, newState) = cfgStepWithExpression expression2 cfg state
                            transition = Transition{src = newState, dst = ExpressionState (nextLabel newCFG) expr, event = TT}
                            cfgWithTransition = addTransition (addState newCFG (dst transition)) transition
                          in (cfgWithTransition, dst transition)

cfgStepWithExpression (Binary string expression1 expression2) cfg state =
                        let expr = Binary string expression1 expression2
                            (newCFG1, newState1) = cfgStepWithExpression expression1 cfg state
                            (newCFG, newState) = cfgStepWithExpression expression2 newCFG1 newState1
                            transition = Transition{src = newState, dst = ExpressionState (nextLabel newCFG) expr, event = TT}
                            cfgWithTransition = addTransition (addState newCFG (dst transition)) transition
                            in (cfgWithTransition, dst transition)

cfgStepWithExpression (Ternary string expression1 expression2 expression3) cfg state =
                        let expr = (Ternary string expression1 expression2 expression3)
                            (newCFG1, newState1) = cfgStepWithExpression expression1 cfg state
                            (newCFG2, newState2) = cfgStepWithExpression expression2 newCFG1 newState1
                            (newCFG, newState) = cfgStepWithExpression expression3 newCFG2 newState2
                            transition = Transition{src = newState, dst = ExpressionState (nextLabel newCFG) expr, event = TT}
                            cfgWithTransition = addTransition (addState newCFG (dst transition)) transition
                            in (cfgWithTransition, dst transition)


-- (FunctionCallNameValueList (Literal (PrimaryExpressionStringLiteral (StringLiteral functionName))) _) cfg state = addFunctionTransition (Identifier {unIdentifier = functionName}) cfg


cfgStepWithExpression (FunctionCallNameValueList (Literal (PrimaryExpressionIdentifier functionName)) (Just (NameValueList nameValueList))) cfg state =
                            let expressions = map (snd) nameValueList
                                (newCFG, newState) = cfgStepWithExpressions expressions cfg state
                                functionCall = FunctionCall functionName (Just (Left (NameValueList nameValueList)))
                            in addFunctionTransition functionCall newCFG newState

cfgStepWithExpression (FunctionCallNameValueList (Literal (PrimaryExpressionIdentifier functionName)) (Nothing)) cfg state =
                        let functionCall = FunctionCall functionName Nothing
                            in addFunctionTransition (functionCall) cfg state

cfgStepWithExpression (FunctionCallNameValueList (MemberAccess expression functionName) (Just (NameValueList nameValueList))) cfg state =
                            let expressions = map (snd) nameValueList
                                (newCFG, newState) = cfgStepWithExpressions expressions cfg state
                                functionCall = OutsideFunctionCall expression functionName (Just (Left (NameValueList nameValueList)))
                            in addFunctionTransition functionCall newCFG newState


cfgStepWithExpression (FunctionCallNameValueList (MemberAccess expression functionName) (Nothing)) cfg state =
                          let functionCall = OutsideFunctionCall expression functionName Nothing
                            in addFunctionTransition (functionCall) cfg state

--add transitions for each expression in name value list


cfgStepWithExpression (FunctionCallExpressionList (Literal (PrimaryExpressionIdentifier functionName)) Nothing) cfg state =
                        let functionCall = FunctionCall functionName Nothing
                            in addFunctionTransition (functionCall) cfg state

cfgStepWithExpression (FunctionCallExpressionList (Literal (PrimaryExpressionIdentifier functionName)) (Just expressionList)) cfg state =
                        let rawExpressionList = unExpressionList expressionList
                            (cfgWithList, stateAfterList) = cfgStepWithExpressions rawExpressionList cfg state
                            functionCall = FunctionCall functionName (Just (Right expressionList))
                           in addFunctionTransition (functionCall) cfgWithList stateAfterList


cfgStepWithExpression (FunctionCallExpressionList (MemberAccess expression functionName) Nothing) cfg state =
                        let (newCFG, newState) = cfgStepWithExpression expression cfg state
                            functionCall = OutsideFunctionCall expression functionName (Nothing)
                           in addFunctionTransition functionCall newCFG newState


cfgStepWithExpression (FunctionCallExpressionList (MemberAccess expression functionName) (Just expressionList)) cfg state =
                        let (newCFG, newState) = cfgStepWithExpression expression cfg state
                            rawExpressionList = unExpressionList expressionList
                            (cfgWithList, stateAfterList) = cfgStepWithExpressions rawExpressionList newCFG newState
                            functionCall = OutsideFunctionCall expression functionName (Just (Right expressionList))
                           in addFunctionTransition (functionCall) cfgWithList stateAfterList


-- Literal primaryExpression
-- New TypeName
cfgStepWithExpression expression cfg state = (cfg, state)

--------------------------------------------------------------
--------------------------------------------------------------

addFunctionTransition :: FunctionCall -> FunctionCFG -> State -> (FunctionCFG, State)
addFunctionTransition (FunctionCall functionName maybeParameters) cfg state  =
                        let entryTransition = Transition{src = state, dst = FunctionCallState{label = nextLabel cfg, functionCall = (FunctionCall functionName maybeParameters)}, event = TT}
                            cfgWithEntryTransition = (addState (addTransition cfg entryTransition) (dst entryTransition))
                        --    exitTransition = Transition{src = dst entryTransition, dst = BasicState{label = nextLabel cfgWithEntryTransition}, event = Exiting (FunctionCall functionName maybeParameters)}
                        --  cfgWithExitTransition = addState (addState (addTransition cfgWithEntryTransition exitTransition) (dst entryTransition)) (dst exitTransition)
                            in (cfgWithEntryTransition, dst entryTransition)

--OutsideFunctionCall Expression FunctionName (Maybe (Either NameValueList ExpressionList))

addFunctionTransition (OutsideFunctionCall expr functionName maybeParameters) cfg state  =
                                                    let entryTransition = Transition{src = state, dst = FunctionCallState{label = nextLabel cfg, functionCall = (OutsideFunctionCall expr functionName maybeParameters)}, event = TT}
                                                        cfgWithEntryTransition = (addState (addTransition cfg entryTransition) (dst entryTransition))
                                                --        exitTransition = Transition{src = dst entryTransition, dst = BasicState{label = nextLabel cfgWithEntryTransition}, event = Exiting (OutsideFunctionCall expr functionName maybeParameters)}
                                                    --    cfgWithExitTransition = addState (addState (addTransition cfgWithEntryTransition exitTransition) (dst entryTransition)) (dst exitTransition)
                                                        in (cfgWithEntryTransition, dst entryTransition)


--------------------------------------------------------------
--------------------------------------------------------------

cfgStepWithMaybeExpression :: Maybe Expression -> FunctionCFG -> State -> (FunctionCFG, State)
cfgStepWithMaybeExpression Nothing cfg state = (cfg, state)
cfgStepWithMaybeExpression (Just expression) cfg state = cfgStepWithExpression expression cfg state

--------------------------------------------------------------
--------------------------------------------------------------

cfgStepWithStatement :: Statement -> FunctionCFG -> State -> (FunctionCFG, State)
--cfgStepWithStatement Nothing cfg state = (cfg, state)



cfgStepWithStatement Throw cfg state =  let throwState = StatementState (nextLabel cfg) Throw
                                            transition = Transition{src = state, dst = throwState, event = TT}
                                            transition2 = Transition{src = throwState, dst = ThrowState, event = TT}
                                            in (addEndState (addStates (addTransitions cfg [transition, transition2]) [throwState, ThrowState]) ThrowState, ThrowState)

cfgStepWithStatement (Return Nothing) cfg state = let returnState = StatementState (nextLabel cfg) (Return Nothing)
                                                      transition = Transition{src = state, dst = returnState, event = TT}
                                                      transition2 = Transition{src = returnState, dst = ReturnState, event = TT}
                                                    in (addEndState (addStates (addTransitions cfg [transition, transition2]) [returnState, ReturnState]) ReturnState, ReturnState)

cfgStepWithStatement (Return (Just expr)) cfg state =
                    let (newCFG, newState) = cfgStepWithExpression expr cfg state
                        transition = Transition{src = newState, dst = StatementState (nextLabel newCFG) ((Return (Just expr))), event = TT}
                        in ((addEndState (addState (addTransition newCFG transition) (dst transition)) (dst transition)), (dst transition))



cfgStepWithStatement (SimpleStatementExpression expr) cfg state =
                    let (newCFG, newState) = cfgStepWithExpression expr cfg state
                        stState = (StatementState (currentLabel newCFG) (SimpleStatementExpression expr))
                      --  transition = Transition{src = newState, dst = StatementState (nextLabel newCFG) ((SimpleStatementExpression expr)), event = TT}
                        in if isFunctionCallState newState
                            then (newCFG, newState)
                            else (replaceStateWithState newCFG newState stState, stState)

cfgStepWithStatement (SimpleStatementVariableList identifierList (Just expr)) cfg state =
                    let (newCFG, newState) = cfgStepWithExpression expr cfg state
                        transition = Transition{src = newState, dst = StatementState (nextLabel newCFG) ((SimpleStatementVariableList identifierList (Just expr))), event = TT}
                        in ((addState (addTransition newCFG transition) (dst transition)), dst transition)

cfgStepWithStatement (SimpleStatementVariableList identifierList Nothing) cfg state =
                    let transition = Transition{src = state, dst = StatementState (nextLabel cfg) ((SimpleStatementVariableList identifierList Nothing)), event = TT}
                        in ((addState (addTransition cfg transition) (dst transition)), dst transition)

cfgStepWithStatement (SimpleStatementVariableDeclaration variableDeclaration Nothing) cfg state =
                    let transition = Transition{src = state, dst = StatementState (nextLabel cfg) ((SimpleStatementVariableDeclaration variableDeclaration Nothing)), event = TT}
                        in ((addState (addTransition cfg transition) (dst transition)), dst transition)

cfgStepWithStatement (SimpleStatementVariableDeclaration variableDeclaration (Just expr)) cfg state =
                     let (newCFG, newState) = cfgStepWithExpression expr cfg state
                         transition = Transition{src = newState, dst = StatementState (nextLabel newCFG) ((SimpleStatementVariableDeclaration variableDeclaration (Just expr))), event = TT}
                        in ((addState (addTransition newCFG transition) (dst transition)), dst transition)

cfgStepWithStatement (BlockStatement (Block [])) cfg state =  (cfg, state)
cfgStepWithStatement (BlockStatement (Block (s : statements))) cfg state =  let (newCFG, newState) = cfgStepWithStatement s cfg state
                        in cfgStepWithStatement (BlockStatement (Block statements)) newCFG newState

--can be optimized by ending in the end state of the true branch always, need to create another function with and end state parameter
cfgStepWithStatement (IfStatement expression ifTrueStatement maybeIfFalseStatement) cfg state =
    let (newCFG, newState) = cfgStepWithExpression expression cfg state
        ifStmt = (IfStatement expression ifTrueStatement maybeIfFalseStatement)
        transitionToIf = Transition{src = newState, dst = StatementState (nextLabel newCFG) (ifStmt), event = TT}

        transitionIfTrue = Transition{src = dst transitionToIf, dst = BasicState (nextLabel newCFG), event = ConditionHolds (ExpressionList [expression])}
        cfgWithTransition = addTransition (addStates newCFG [src transitionIfTrue, dst transitionIfTrue]) transitionIfTrue
        (cfgWithIfTrueBlock, ifTrueEndState) = (cfgStepWithStatement ifTrueStatement cfgWithTransition (dst transitionIfTrue))

        transitionIfFalse = Transition{src = dst transitionToIf, dst = BasicState (nextLabel newCFG), event = ConditionDoesNotHold (ExpressionList [expression])}
        cfgIfTrueWithTransition = addTransition (addState cfgWithIfTrueBlock (dst transitionIfFalse)) transitionIfFalse
        (cfgWithIfFalseBlock, ifFalseEndState) = if(maybeIfFalseStatement /= Nothing)
                                        then let Just s = maybeIfFalseStatement
                                                 in cfgStepWithStatement s cfgIfTrueWithTransition (dst transitionIfFalse)
                                        else (cfgIfTrueWithTransition, dst transitionIfFalse)
        bothEndState = BasicState (nextLabel cfgWithIfFalseBlock)
        cfgWithAllIfBlock = addTransition(addTransition cfgIfTrueWithTransition Transition{src = ifTrueEndState, dst = bothEndState, event = TT}) Transition{src = ifFalseEndState, dst = bothEndState, event = TT}
                        in ((addState cfgWithAllIfBlock bothEndState), bothEndState)


cfgStepWithStatement (WhileStatement expression statement) cfg startState =
                    let (newCFG, newState) = cfgStepWithExpression expression cfg startState
                        (branchingCFG, trueState, falseState) = cfgBranchOnConditionCheck expression newCFG newState
                        (cfgWithLoopBody, bodyEndState) = cfgFromStatementWithContinueAndBreak statement branchingCFG trueState newState falseState
                        transitionFromBodyEndState = Transition{src = bodyEndState, dst = newState, event = TT}
                        finishedCFG = addTransition cfgWithLoopBody transitionFromBodyEndState
                        in (finishedCFG, falseState)


-- DoWhileStatement Statement Expression


cfgStepWithStatement (DoWhileStatement statement expression) cfg startState =
                    let continueState = BasicState (nextLabel cfg)
                        cfgWithContinueState = addState cfg continueState
                        breakState = BasicState (nextLabel cfg)
                        cfgWithBreakState = addState cfgWithContinueState breakState --cfg with both continue and break states
                        (cfgWithStatement, endState) = cfgFromStatementWithContinueAndBreak statement cfgWithBreakState startState continueState breakState --CFG with body done once
                        (newCFG, newState) = cfgStepWithExpression expression cfgWithStatement endState --CFG checking condition
                        (branchingCFG, ifTrue, ifFalse) = cfgBranchOnConditionCheck expression newCFG newState
                        --TODO check if continueState and breakState are reachable, if not don't use them
                        --TODO can do step above manually, using break as false and continuestate as true
                        breakTransition = Transition{src = breakState, dst = ifFalse, event = TT}
                        continueTransition = Transition{src = continueState, dst = startState, event = TT}
                        connectingEndOfBlockTransition = Transition{src = ifTrue, dst = continueState, event = TT}
                        finishedCFG = addTransition (addTransition (addTransition branchingCFG breakTransition) continueTransition) connectingEndOfBlockTransition
                        in (finishedCFG, ifFalse)

-- ForStatement (Maybe Statement, Maybe Expression, Maybe Expression) Statement


--infinite loop
--cfgStepWithStatement (ForStatement Nothing Nothing Nothing) statement) cfg startState =
--                    let continueState = BasicState{label = nextLabel cfg}
--                        cfgWithContinueState = addState cfg continueState
--                        breakState = BasicState{label = nextLabel cfg}
--                        cfgWithBreakState = addState cfg breakState
--                        (cfgWithStatement, endState) = cfgFromStatementWithContinueAndBreak statement cfgWithBreakState startState continueState breakState
--                        loopTransition = Transition{src = endState, dst = startState, label = TT}
--                        finishedCFG = addTransition cfgWithStatement loopTransition
--                        in (finishedCFG, endState)




--cfgStepWithStatement (ForStatement Just statement1 expression1 Nothing) statement) cfg startState =
--                    let initialStatementState = BasicState{label = nextLabel cfg}
--                        cfgWithInitialStatementState = addState cfg initialStatementState
--                        initialTransition = Transition{src = startState, dst = initialStatementState, label = Statement statement1}
--                        cfgWithInitialTransition = addTransition cfgWithInitialStatementState initialTransition
--                        conditionTrueState = BasicState{label = nextLabel cfg}
--                        cfgWithTrueState = addState cfgWithInitialTransition conditionTrueState
--                        conditionCheckTrueTransition = Transition{src = initialStatementState, dst = conditionTrueState, label = ConditionHolds expression1}
--                        conditionFalseState = BasicState{label = nextLabel cfg}
--                        cfgWithFalseState = addState cfgWithTrueState conditionTrueState
--                        conditionCheckTrueTransition = Transition{src = initialStatementState, dst = conditionFalseState, label = ConditionDoesNotHold expression1}
--                        cfgWithTrueAndFalseTransitions = addTransition addTransition cfgWithFalseState conditionCheckTrueTransition conditionCheckTrueTransition
--                        (cfgWithStatement, endState) = cfgFromStatementWithContinueAndBreak statement cfgWithTrueAndFalseTransitions conditionTrueState initialStatementState endState
--                        endStateTTTransition = Transition{src = endState, dst = initialStatementState, label = TT}
--                        finishedCFG = addTransition cfgWithStatement endStateTTTransition
--                        in (finishedCFG, conditionFalseState)


cfgStepWithStatement (ForStatement (statement1, expression1, expression2) statement) cfg startState =
                    let (cfgWithStatement1, stateAfterInitialStatement) = cfgStepWithMaybeStatement statement1 cfg startState -- do first statement
                        (cfgWithExpression1, stateAfterConditionCheck) = cfgStepWithMaybeExpression expression1 cfgWithStatement1 stateAfterInitialStatement --check condition
                        conditionTrueState = BasicState (nextLabel cfgWithExpression1)
                        conditionCheckTrueTransition = Transition{src = stateAfterConditionCheck, dst = conditionTrueState, event = if(expression1 /= Nothing)
                                                            then let Just e = expression1
                                                                    in ConditionHolds (ExpressionList [e])
                                                            else TT}--no condition means true
                        cfgWithTrueState = addTransition (addState cfgWithExpression1 conditionTrueState) conditionCheckTrueTransition --add condition holds transition
                        conditionFalseState = BasicState (nextLabel cfgWithTrueState)
                        conditionCheckFalseTransition = Transition{src = stateAfterConditionCheck, dst = conditionFalseState, event = if(expression1 /= Nothing)
                                                          then let Just e = expression1
                                                                in ConditionDoesNotHold (ExpressionList [e])
                                                          else TT} --will not be added in this case
                        cfgWithFalseState = if(expression1 /= Nothing)
                                                then addTransition (addState cfgWithTrueState conditionTrueState) conditionCheckFalseTransition
                                                else cfgWithTrueState --condition is always true so no false transition
                        continueFromState = BasicState (nextLabel cfgWithFalseState) --state to take in case of continue
                        cfgWithContinueState = addState cfgWithFalseState continueFromState
                        (cfgWithStatement, endState) = cfgFromStatementWithContinueAndBreak statement cfgWithContinueState conditionTrueState continueFromState conditionFalseState
                        finishedCFG = if(endState == conditionFalseState) --if statement always end in break
                                        then cfgWithStatement --then existing CFG is enough
                                        else let fromEndToContinueTransition = Transition{src = endState, dst = continueFromState, event = TT}--else connect end state to continuefrom state (note that continuefrom may have been used in some banch of statement, thus why we do this)
                                                 cfgWithTransition = addTransition cfgWithStatement fromEndToContinueTransition
                                                 (cfgWithExpression2, afterExpression2State) = cfgStepWithMaybeExpression expression2 cfgWithTransition continueFromState --perform expression2 before checking expression1 again
                                                 transitionFromEndToStart = Transition{src = afterExpression2State, dst = stateAfterInitialStatement, event = TT}
                                                 in  addTransition cfgWithExpression2 transitionFromEndToStart
                        in (finishedCFG, conditionFalseState)

--Error because expression2 are MaybeExpression type
cfgStepWithStatement any cfg state =  let transition = Transition{src = state, dst = StatementState (nextLabel cfg) any, event = TT}
                        in ((addState (addTransitions cfg [transition]) (dst transition)), dst transition)
--------------------------------------------------------------
--------------------------------------------------------------

cfgStepWithMaybeStatement :: Maybe Statement -> FunctionCFG -> State -> (FunctionCFG, State)
cfgStepWithMaybeStatement Nothing cfg state = (cfg, state)
cfgStepWithMaybeStatement (Just statement) cfg state = cfgStepWithStatement statement cfg state

--------------------------------------------------------------
--------------------------------------------------------------
--handles continue in while and for
--continue jumps over one iteration of the loop
--break exits the loop

cfgBranchOnConditionCheck :: Expression -> FunctionCFG -> State -> (FunctionCFG, State, State)
cfgBranchOnConditionCheck expression cfg state =
                let conditionTrueState = BasicState (nextLabel cfg)
                    trueTransition = Transition{src = state, dst = conditionTrueState, event = ConditionHolds (ExpressionList [expression])}
                    cfgWithExpressionWithTrueState = addTransition (addState cfg conditionTrueState) trueTransition
                    conditionFalseState = BasicState (nextLabel cfgWithExpressionWithTrueState)
                    falseTransition = Transition{src = state, dst = conditionFalseState, event = ConditionDoesNotHold (ExpressionList [expression])}
                    cfgWithExpressionWithFalseState = addTransition (addState cfgWithExpressionWithTrueState conditionFalseState) falseTransition
                    in (cfgWithExpressionWithFalseState, conditionTrueState, conditionFalseState)

--------------------------------------------------------------
--------------------------------------------------------------

joinStates :: FunctionCFG -> State -> State -> (FunctionCFG, State)
joinStates cfg state1 state2 = let newEndState = BasicState (nextLabel cfg)
                                   transition1 = Transition{src = state1, dst = newEndState, event = TT}
                                   transition2 = Transition{src = state2, dst = newEndState, event = TT}
                                   newCFG = addTransition (addTransition (addState cfg newEndState) transition1) transition2
                                   in (newCFG, newEndState)

--------------------------------------------------------------
--------------------------------------------------------------

cfgFromStatementWithContinueAndBreak :: Statement -> FunctionCFG -> State -> State -> State -> (FunctionCFG, State)
cfgFromStatementWithContinueAndBreak (IfStatement expression statement maybeStatement) cfg startState continueFrom breakFrom =
                let (cfgWithExpression, afterExpression) = cfgStepWithExpression expression cfg startState
                    (cfgWithBranching, trueState, falseState) = cfgBranchOnConditionCheck expression cfgWithExpression afterExpression
                    (cfgWithStatement, endStateIfTrue) = cfgFromStatementWithContinueAndBreak statement cfgWithBranching trueState continueFrom breakFrom
                    (cfgWithStatementAndElse, endStateIfFalse) =
                                        if(maybeStatement /= Nothing)
                                        then let Just elseStmt = maybeStatement
                                                in cfgFromStatementWithContinueAndBreak elseStmt cfgWithStatement falseState continueFrom breakFrom
                                        else (cfgWithStatement, falseState)
                    in if(endStateIfFalse /= continueFrom && endStateIfFalse /= breakFrom)
                        then
                            if(endStateIfTrue /= continueFrom && endStateIfTrue /= breakFrom)
                            then joinStates cfgWithStatementAndElse endStateIfTrue endStateIfFalse
                            else (cfgWithStatementAndElse, endStateIfFalse)

                        else if(endStateIfTrue /= continueFrom && endStateIfTrue /= breakFrom)
                            then  (cfgWithStatementAndElse, endStateIfTrue)
                                else (cfgWithStatementAndElse, endStateIfFalse)


cfgFromStatementWithContinueAndBreak (BlockStatement (Block (Continue:statements))) cfg startState continueFrom _ =
                    cfgFromStatementWithContinueAndBreak Continue cfg startState continueFrom continueFrom

cfgFromStatementWithContinueAndBreak (BlockStatement (Block (Break:statements))) cfg startState _ breakTo =
                    cfgFromStatementWithContinueAndBreak Break cfg startState breakTo breakTo


cfgFromStatementWithContinueAndBreak (BlockStatement (Block (s:statements))) cfg startState continueFrom breakTo =
                    let (newCFG, newState) = cfgFromStatementWithContinueAndBreak s cfg startState continueFrom breakTo
                        in cfgFromStatementWithContinueAndBreak (BlockStatement (Block statements)) newCFG newState continueFrom breakTo

cfgFromStatementWithContinueAndBreak Continue cfg startState continueFrom _ =
                    let continueState = StatementState (nextLabel cfg) (Continue)
                        transition = Transition{src = startState, dst = continueState, event = TT}
                        transition2 = Transition{src = continueState, dst = continueFrom, event = TT}
                        in (addTransitions (addState cfg continueState) [transition,transition2], continueFrom)

cfgFromStatementWithContinueAndBreak Break cfg startState _ breakTo =
                    let breakState = StatementState (nextLabel cfg) (Break)
                        transition = Transition{src = startState, dst = breakState, event = TT}
                        transition2 = Transition{src = breakState, dst = breakTo, event = TT}
                        in (addTransitions (addState cfg breakState) [transition, transition2], breakTo)

cfgFromStatementWithContinueAndBreak statement cfg startState continueFrom breakTo = cfgStepWithStatement statement cfg startState

--------------------------------------------------------------
--------------------------------------------------------------

alphabet :: FunctionCFG -> [Label]
alphabet cfg = [event transition | transition <- (transitions cfg)]


--------------------------------------------------------------
--------------------------------------------------------------
--TODO
--need to handle function modifiers
--delegatecall and call not being parsed





--------------------------------------------------------------
--------------------------------------------------------------
--comparePropertyEventAndCFGLabel :: DEA.Event -> Label -> Bool

--------------------------------------------------------------
--------------------------------------------------------------

--TODO:
--function f() returns (uint i){i = 6;} is equivalent to function f() returns (uint){i = 6; return i;}

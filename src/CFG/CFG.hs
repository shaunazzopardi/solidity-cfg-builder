module CFG.CFG (State(..), Label(..), Transition(..), FunctionCFG(..), CFG(..), contractCFG, FunctionCall(..)) where

import Solidity.Solidity;
import Data.List
--import DEA.DEA;


data State = BasicState {
            label :: Int
            }
     | ThrowState
     | ReturnState
     | FunctionCallState {
        label :: Int,
        functionCall :: FunctionCall
        }
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

    
data Label = Label Statement | LabelE Expression | ConditionHolds Expression | ConditionDoesNotHold Expression | Tau | Any | ReturnLabel Expression | ReturnVoid | Entering FunctionCall | Exiting FunctionCall | Assert Expression | Require Expression deriving (Eq, Ord, Show)
    
data FunctionCall = FunctionCall FunctionName (Maybe (Either NameValueList ExpressionList)) deriving (Eq, Ord, Show)
  
data Transition =
  Transition {
      src, dst :: State,
      event :: Label
} deriving (Eq, Ord, Show)

data FunctionCFG = FunctionCFG{
    functionName :: String,
    transitions :: [Transition],
    states :: [State],
    initial :: State,
    end :: [State]
} deriving (Eq, Ord, Show)

data CFG = CFG [FunctionCFG]

--------------------------------------------------------------
--------------------------------------------------------------

contractCFG :: SolidityCode -> CFG
contractCFG (SolidityCode (SourceUnit sourceUnits)) = 
                                let functionCFGs = map (contractCFGFromContractDefinition) sourceUnits
                                    functionCFGsFlattened = foldr (++) [] functionCFGs
                                    in CFG (map (handleAssertAndRequires functionCFGsFlattened) functionCFGsFlattened)
--contractCFG _ = CFG []
--------------------------------------------------------------
--------------------------------------------------------------

handleAssertAndRequires :: [FunctionCFG] -> FunctionCFG -> FunctionCFG
handleAssertAndRequires (cfgs) cfg = let requireStates = [FunctionCallState label (FunctionCall (Identifier "require") params ) | FunctionCallState label (FunctionCall (Identifier "require") params ) <- (states cfg), not (requireIsOverridden cfgs)]
                                         assertStates = [FunctionCallState label (FunctionCall (Identifier "assert") params ) | FunctionCallState label (FunctionCall (Identifier "assert") params ) <- (states cfg), not (assertIsOverridden cfgs)]
                                         newCFGWithAssertAndRequire = functionCallStatesToAssertOrRequire (requireStates ++ assertStates) cfg
                                       in newCFGWithAssertAndRequire

--------------------------------------------------------------
--------------------------------------------------------------

assertIsOverridden :: [FunctionCFG] -> Bool
assertIsOverridden [] = False
assertIsOverridden (cfg:cfgs) = if((functionName cfg) == "assert")
                                    then True
                                    else assertIsOverridden cfgs

requireIsOverridden :: [FunctionCFG] -> Bool
requireIsOverridden [] = False
requireIsOverridden (cfg:cfgs) = if((functionName cfg) == "require")
                                    then True
                                    else requireIsOverridden cfgs

--------------------------------------------------------------
--------------------------------------------------------------
--data FunctionCall = FunctionCall FunctionName (Maybe (Either NameValueList ExpressionList)) deriving (Eq, Ord, Show)

functionCallStatesToAssertOrRequire :: [State] -> FunctionCFG -> FunctionCFG
functionCallStatesToAssertOrRequire [] cfg = cfg
functionCallStatesToAssertOrRequire (s:ss) cfg = let newCFG = functionCallToAssertOrRequire s cfg
                                                    in functionCallStatesToAssertOrRequire ss newCFG
                                                                          
functionCallToAssertOrRequire :: State -> FunctionCFG -> FunctionCFG
functionCallToAssertOrRequire (FunctionCallState label functionCall) cfg =let uponEntryTransition = [t | t <- (transitions cfg), (dst t) == (FunctionCallState label functionCall)]
                                                                              uponExitTransition = [t | t <- (transitions cfg), (src t) == (FunctionCallState label functionCall)]
                                                                              partialNewTransitions = (((transitions cfg) \\ uponEntryTransition) \\ uponExitTransition)
                                                                              partialNewStates = ((states cfg) \\ [FunctionCallState label functionCall])
                                                                              newCFG = FunctionCFG{
                                                                                           functionName = functionName cfg,
                                                                                           transitions = partialNewTransitions,
                                                                                           states = partialNewStates,
                                                                                           initial = initial cfg,
                                                                                           end = end cfg
                                                                                       }
                                                                    in if(length uponEntryTransition == 1 && length uponExitTransition == 1)
                                                                          then let source = src $ head uponEntryTransition
                                                                                   end = dst $ head uponExitTransition
                                                                                   newNewCFG = cfgStepWithAssertOrRequire functionCall newCFG source end
                                                                                  in if(newNewCFG == newCFG)
                                                                                        then cfg
                                                                                        else newNewCFG
                                                                          else cfg--consider transitioning to error state

                                                                          
--------------------------------------------------------------
--------------------------------------------------------------

cfgStepWithAssertOrRequire :: FunctionCall -> FunctionCFG -> State -> State -> FunctionCFG
cfgStepWithAssertOrRequire (FunctionCall (Identifier "require") (Just (Right (ExpressionList [expression])))) cfg startState endState = 
                                     cfgStepWithRequire expression cfg startState endState

cfgStepWithAssertOrRequire (FunctionCall (Identifier "assert") (Just (Right (ExpressionList [expression])))) cfg startState endState = 
                                     cfgStepWithAssert expression cfg startState endState

cfgStepWithAssertOrRequire _ newCFG startState endState = newCFG                         
--------------------------------------------------------------
--------------------------------------------------------------

cfgStepWithAssert :: Expression -> FunctionCFG -> State -> State -> FunctionCFG
cfgStepWithAssert expr cfg startState endState = 
                    let (newCFG, newState) = (cfg, startState)--cfgStepWithExpression expr cfg startState
                        transition1 = Transition{src = newState, dst = BasicState (nextLabel cfg), event = Assert expr}
                        transition2 = Transition{src = (dst transition1), dst = ThrowState, event = ConditionDoesNotHold expr}          
                        newCFG2 = addState (addTransition (addState (addTransition newCFG transition2) (dst transition2)) transition1) (dst transition1)
                        transition3 = Transition{src = dst transition1, dst = endState, event = ConditionHolds expr}
                        newCfgWithThrowing = (addState (addTransition newCFG2 transition3) (dst transition3)) 
                        in newCfgWithThrowing
          
cfgStepWithRequire :: Expression -> FunctionCFG -> State -> State -> FunctionCFG          
cfgStepWithRequire expr cfg startState endState = 
                    let (newCFG, newState) = (cfg, startState)--cfgStepWithExpression expr cfg startState
                        transition1 = Transition{src = newState, dst = BasicState (nextLabel cfg), event = Require expr}
                        transition2 = Transition{src = (dst transition1), dst = ThrowState, event = ConditionDoesNotHold expr}                 
                        newCFG2 = addState (addTransition (addState (addTransition newCFG transition2) (dst transition2)) transition1) (dst transition1)
                        transition3 = Transition{src = dst transition1, dst = endState, event = ConditionHolds expr}
                        newCfgWithThrowing = addState (addTransition newCFG2 transition3) (dst transition3)
                        in newCfgWithThrowing



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

contractCFGFromContractDefinition :: SourceUnit1 -> [FunctionCFG]
contractCFGFromContractDefinition (SourceUnit1_ContractDefinition contractDefinition) = 
                                            let cfgs = contractParts contractDefinition
                                                in justifyList (map (contractPartCFG) cfgs)
contractCFGFromContractDefinition _ = []
--------------------------------------------------------------
--------------------------------------------------------------

justifyList :: [Maybe FunctionCFG] -> [FunctionCFG]
justifyList [] = []
justifyList ((Just functionCFG):rest) = functionCFG:(justifyList rest)
justifyList ((Nothing):rest) = justifyList rest

--------------------------------------------------------------
--------------------------------------------------------------

contractPartCFG :: ContractPart -> Maybe FunctionCFG
contractPartCFG (ContractPartFunctionDefinition (Just identifier) _ _ (_) (Just block)) = 
                                        let cfg = FunctionCFG{
                                                      functionName = unIdentifier identifier,
                                                      transitions = [],
                                                      states = [BasicState 0],
                                                      initial = BasicState 0,
                                                      end = []
                                                  }
                                            (newCFG, state) = (cfgStepWithStatement (BlockStatement block) cfg (initial cfg))
                                            in Just (addEndState newCFG state)

contractPartCFG _ = Nothing

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
                                    functionName = functionName cfg,
                                    transitions = (transitions cfg) ++ [transition],
                                    states = states cfg,
                                    initial = initial cfg,
                                    end = end cfg
                                }

--------------------------------------------------------------
--------------------------------------------------------------

addState :: FunctionCFG -> State -> FunctionCFG
addState cfg state = let oldStates = states cfg
                                in FunctionCFG {
                                    functionName = functionName cfg,
                                    transitions = transitions cfg,
                                    states = oldStates ++ [state],
                                    initial = initial cfg,
                                    end = end cfg
                                }

--------------------------------------------------------------
--------------------------------------------------------------

addEndState :: FunctionCFG -> State -> FunctionCFG
addEndState cfg state = FunctionCFG {
                            functionName = functionName cfg,
                            transitions = transitions cfg,
                            states = states cfg,
                            initial = initial cfg,
                            end = (end cfg) ++ [state]
                        }

--------------------------------------------------------------
--------------------------------------------------------------

nextLabel cfg = length (states cfg)
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
                        let (newCFG, newState) = cfgStepWithExpression expression cfg state
                            transition = Transition{src = newState, dst=BasicState{label = nextLabel newCFG}, event = LabelE (Unary string expression)}
                            cfgWithTransition = addTransition (addState newCFG (dst transition)) transition
                            in (cfgWithTransition, dst transition)

cfgStepWithExpression (Binary string expression1 expression2) cfg state = 
                        let (newCFG1, newState1) = cfgStepWithExpression expression1 cfg state
                            (newCFG, newState) = cfgStepWithExpression expression2 newCFG1 newState1
                            transition = Transition{src = newState, dst=BasicState{label = nextLabel newCFG}, event = LabelE (Binary string expression1 expression2)}
                            cfgWithTransition = addTransition (addState newCFG (dst transition)) transition
                            in (cfgWithTransition, dst transition)

cfgStepWithExpression (Ternary string expression1 expression2 expression3) cfg state =
                        let (newCFG1, newState1) = cfgStepWithExpression expression1 cfg state
                            (newCFG2, newState2) = cfgStepWithExpression expression2 newCFG1 newState1
                            (newCFG, newState) = cfgStepWithExpression expression3 newCFG2 newState2
                            transition = Transition{src = newState, dst=BasicState{label = nextLabel newCFG}, event = LabelE (Ternary string expression1 expression2 expression3)}
                            cfgWithTransition = addTransition (addState newCFG (dst transition)) transition
                            in (cfgWithTransition, dst transition)


-- (FunctionCallNameValueList (Literal (PrimaryExpressionStringLiteral (StringLiteral functionName))) _) cfg state = addFunctionTransition (Identifier {unIdentifier = functionName}) cfg 

cfgStepWithExpression (FunctionCallNameValueList (Literal (PrimaryExpressionIdentifier functionName)) (Just (NameValueList nameValueList))) cfg state =
                            let expressions = map (snd) nameValueList
                                (newCFG, newState) = cfgStepWithExpressions expressions cfg state
                                functionCall = FunctionCall functionName (Just (Left (NameValueList nameValueList)))
                            in addFunctionTransition functionCall newCFG newState

cfgStepWithExpression (FunctionCallNameValueList (Literal (PrimaryExpressionIdentifier functionName)) (Nothing)) cfg state =  let functionCall = FunctionCall functionName Nothing
                            in addFunctionTransition (functionCall) cfg state

cfgStepWithExpression (FunctionCallNameValueList (MemberAccess expression functionName) (Just (NameValueList nameValueList))) cfg state =
                            let expressions = map (snd) nameValueList
                                (newCFG, newState) = cfgStepWithExpressions expressions cfg state
                                functionCall = FunctionCall functionName (Just (Left (NameValueList nameValueList)))
                            in addFunctionTransition functionCall newCFG newState

                            
cfgStepWithExpression (FunctionCallNameValueList (MemberAccess expression functionName) (Nothing)) cfg state = let functionCall = FunctionCall functionName Nothing
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
                            functionCall = FunctionCall functionName (Nothing)
                           in addFunctionTransition functionCall newCFG newState


cfgStepWithExpression (FunctionCallExpressionList (MemberAccess expression functionName) (Just expressionList)) cfg state =                            
                        let (newCFG, newState) = cfgStepWithExpression expression cfg state
                            rawExpressionList = unExpressionList expressionList
                            (cfgWithList, stateAfterList) = cfgStepWithExpressions rawExpressionList newCFG newState
                            functionCall = FunctionCall functionName (Just (Right expressionList))
                           in addFunctionTransition (functionCall) cfgWithList stateAfterList

                           
-- Literal primaryExpression  
-- New TypeName                         
cfgStepWithExpression expression cfg state = (cfg, state)
                           
--------------------------------------------------------------
--------------------------------------------------------------
                           
addFunctionTransition :: FunctionCall -> FunctionCFG -> State -> (FunctionCFG, State)
addFunctionTransition (FunctionCall functionName maybeParameters) cfg state  = 
                        let entryTransition = Transition{src = state, dst = FunctionCallState{label = nextLabel cfg, functionCall = (FunctionCall functionName maybeParameters)}, event = Entering (FunctionCall functionName maybeParameters)}
                            cfgWithEntryTransition = addTransition cfg entryTransition
                            exitTransition = Transition{src = dst entryTransition, dst = BasicState{label = nextLabel cfgWithEntryTransition}, event = Exiting (FunctionCall functionName maybeParameters)}
                            cfgWithExitTransition = addState (addState (addTransition cfgWithEntryTransition exitTransition) (dst entryTransition)) (dst exitTransition)
                            in (cfgWithExitTransition, dst exitTransition)
                            

--------------------------------------------------------------
--------------------------------------------------------------

cfgStepWithMaybeExpression :: Maybe Expression -> FunctionCFG -> State -> (FunctionCFG, State)
cfgStepWithMaybeExpression Nothing cfg state = (cfg, state)
cfgStepWithMaybeExpression (Just expression) cfg state = cfgStepWithExpression expression cfg state

--------------------------------------------------------------
--------------------------------------------------------------
                            
cfgStepWithStatement :: Statement -> FunctionCFG -> State -> (FunctionCFG, State)
--cfgStepWithStatement Nothing cfg state = (cfg, state)
                        
                        

cfgStepWithStatement Throw cfg state =  let transition = Transition{src = state, dst = ThrowState, event = Label Throw} 
                        in (addEndState (addState (addTransition cfg transition) ThrowState) ThrowState, ThrowState)
                        
cfgStepWithStatement (Return Nothing) cfg state =
                    let transition = Transition{src = state, dst = ReturnState, event = ReturnVoid}
                        in (addEndState (addState (addTransition cfg transition) ReturnState) ReturnState, ReturnState)
                        
cfgStepWithStatement (Return (Just expr)) cfg state =  
                    let (newCFG, newState) = cfgStepWithExpression expr cfg state
                        transition = Transition{src = newState, dst = BasicState{label = nextLabel newCFG}, event = (ReturnLabel expr)}
                        in ((addEndState (addState (addTransition newCFG transition) (dst transition)) (dst transition)), (dst transition))

cfgStepWithStatement (SimpleStatementExpression expr) cfg state = cfgStepWithExpression expr cfg state

cfgStepWithStatement (SimpleStatementVariableList identifierList (Just expr)) cfg state = 
                    let (newCFG, newState) = cfgStepWithExpression expr cfg state
                        transition = Transition{src = newState, dst = BasicState{label = nextLabel newCFG}, event = Label (SimpleStatementVariableList identifierList (Just expr))}
                        in ((addState (addTransition newCFG transition) (dst transition)), dst transition)
                        
cfgStepWithStatement (SimpleStatementVariableList identifierList Nothing) cfg state = 
                    let transition = Transition{src = state, dst = BasicState{label = nextLabel cfg}, event = Label (SimpleStatementVariableList identifierList (Nothing))}
                        in ((addState (addTransition cfg transition) (dst transition)), dst transition)
                        
cfgStepWithStatement (SimpleStatementVariableDeclaration variableDeclaration Nothing) cfg state = 
                    let transition = Transition{src = state, dst = BasicState{label = nextLabel cfg},   event = Label (SimpleStatementVariableDeclaration variableDeclaration (Nothing))}
                        in ((addState (addTransition cfg transition) (dst transition)), dst transition)
                        
cfgStepWithStatement (SimpleStatementVariableDeclaration variableDeclaration (Just expr)) cfg state = 
                     let (newCFG, newState) = cfgStepWithExpression expr cfg state
                         transition = Transition{src = newState, dst = BasicState{label = nextLabel newCFG}, event = Label (SimpleStatementVariableDeclaration variableDeclaration (Just expr))}
                        in ((addState (addTransition newCFG transition) (dst transition)), dst transition)
                        
cfgStepWithStatement (BlockStatement (Block [])) cfg state =  (cfg, state)
cfgStepWithStatement (BlockStatement (Block (s : statements))) cfg state =  let (newCFG, newState) = cfgStepWithStatement s cfg state
                        in cfgStepWithStatement (BlockStatement (Block statements)) newCFG newState 

--can be optimized by ending in the end state of the true branch always, need to create another function with and end state parameter
cfgStepWithStatement (IfStatement expression ifTrueStatement maybeIfFalseStatement) cfg state =  
    let (newCFG, newState) = cfgStepWithExpression expression cfg state
        transitionIfTrue = Transition{src = newState, dst = BasicState{label = nextLabel newCFG}, event = ConditionHolds expression} 
        cfgWithTransition = addTransition (addState newCFG (dst transitionIfTrue)) transitionIfTrue
        (cfgWithIfTrueBlock, ifTrueEndState) = (cfgStepWithStatement ifTrueStatement cfgWithTransition (dst transitionIfTrue))
        
        transitionIfFalse = Transition{src = newState, dst = BasicState{label = nextLabel cfgWithIfTrueBlock}, event = ConditionDoesNotHold expression} 
        cfgIfTrueWithTransition = addTransition (addState cfgWithIfTrueBlock (dst transitionIfFalse)) transitionIfFalse
        (cfgWithIfFalseBlock, ifFalseEndState) = if(maybeIfFalseStatement /= Nothing)
                                        then let Just s = maybeIfFalseStatement
                                                 in cfgStepWithStatement s cfgIfTrueWithTransition (dst transitionIfFalse)
                                        else (cfgIfTrueWithTransition, dst transitionIfFalse)
        bothEndState = BasicState{label = nextLabel cfgWithIfFalseBlock}
        cfgWithAllIfBlock = addTransition(addTransition cfgIfTrueWithTransition Transition{src = ifTrueEndState, dst = bothEndState, event = Tau}) Transition{src = ifFalseEndState, dst = bothEndState, event = Tau}
                        in ((addState cfgWithAllIfBlock bothEndState), bothEndState)

                    
cfgStepWithStatement (WhileStatement expression statement) cfg startState =  
                    let (newCFG, newState) = cfgStepWithExpression expression cfg startState
                        (branchingCFG, trueState, falseState) = cfgBranchOnConditionCheck expression newCFG newState
                        (cfgWithLoopBody, bodyEndState) = cfgFromStatementWithContinueAndBreak statement branchingCFG trueState newState falseState 
                        transitionFromBodyEndState = Transition{src = bodyEndState, dst = newState, event = Tau}
                        finishedCFG = addTransition cfgWithLoopBody transitionFromBodyEndState
                        in (finishedCFG, falseState)


-- DoWhileStatement Statement Expression
                        
                    
cfgStepWithStatement (DoWhileStatement statement expression) cfg startState =  
                    let continueState = BasicState{label = nextLabel cfg}
                        cfgWithContinueState = addState cfg continueState
                        breakState = BasicState{label = nextLabel cfg}
                        cfgWithBreakState = addState cfgWithContinueState breakState --cfg with both continue and break states
                        (cfgWithStatement, endState) = cfgFromStatementWithContinueAndBreak statement cfgWithBreakState startState continueState breakState --CFG with body done once
                        (newCFG, newState) = cfgStepWithExpression expression cfgWithStatement endState --CFG checking condition
                        (branchingCFG, ifTrue, ifFalse) = cfgBranchOnConditionCheck expression newCFG newState
                        --TODO check if continueState and breakState are reachable, if not don't use them
                        --TODO can do step above manually, using break as false and continuestate as true
                        breakTransition = Transition{src = breakState, dst = ifFalse, event = Tau}
                        continueTransition = Transition{src = continueState, dst = startState, event = Tau}
                        connectingEndOfBlockTransition = Transition{src = ifTrue, dst = continueState, event = Tau}
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
--                        loopTransition = Transition{src = endState, dst = startState, label = Tau}
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
--                        endStateTauTransition = Transition{src = endState, dst = initialStatementState, label = Tau}
--                        finishedCFG = addTransition cfgWithStatement endStateTauTransition
--                        in (finishedCFG, conditionFalseState)  
                        
                        
cfgStepWithStatement (ForStatement (statement1, expression1, expression2) statement) cfg startState =  
                    let (cfgWithStatement1, stateAfterInitialStatement) = cfgStepWithMaybeStatement statement1 cfg startState -- do first statement
                        (cfgWithExpression1, stateAfterConditionCheck) = cfgStepWithMaybeExpression expression1 cfgWithStatement1 stateAfterInitialStatement --check condition
                        conditionTrueState = BasicState{label = nextLabel cfgWithExpression1}
                        conditionCheckTrueTransition = Transition{src = stateAfterConditionCheck, dst = conditionTrueState, event = if(expression1 /= Nothing) 
                                                            then let Just e = expression1
                                                                    in ConditionHolds e
                                                            else Tau}--no condition means true
                        cfgWithTrueState = addTransition (addState cfgWithExpression1 conditionTrueState) conditionCheckTrueTransition --add condition holds transition
                        conditionFalseState = BasicState{label = nextLabel cfgWithTrueState}
                        conditionCheckFalseTransition = Transition{src = stateAfterConditionCheck, dst = conditionFalseState, event = if(expression1 /= Nothing) 
                                                          then let Just e = expression1
                                                                in ConditionDoesNotHold e
                                                          else Tau} --will not be added in this case
                        cfgWithFalseState = if(expression1 /= Nothing) 
                                                then addTransition (addState cfgWithTrueState conditionTrueState) conditionCheckFalseTransition 
                                                else cfgWithTrueState --condition is always true so no false transition
                        continueFromState = BasicState{label = nextLabel cfgWithFalseState} --state to take in case of continue
                        cfgWithContinueState = addState cfgWithFalseState continueFromState
                        (cfgWithStatement, endState) = cfgFromStatementWithContinueAndBreak statement cfgWithContinueState conditionTrueState continueFromState conditionFalseState
                        finishedCFG = if(endState == conditionFalseState) --if statement always end in break
                                        then cfgWithStatement --then existing CFG is enough
                                        else let fromEndToContinueTransition = Transition{src = endState, dst = continueFromState, event = Tau}--else connect end state to continuefrom state (note that continuefrom may have been used in some banch of statement, thus why we do this)
                                                 cfgWithTransition = addTransition cfgWithStatement fromEndToContinueTransition 
                                                 (cfgWithExpression2, afterExpression2State) = cfgStepWithMaybeExpression expression2 cfgWithTransition continueFromState --perform expression2 before checking expression1 again
                                                 transitionFromEndToStart = Transition{src = afterExpression2State, dst = stateAfterInitialStatement, event = Tau}
                                                 in  addTransition cfgWithExpression2 transitionFromEndToStart
                        in (finishedCFG, conditionFalseState) 
                        
--Error because expression2 are MaybeExpression type
cfgStepWithStatement any cfg state =  let transition = Transition{src = state, dst = BasicState{label = nextLabel cfg}, event = Label any} 
                        in ((addState (addTransition cfg transition) (dst transition)), dst transition)
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
                let conditionTrueState = BasicState{label = nextLabel cfg}
                    trueTransition = Transition{src = state, dst = conditionTrueState, event = ConditionHolds expression}
                    cfgWithExpressionWithTrueState = addTransition (addState cfg conditionTrueState) trueTransition
                    conditionFalseState = BasicState{label = nextLabel cfgWithExpressionWithTrueState}
                    falseTransition = Transition{src = state, dst = conditionFalseState, event = ConditionDoesNotHold expression}
                    cfgWithExpressionWithFalseState = addTransition (addState cfgWithExpressionWithTrueState conditionFalseState) falseTransition
                    in (cfgWithExpressionWithFalseState, conditionTrueState, conditionFalseState)

--------------------------------------------------------------
--------------------------------------------------------------

joinStates :: FunctionCFG -> State -> State -> (FunctionCFG, State)
joinStates cfg state1 state2 = let newEndState = BasicState{label = nextLabel cfg}
                                   transition1 = Transition{src = state1, dst = newEndState, event = Tau}
                                   transition2 = Transition{src = state2, dst = newEndState, event = Tau}
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
                    let transition = Transition{src = startState, dst = continueFrom, event = Label Continue}
                        in (addTransition cfg transition, continueFrom)

cfgFromStatementWithContinueAndBreak (BlockStatement (Block (Break:statements))) cfg startState _ breakTo = 
                    let transition = Transition{src = startState, dst = breakTo, event = Label Break}
                        in (addTransition cfg transition, breakTo)
  
                        
cfgFromStatementWithContinueAndBreak (BlockStatement (Block (s:statements))) cfg startState continueFrom breakTo = 
                    let (newCFG, newState) = cfgFromStatementWithContinueAndBreak s cfg startState continueFrom breakTo
                        in cfgFromStatementWithContinueAndBreak (BlockStatement (Block statements)) newCFG newState continueFrom breakTo

cfgFromStatementWithContinueAndBreak Continue cfg startState continueFrom _ = 
                    let transition = Transition{src = startState, dst = continueFrom, event = Label Continue}
                        in (addTransition cfg transition, continueFrom)
                        
cfgFromStatementWithContinueAndBreak Break cfg startState _ breakTo = 
                    let transition = Transition{src = startState, dst = breakTo, event = Label Continue}
                        in (addTransition cfg transition, breakTo)

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

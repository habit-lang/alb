{-# LANGUAGE FlexibleContexts #-}
module Typechecker.TypeInference (inferTypes, emptyTypeInferenceState, ClassEnv(..), Binding(..), to, (@@), doTrace) where

import Common
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Solver (SolverEnv)
import Syntax.Common
import Syntax.IMPEG
import Syntax.IMPEG.TSubst (emptyUnifier)
import qualified Syntax.XMPEG as X

import Typechecker.TypeInference.Base
import Typechecker.TypeInference.Expr
import Typechecker.TypeInference.Instances
import Typechecker.TypeInference.TopDecl

----------------------------------------------------------------------------------------------------

type TcPassState = (ClassEnv, TyEnv, CtorEnv, BitdataCtorEnv, BitdataBDDEnv, StructRegionEnv, [RequirementT])

emptyTypeInferenceState :: TcPassState
emptyTypeInferenceState = ( ClassEnv ([], [], [], Map.empty, []) Map.empty Map.empty Map.empty
                          , Map.empty  -- type environment
                          , Map.empty  -- constructor environment
                          , Map.empty  -- bitdata constructor environment
                          , Map.empty  -- bitdata BDDs environment
                          , Map.empty  -- structure environment
                          , []
                          )

inferTypes :: Has s TcPassState => String -> Pass s (Program Pred KId KId) (X.Program KId, (Map Id (X.Scheme X.Type, Int), SolverEnv))
inferTypes fn = up (\p -> PassM (StateT (\globals@(classEnv, tyEnv, ctorEnv, bitdataCtors, bitdataBDDs, structRegions, requirementTemplates) ->
                                             do ((p', xctors, tyEnv'), TcState _ ctorEnv' classEnv' _ _ bitdataCtors' bitdataBDDs' structRegions' requirementTemplates') <-
                                                    runStateT (runM (checkProgram fn p))
                                                                  (TcState tyEnv ctorEnv classEnv ([], []) emptyUnifier bitdataCtors bitdataBDDs structRegions requirementTemplates)
                                                return ((p', (xctors, solverEnvironment classEnv')),
                                                        (classEnv', Map.union tyEnv tyEnv', ctorEnv', bitdataCtors', bitdataBDDs', structRegions', requirementTemplates')))))

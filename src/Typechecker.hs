module Typechecker (inferKinds, inferTypes, cleanupProgram, emptyKindInferenceState, emptyTypeInferenceState) where

import Typechecker.Cleanup
import Typechecker.TypeInference.Instances
import Typechecker.KindInference
import Typechecker.TypeInference
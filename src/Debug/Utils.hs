module Debug.Utils (trace, traceV, traceIf, traceMsg) where

import Debug.Trace

-- Trace the value
traceV :: (Show s) => s -> s
traceV x = trace (show x) x

-- Trace if the boolean is true
traceIf :: Bool -> String -> a -> a
traceIf True = trace
traceIf False = const id

-- trace the value with a custom message in front of it
traceMsg :: (Show s) => String -> s -> s
traceMsg str x = trace (str ++ ": " ++ show x) x


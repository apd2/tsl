-- Namespace type class

{-# LANGUAGE MultiParamTypeClasses #-}

module NS(NS, StaticNS) where

import Name
import Pos

class NS a b where
    lookup :: a -> Selector -> b

class StaticNS a b where
    slookup :: a -> Ident -> b

--class Ctx a where
--    lookup :: a -> Path -> GlobalPath

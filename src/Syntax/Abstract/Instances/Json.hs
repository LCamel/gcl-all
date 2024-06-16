module Syntax.Abstract.Instances.Json where

import           Syntax.Abstract.Types
import           Data.Aeson                     ( FromJSON
                                                , ToJSON
                                                )

instance ToJSON Endpoint
instance ToJSON Interval
instance ToJSON TBase
instance ToJSON Type
instance ToJSON Expr
instance ToJSON Chain
instance ToJSON FuncClause 
instance ToJSON CaseClause
instance ToJSON Pattern
instance ToJSON Lit

instance FromJSON Expr
instance FromJSON Chain
instance FromJSON FuncClause 
instance FromJSON CaseClause
instance FromJSON Pattern
instance FromJSON Lit

module Experiment.LambdaCalculusMapping.TH where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

atoz = pure <$> ['a'..'z']
oneOrTwo = atoz ++ ((++) <$> atoz <*> atoz)

genNames :: [String] -> Q [Dec]
genNames names = concat <$> mapM f names'
    where
        names' :: [String]
        names' = filter (\n -> not $ n `elem` ["do", "if", "in", "of"]) names

        f name = do
            nameStr <- lift name
            let e = AppE (VarE $ mkName "fromString") nameStr
            aTyVar <- newName "a"
            let sig = SigD (mkName name) $ ForallT [PlainTV aTyVar] [AppT (ConT $ mkName "IsString") (VarT aTyVar)] (VarT aTyVar)
            let def = FunD (mkName name) [Clause [] (NormalB e) []]
            return [sig, def]

genSingleNames :: [Char] -> Q [Dec]
genSingleNames = genNames . map pure

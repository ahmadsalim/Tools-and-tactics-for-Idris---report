{-# LANGUAGE NoMonomorphismRestriction #-}
module Parse where

import Text.Trifecta
import Control.Applicative
import Text.Parser.Char


landCode = string "+45"

phoneNumber = option "" landCode *> count 8 digit

username = many alphaNum

login = do id <- try phoneNumber <|> username
           string "--"
           password <- some alphaNum
           return (id, password)

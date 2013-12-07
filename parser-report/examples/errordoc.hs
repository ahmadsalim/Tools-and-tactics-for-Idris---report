{- | Parses an accessibilty modifier (e.g. public, private) -}
accessibility :: IdrisParser Accessibility
accessibility = do reserved "public";   return Public
            <|> do reserved "abstract"; return Frozen
            <|> do reserved "private";  return Hidden
            <?> "accessibility modifier"

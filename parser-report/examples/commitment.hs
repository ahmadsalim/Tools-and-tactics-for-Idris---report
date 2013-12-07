decl' :: SyntaxInfo -> IdrisParser PDecl
decl' syn =    try fixity
           <|> try (fnDecl' syn)
           <|> try (data_ syn)
           <|> try (record syn)
           <|> try (syntaxDecl syn)
           <?> "declaration"

decl' :: SyntaxInfo -> IdrisParser PDecl
decl' syn =    fixity
           <|> syntaxDecl syn
           <|> fnDecl' syn
           <|> data_ syn
           <|> record syn
           <?> "declaration"

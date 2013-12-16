elabEliminator :: [Int] -> Name -> PTerm -> [(String, Name, PTerm, FC)] -> ElabInfo -> EliminatorState ()
elabEliminator paramPos n ty cons info = do
  elimLog $ "Elaborating eliminator"
  let (cnstrs, _) = splitPi ty
  let (splittedTy@(pms, idxs)) = splitPms cnstrs
  generalParams <- namePis False pms
  motiveIdxs    <- namePis False idxs
  let motive = mkMotive n paramPos generalParams motiveIdxs
  consTerms <- mapM (\(c@(_,cnm,_,_)) -> do
                              name <- freshName $ "elim_" ++ simpleName cnm
                              consTerm <- extractConsTerm c generalParams
                              return (name, expl, consTerm)) cons
  scrutineeIdxs <- namePis False idxs
  let motiveConstr = [(motiveName, expl, motive)]
  let scrutinee = (scrutineeName, expl, applyCons n (interlievePos paramPos generalParams scrutineeIdxs 0))
  let eliminatorTy = piConstr (generalParams ++ motiveConstr ++ consTerms ++ scrutineeIdxs ++ [scrutinee])
        (applyMotive (map (\(n,_,_) -> PRef elimFC n) scrutineeIdxs) (PRef elimFC scrutineeName))
  let eliminatorTyDecl = PTy (show n) defaultSyntax elimFC [TotalFn] elimDeclName eliminatorTy
  let clauseConsElimArgs = map getPiName consTerms
  let clauseGeneralArgs' = map getPiName generalParams ++ [motiveName] ++ clauseConsElimArgs
  let clauseGeneralArgs  = map (\arg -> pexp (PRef elimFC arg)) clauseGeneralArgs'
  let elimSig = "-- eliminator signature: " ++ showImp Nothing True True eliminatorTy
  eliminatorClauses <- mapM (\(cns, cnsElim) -> generateEliminatorClauses cns cnsElim clauseGeneralArgs generalParams)
    (zip cons clauseConsElimArgs)
  let eliminatorDef = PClauses emptyFC [TotalFn] elimDeclName eliminatorClauses
  elimLog $ "-- eliminator definition: " ++ showDeclImp True eliminatorDef
  Control.Monad.State.lift $ idrisCatch (elabDecl EAll info eliminatorTyDecl) (\err -> return ())
  -- Do not elaborate clauses if there aren't any
  case eliminatorClauses of
    [] -> return ()
    _  -> Control.Monad.State.lift $ idrisCatch (elabDecl EAll info eliminatorDef) (\err -> return ())
  where elimLog :: String -> EliminatorState ()
        elimLog s = Control.Monad.State.lift (logLvl 2 s)

        elimFC :: FC
        elimFC = fileFC "(eliminator)"

        elimDeclName :: Name
        elimDeclName = SN $ ElimN n

        applyNS :: Name -> [String] -> Name
        applyNS n []  = n
        applyNS n ns  = NS n ns

        splitPi :: PTerm -> ([(Name, Plicity, PTerm)], PTerm)
        splitPi = splitPi' []
          where splitPi' :: [(Name, Plicity, PTerm)] -> PTerm -> ([(Name, Plicity, PTerm)], PTerm)
                splitPi' acc (PPi pl n tyl tyr) = splitPi' ((n, pl, tyl):acc) tyr
                splitPi' acc t                  = (reverse acc, t)

        splitPms :: [(Name, Plicity, PTerm)] -> ([(Name, Plicity, PTerm)], [(Name, Plicity, PTerm)])
        splitPms cnstrs = (map fst pms, map fst idxs)
           where (pms, idxs) = partition (\c -> snd c `elem` paramPos) (zip cnstrs [0..])

        isMachineGenerated :: Name -> Bool
        isMachineGenerated (MN _ _) = True
        isMachineGenerated _        = False

        namePis :: Bool -> [(Name, Plicity, PTerm)] -> EliminatorState [(Name, Plicity, PTerm)]
        namePis keepOld pms = do names <- mapM (mkPiName keepOld) pms
                                 let oldNames = map fst names
                                 let params   = map snd names
                                 return $ map (\(n, pl, ty) -> (n, pl, removeParamPis oldNames params ty)) params

        mkPiName :: Bool -> (Name, Plicity, PTerm) -> EliminatorState (Name, (Name, Plicity, PTerm))
        mkPiName keepOld (n, pl, piarg) | not (isMachineGenerated n) && keepOld = do return (n, (n, pl, piarg))
        mkPiName _ (oldName, pl, piarg) =  do name <- freshName $ keyOf piarg
                                              return (oldName, (name, pl, piarg))
          where keyOf :: PTerm -> String
                keyOf (PRef _ name) | isLetter (nameStart name) = (toLower $ nameStart name):"__"
                keyOf (PApp _ tyf _) = keyOf tyf
                keyOf PType = "ty__"
                keyOf _     = "carg__"
                nameStart :: Name -> Char
                nameStart n = nameStart' (simpleName n)
                  where nameStart' :: String -> Char
                        nameStart' "" = ' '
                        nameStart' ns = head ns

        simpleName :: Name -> String
        simpleName (NS n _) = simpleName n
        simpleName (MN i n) = n ++ show i
        simpleName n        = show n

        nameSpaces :: Name -> [String]
        nameSpaces (NS _ ns) = ns
        nameSpaces _         = []

        freshName :: String -> EliminatorState Name
        freshName key = do
          nameMap <- get
          let i = fromMaybe 0 (Map.lookup key nameMap)
          let name = key ++ show i
          put $ Map.insert key (i+1) nameMap
          return (UN name)

        scrutineeName :: Name
        scrutineeName = UN "scrutinee"

        scrutineeArgName :: Name
        scrutineeArgName = UN "scrutineeArg"

        motiveName :: Name
        motiveName = UN "prop"

        mkMotive :: Name -> [Int] -> [(Name, Plicity, PTerm)] -> [(Name, Plicity, PTerm)] -> PTerm
        mkMotive n paramPos params indicies =
          let scrutineeTy = (scrutineeArgName, expl, applyCons n (interlievePos paramPos params indicies 0))
          in piConstr (indicies ++ [scrutineeTy]) PType

        piConstr :: [(Name, Plicity, PTerm)] -> PTerm -> PTerm
        piConstr [] ty = ty
        piConstr ((n, pl, tyb):tyr) ty = PPi pl n tyb (piConstr tyr ty)

        interlievePos :: [Int] -> [a] -> [a] -> Int -> [a]
        interlievePos idxs []     l2     i = l2
        interlievePos idxs l1     []     i = l1
        interlievePos idxs (x:xs) l2     i | i `elem` idxs = x:(interlievePos idxs xs l2 (i+1))
        interlievePos idxs l1     (y:ys) i = y:(interlievePos idxs l1 ys (i+1))

        replaceParams :: [Int] -> [(Name, Plicity, PTerm)] -> PTerm -> PTerm
        replaceParams paramPos params cns =
          let (_, cnsResTy) = splitPi cns
          in case cnsResTy of
               PApp _ _ args ->
                let oldParams = paramNamesOf 0 paramPos args
                in removeParamPis oldParams params cns
               _ -> cns

        removeParamPis :: [Name] -> [(Name, Plicity, PTerm)] -> PTerm -> PTerm
        removeParamPis oldParams params (PPi pl n tyb tyr) =
          case findIndex (== n) oldParams of
            Nothing -> (PPi pl n (removeParamPis oldParams params tyb) (removeParamPis oldParams params tyr))
            Just i  -> (removeParamPis oldParams params tyr)
        removeParamPis oldParams params (PRef _ n) = 
          case findIndex (== n) oldParams of
               Nothing -> (PRef elimFC n)
               Just i  -> let (newname,_,_) = params !! i in (PRef elimFC (newname))
        removeParamPis oldParams params (PApp _ cns args) =
          PApp elimFC (removeParamPis oldParams params cns) $ replaceParamArgs args
            where replaceParamArgs :: [PArg] -> [PArg]
                  replaceParamArgs []          = []
                  replaceParamArgs (arg:args)  =
                    case extractName (getTm arg) of
                      []   -> arg:replaceParamArgs args
                      [n]  ->
                        case findIndex (== n) oldParams of
                          Nothing -> arg:replaceParamArgs args
                          Just i  -> let (newname,_,_) = params !! i
                            in arg {getTm = PRef elimFC newname}:replaceParamArgs args
        removeParamPis oldParams params t = t

        paramNamesOf :: Int -> [Int] -> [PArg] -> [Name]
        paramNamesOf i paramPos []          = []
        paramNamesOf i paramPos (arg:args)  =
          (if i `elem` paramPos then extractName (getTm arg) else []) 
            ++ paramNamesOf (i+1) paramPos args

        extractName :: PTerm -> [Name]
        extractName (PRef _ n) = [n]
        extractName _          = []

        splitArgPms :: PTerm -> ([PTerm], [PTerm])
        splitArgPms (PApp _ f args) = splitArgPms' args
          where splitArgPms' :: [PArg] -> ([PTerm], [PTerm])
                splitArgPms' cnstrs = (map (getTm . fst) pms, map (getTm . fst) idxs)
                    where (pms, idxs) = partition (\c -> snd c `elem` paramPos) (zip cnstrs [0..])
        splitArgPms _                 = ([],[])


        implicitIndexes :: (String, Name, PTerm, FC) -> EliminatorState [(Name, Plicity, PTerm)]
        implicitIndexes (cns@(doc, cnm, ty, fc)) = do
          i <-  Control.Monad.State.lift getIState
          implargs' <- case lookupCtxt cnm (idris_implicits i) of
            [] -> do fail $ "Error while showing implicits for " ++ show cnm
            [args] -> do return args
            _ -> do fail $ "Ambigous name for " ++ show cnm
          let implargs = mapMaybe convertImplPi implargs'
          let (_, cnsResTy) = splitPi ty
          case cnsResTy of
             PApp _ _ args ->
              let oldParams = paramNamesOf 0 paramPos args
              in return $ filter (\(n,_,_) -> not (n `elem` oldParams))implargs
             _ -> return implargs

        extractConsTerm :: (String, Name, PTerm, FC) -> [(Name, Plicity, PTerm)] -> EliminatorState PTerm
        extractConsTerm (doc, cnm, ty, fc) generalParameters = do
          let cons' = replaceParams paramPos generalParameters ty
          let (args, resTy) = splitPi cons'
          implidxs <- implicitIndexes (doc, cnm, ty, fc)
          consArgs <- namePis True args
          let recArgs = findRecArgs consArgs
          let recMotives = map applyRecMotive recArgs
          let (_, consIdxs) = splitArgPms resTy
          return $ piConstr (implidxs ++ consArgs ++ recMotives) (applyMotive consIdxs (applyCons cnm consArgs))
            where applyRecMotive :: (Name, Plicity, PTerm) -> (Name, Plicity, PTerm)
                  applyRecMotive (n,_,ty)  = (UN $ "ih" ++ simpleName n, expl, applyMotive idxs (PRef elimFC n))
                      where (_, idxs) = splitArgPms ty

        findRecArgs :: [(Name, Plicity, PTerm)] -> [(Name, Plicity, PTerm)]
        findRecArgs []                            = []
        findRecArgs (ty@(_,_,PRef _ tn):rs)            | simpleName tn == simpleName n = ty:findRecArgs rs
        findRecArgs (ty@(_,_,PApp _ (PRef _ tn) _):rs) | simpleName tn == simpleName n = ty:findRecArgs rs
        findRecArgs (ty:rs)                                                            = findRecArgs rs

        applyCons :: Name -> [(Name, Plicity, PTerm)] -> PTerm
        applyCons tn targs = PApp elimFC (PRef elimFC tn) (map convertArg targs)

        convertArg :: (Name, Plicity, PTerm) -> PArg
        convertArg (n, _, _)      = pexp (PRef elimFC n)

        applyMotive :: [PTerm] -> PTerm -> PTerm
        applyMotive idxs t = PApp elimFC (PRef elimFC motiveName) (map pexp idxs ++ [pexp t])

        getPiName :: (Name, Plicity, PTerm) -> Name
        getPiName (name,_,_) = name

        convertImplPi :: PArg -> Maybe (Name, Plicity, PTerm)
        convertImplPi (PImp {getTm = t, pname = n}) = Just (n, expl, t)
        convertImplPi _                             = Nothing

        generateEliminatorClauses :: (String, Name, PTerm, FC) -> Name ->
                  [PArg] -> [(Name, Plicity, PTerm)] -> EliminatorState PClause
        generateEliminatorClauses (doc, cnm, ty, fc) 
            cnsElim generalArgs generalParameters = do
          let cons' = replaceParams paramPos generalParameters ty
          let (args, resTy) = splitPi cons'
          i <- Control.Monad.State.lift getIState
          implidxs <- implicitIndexes (doc, cnm, ty, fc)
          let (_, generalIdxs') = splitArgPms resTy
          let generalIdxs = map pexp generalIdxs'
          consArgs <- namePis True args
          let lhsPattern = PApp elimFC (PRef elimFC elimDeclName) 
              (generalArgs ++ generalIdxs ++ [pexp $ applyCons cnm consArgs])
          let recArgs = findRecArgs consArgs
          let recElims = map applyRecElim recArgs
          let rhsExpr    = PApp elimFC (PRef elimFC cnsElim) 
              (map convertArg implidxs ++ map convertArg consArgs ++ recElims)
          return $ PClause elimFC elimDeclName lhsPattern [] rhsExpr []
            where applyRecElim :: (Name, Plicity, PTerm) -> PArg
                  applyRecElim (constr@(recCnm,_,recTy)) = pexp $ PApp elimFC (PRef elimFC elimDeclName) 
                              (generalArgs ++ map pexp idxs ++ [pexp $ PRef elimFC recCnm])
                    where (_, idxs) = splitArgPms recTy


induction :: Name -> RunTactic
induction nm ctxt env (Bind x (Hole t) (P _ x' _)) | x == x' = do
  (tmv, tmt) <- lift $ check ctxt env (Var nm)
  let tmt' = normalise ctxt env tmt
  case unApply tmt' of
    (P _ tnm _, pms@[]) -> do
        case lookupTy (SN (ElimN tnm)) ctxt of
          [elimTy] -> do
             let args     = getArgTys elimTy
             let pmargs   = take (length pms) args
             let args'    = drop (length pms) args
             let propTy   = head args'
             let consargs = init $ tail args'
             let scr      = last $ tail args'
             let prop = Bind nm (Lam tmt') t
             let res = substV prop $ bindConsArgs consargs
                  (mkApp (P Ref (SN (ElimN tnm)) (TType (UVal 0))) ([prop] ++ map makeConsArg consargs ++ [tmv]))
             action (\ps -> ps {holes = holes ps \\ [x]})
             mapM_ addConsHole (reverse consargs)
             let res' = forget $ res
             (scv, sct) <- lift $ check ctxt env res'
             let scv' = specialise ctxt env [] scv
             return scv'
          [] -> fail $ "Induction needs an eliminator for " ++ show nm
          xs -> fail $ "Multiple definitions found when searching for the eliminator of " ++ show nm
    (P _ nm _, _) -> fail "Induction not yet supported for types with arguments"
    _ -> fail "Unkown type for induction"
    where scname = MN 0 "scarg"
          makeConsArg (nm, ty) = P Bound nm ty
          bindConsArgs ((nm, ty):args) v = Bind nm (Hole ty) $ bindConsArgs args v
          bindConsArgs [] v = v
          addConsHole (nm, ty) =
            action (\ps -> ps { holes = nm : holes ps })
induction tm ctxt env _ = do fail "Can't do induction here"

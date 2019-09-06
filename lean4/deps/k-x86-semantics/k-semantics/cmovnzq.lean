def cmovnzq1 : instruction :=
  definst "cmovnzq" $ do
    pattern fun (v_3190 : reg (bv 64)) (v_3191 : reg (bv 64)) => do
      v_4956 <- getRegister zf;
      v_4958 <- getRegister v_3190;
      v_4959 <- getRegister v_3191;
      setRegister (lhs.of_reg v_3191) (mux (notBool_ v_4956) v_4958 v_4959);
      pure ()
    pat_end;
    pattern fun (v_3186 : Mem) (v_3187 : reg (bv 64)) => do
      v_8220 <- getRegister zf;
      v_8222 <- evaluateAddress v_3186;
      v_8223 <- load v_8222 8;
      v_8224 <- getRegister v_3187;
      setRegister (lhs.of_reg v_3187) (mux (notBool_ v_8220) v_8223 v_8224);
      pure ()
    pat_end

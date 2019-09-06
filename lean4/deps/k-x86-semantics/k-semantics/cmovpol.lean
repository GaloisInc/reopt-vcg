def cmovpol1 : instruction :=
  definst "cmovpol" $ do
    pattern fun (v_3274 : reg (bv 32)) (v_3275 : reg (bv 32)) => do
      v_5039 <- getRegister pf;
      v_5041 <- getRegister v_3274;
      v_5042 <- getRegister v_3275;
      setRegister (lhs.of_reg v_3275) (mux (notBool_ v_5039) v_5041 v_5042);
      pure ()
    pat_end;
    pattern fun (v_3267 : Mem) (v_3270 : reg (bv 32)) => do
      v_8276 <- getRegister pf;
      v_8278 <- evaluateAddress v_3267;
      v_8279 <- load v_8278 4;
      v_8280 <- getRegister v_3270;
      setRegister (lhs.of_reg v_3270) (mux (notBool_ v_8276) v_8279 v_8280);
      pure ()
    pat_end

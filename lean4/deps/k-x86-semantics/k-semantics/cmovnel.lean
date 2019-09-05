def cmovnel1 : instruction :=
  definst "cmovnel" $ do
    pattern fun (v_2917 : reg (bv 32)) (v_2918 : reg (bv 32)) => do
      v_4705 <- getRegister zf;
      v_4708 <- getRegister v_2917;
      v_4709 <- getRegister v_2918;
      setRegister (lhs.of_reg v_2918) (mux (notBool_ (eq v_4705 (expression.bv_nat 1 1))) v_4708 v_4709);
      pure ()
    pat_end;
    pattern fun (v_2910 : Mem) (v_2913 : reg (bv 32)) => do
      v_8230 <- getRegister zf;
      v_8233 <- evaluateAddress v_2910;
      v_8234 <- load v_8233 4;
      v_8235 <- getRegister v_2913;
      setRegister (lhs.of_reg v_2913) (mux (notBool_ (eq v_8230 (expression.bv_nat 1 1))) v_8234 v_8235);
      pure ()
    pat_end

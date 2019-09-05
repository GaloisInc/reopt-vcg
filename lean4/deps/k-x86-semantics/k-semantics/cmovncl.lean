def cmovncl1 : instruction :=
  definst "cmovncl" $ do
    pattern fun (v_2890 : reg (bv 32)) (v_2891 : reg (bv 32)) => do
      v_4672 <- getRegister cf;
      v_4675 <- getRegister v_2890;
      v_4676 <- getRegister v_2891;
      setRegister (lhs.of_reg v_2891) (mux (notBool_ (eq v_4672 (expression.bv_nat 1 1))) v_4675 v_4676);
      pure ()
    pat_end;
    pattern fun (v_2883 : Mem) (v_2886 : reg (bv 32)) => do
      v_8206 <- getRegister cf;
      v_8209 <- evaluateAddress v_2883;
      v_8210 <- load v_8209 4;
      v_8211 <- getRegister v_2886;
      setRegister (lhs.of_reg v_2886) (mux (notBool_ (eq v_8206 (expression.bv_nat 1 1))) v_8210 v_8211);
      pure ()
    pat_end

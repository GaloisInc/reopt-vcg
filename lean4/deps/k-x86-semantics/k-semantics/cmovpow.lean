def cmovpow1 : instruction :=
  definst "cmovpow" $ do
    pattern fun (v_3263 : reg (bv 16)) (v_3264 : reg (bv 16)) => do
      v_5160 <- getRegister pf;
      v_5163 <- getRegister v_3263;
      v_5164 <- getRegister v_3264;
      setRegister (lhs.of_reg v_3264) (mux (notBool_ (eq v_5160 (expression.bv_nat 1 1))) v_5163 v_5164);
      pure ()
    pat_end;
    pattern fun (v_3258 : Mem) (v_3259 : reg (bv 16)) => do
      v_8565 <- getRegister pf;
      v_8568 <- evaluateAddress v_3258;
      v_8569 <- load v_8568 2;
      v_8570 <- getRegister v_3259;
      setRegister (lhs.of_reg v_3259) (mux (notBool_ (eq v_8565 (expression.bv_nat 1 1))) v_8569 v_8570);
      pure ()
    pat_end

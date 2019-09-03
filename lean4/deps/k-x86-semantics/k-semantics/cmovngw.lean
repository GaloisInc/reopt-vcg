def cmovngw1 : instruction :=
  definst "cmovngw" $ do
    pattern fun (v_2923 : reg (bv 16)) (v_2924 : reg (bv 16)) => do
      v_4750 <- getRegister zf;
      v_4752 <- getRegister sf;
      v_4754 <- getRegister of;
      v_4759 <- getRegister v_2923;
      v_4760 <- getRegister v_2924;
      setRegister (lhs.of_reg v_2924) (mux (bit_or (eq v_4750 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4752 (expression.bv_nat 1 1)) (eq v_4754 (expression.bv_nat 1 1))))) v_4759 v_4760);
      pure ()
    pat_end;
    pattern fun (v_2920 : Mem) (v_2919 : reg (bv 16)) => do
      v_8329 <- getRegister zf;
      v_8331 <- getRegister sf;
      v_8333 <- getRegister of;
      v_8338 <- evaluateAddress v_2920;
      v_8339 <- load v_8338 2;
      v_8340 <- getRegister v_2919;
      setRegister (lhs.of_reg v_2919) (mux (bit_or (eq v_8329 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8331 (expression.bv_nat 1 1)) (eq v_8333 (expression.bv_nat 1 1))))) v_8339 v_8340);
      pure ()
    pat_end

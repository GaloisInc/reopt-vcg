def cmovcw1 : instruction :=
  definst "cmovcw" $ do
    pattern fun (v_2524 : reg (bv 16)) (v_2525 : reg (bv 16)) => do
      v_4208 <- getRegister cf;
      v_4210 <- getRegister v_2524;
      v_4211 <- getRegister v_2525;
      setRegister (lhs.of_reg v_2525) (mux (eq v_4208 (expression.bv_nat 1 1)) v_4210 v_4211);
      pure ()
    pat_end;
    pattern fun (v_2521 : Mem) (v_2520 : reg (bv 16)) => do
      v_7928 <- getRegister cf;
      v_7930 <- evaluateAddress v_2521;
      v_7931 <- load v_7930 2;
      v_7932 <- getRegister v_2520;
      setRegister (lhs.of_reg v_2520) (mux (eq v_7928 (expression.bv_nat 1 1)) v_7931 v_7932);
      pure ()
    pat_end

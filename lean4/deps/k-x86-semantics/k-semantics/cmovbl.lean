def cmovbl1 : instruction :=
  definst "cmovbl" $ do
    pattern fun (v_2479 : reg (bv 32)) (v_2480 : reg (bv 32)) => do
      v_4158 <- getRegister cf;
      v_4160 <- getRegister v_2479;
      v_4161 <- getRegister v_2480;
      setRegister (lhs.of_reg v_2480) (mux (eq v_4158 (expression.bv_nat 1 1)) v_4160 v_4161);
      pure ()
    pat_end;
    pattern fun (v_2475 : Mem) (v_2476 : reg (bv 32)) => do
      v_7893 <- getRegister cf;
      v_7895 <- evaluateAddress v_2475;
      v_7896 <- load v_7895 4;
      v_7897 <- getRegister v_2476;
      setRegister (lhs.of_reg v_2476) (mux (eq v_7893 (expression.bv_nat 1 1)) v_7896 v_7897);
      pure ()
    pat_end

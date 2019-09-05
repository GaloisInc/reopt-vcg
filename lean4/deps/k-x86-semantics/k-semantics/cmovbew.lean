def cmovbew1 : instruction :=
  definst "cmovbew" $ do
    pattern fun (v_2534 : reg (bv 16)) (v_2535 : reg (bv 16)) => do
      v_4209 <- getRegister cf;
      v_4211 <- getRegister zf;
      v_4214 <- getRegister v_2534;
      v_4215 <- getRegister v_2535;
      setRegister (lhs.of_reg v_2535) (mux (bit_or (eq v_4209 (expression.bv_nat 1 1)) (eq v_4211 (expression.bv_nat 1 1))) v_4214 v_4215);
      pure ()
    pat_end;
    pattern fun (v_2525 : Mem) (v_2526 : reg (bv 16)) => do
      v_7869 <- getRegister cf;
      v_7871 <- getRegister zf;
      v_7874 <- evaluateAddress v_2525;
      v_7875 <- load v_7874 2;
      v_7876 <- getRegister v_2526;
      setRegister (lhs.of_reg v_2526) (mux (bit_or (eq v_7869 (expression.bv_nat 1 1)) (eq v_7871 (expression.bv_nat 1 1))) v_7875 v_7876);
      pure ()
    pat_end

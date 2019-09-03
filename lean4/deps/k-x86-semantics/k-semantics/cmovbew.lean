def cmovbew1 : instruction :=
  definst "cmovbew" $ do
    pattern fun (v_2470 : reg (bv 16)) (v_2471 : reg (bv 16)) => do
      v_4145 <- getRegister cf;
      v_4147 <- getRegister zf;
      v_4150 <- getRegister v_2470;
      v_4151 <- getRegister v_2471;
      setRegister (lhs.of_reg v_2471) (mux (bit_or (eq v_4145 (expression.bv_nat 1 1)) (eq v_4147 (expression.bv_nat 1 1))) v_4150 v_4151);
      pure ()
    pat_end;
    pattern fun (v_2463 : Mem) (v_2462 : reg (bv 16)) => do
      v_7883 <- getRegister cf;
      v_7885 <- getRegister zf;
      v_7888 <- evaluateAddress v_2463;
      v_7889 <- load v_7888 2;
      v_7890 <- getRegister v_2462;
      setRegister (lhs.of_reg v_2462) (mux (bit_or (eq v_7883 (expression.bv_nat 1 1)) (eq v_7885 (expression.bv_nat 1 1))) v_7889 v_7890);
      pure ()
    pat_end

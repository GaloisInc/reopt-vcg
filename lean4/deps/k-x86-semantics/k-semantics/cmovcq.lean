def cmovcq1 : instruction :=
  definst "cmovcq" $ do
    pattern fun (v_2579 : reg (bv 64)) (v_2580 : reg (bv 64)) => do
      v_4262 <- getRegister cf;
      v_4264 <- getRegister v_2579;
      v_4265 <- getRegister v_2580;
      setRegister (lhs.of_reg v_2580) (mux (eq v_4262 (expression.bv_nat 1 1)) v_4264 v_4265);
      pure ()
    pat_end;
    pattern fun (v_2574 : Mem) (v_2575 : reg (bv 64)) => do
      v_7907 <- getRegister cf;
      v_7909 <- evaluateAddress v_2574;
      v_7910 <- load v_7909 8;
      v_7911 <- getRegister v_2575;
      setRegister (lhs.of_reg v_2575) (mux (eq v_7907 (expression.bv_nat 1 1)) v_7910 v_7911);
      pure ()
    pat_end

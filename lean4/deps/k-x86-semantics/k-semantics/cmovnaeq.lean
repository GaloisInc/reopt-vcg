def cmovnaeq1 : instruction :=
  definst "cmovnaeq" $ do
    pattern fun (v_2815 : reg (bv 64)) (v_2816 : reg (bv 64)) => do
      v_4508 <- getRegister cf;
      v_4509 <- getRegister v_2815;
      v_4510 <- getRegister v_2816;
      setRegister (lhs.of_reg v_2816) (mux v_4508 v_4509 v_4510);
      pure ()
    pat_end;
    pattern fun (v_2811 : Mem) (v_2812 : reg (bv 64)) => do
      v_7901 <- getRegister cf;
      v_7902 <- evaluateAddress v_2811;
      v_7903 <- load v_7902 8;
      v_7904 <- getRegister v_2812;
      setRegister (lhs.of_reg v_2812) (mux v_7901 v_7903 v_7904);
      pure ()
    pat_end

def cmovnlq1 : instruction :=
  definst "cmovnlq" $ do
    pattern fun (v_3058 : reg (bv 64)) (v_3059 : reg (bv 64)) => do
      v_4819 <- getRegister sf;
      v_4820 <- getRegister of;
      v_4822 <- getRegister v_3058;
      v_4823 <- getRegister v_3059;
      setRegister (lhs.of_reg v_3059) (mux (eq v_4819 v_4820) v_4822 v_4823);
      pure ()
    pat_end;
    pattern fun (v_3054 : Mem) (v_3055 : reg (bv 64)) => do
      v_8131 <- getRegister sf;
      v_8132 <- getRegister of;
      v_8134 <- evaluateAddress v_3054;
      v_8135 <- load v_8134 8;
      v_8136 <- getRegister v_3055;
      setRegister (lhs.of_reg v_3055) (mux (eq v_8131 v_8132) v_8135 v_8136);
      pure ()
    pat_end

def cmovcl1 : instruction :=
  definst "cmovcl" $ do
    pattern fun (v_2572 : reg (bv 32)) (v_2573 : reg (bv 32)) => do
      v_4252 <- getRegister cf;
      v_4254 <- getRegister v_2572;
      v_4255 <- getRegister v_2573;
      setRegister (lhs.of_reg v_2573) (mux (eq v_4252 (expression.bv_nat 1 1)) v_4254 v_4255);
      pure ()
    pat_end;
    pattern fun (v_2565 : Mem) (v_2568 : reg (bv 32)) => do
      v_7900 <- getRegister cf;
      v_7902 <- evaluateAddress v_2565;
      v_7903 <- load v_7902 4;
      v_7904 <- getRegister v_2568;
      setRegister (lhs.of_reg v_2568) (mux (eq v_7900 (expression.bv_nat 1 1)) v_7903 v_7904);
      pure ()
    pat_end

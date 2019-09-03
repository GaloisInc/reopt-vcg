def cmovcw1 : instruction :=
  definst "cmovcw" $ do
    pattern fun (v_2538 : reg (bv 16)) (v_2539 : reg (bv 16)) => do
      v_4221 <- getRegister cf;
      v_4223 <- getRegister v_2538;
      v_4224 <- getRegister v_2539;
      setRegister (lhs.of_reg v_2539) (mux (eq v_4221 (expression.bv_nat 1 1)) v_4223 v_4224);
      pure ()
    pat_end;
    pattern fun (v_2532 : Mem) (v_2534 : reg (bv 16)) => do
      v_7901 <- getRegister cf;
      v_7903 <- evaluateAddress v_2532;
      v_7904 <- load v_7903 2;
      v_7905 <- getRegister v_2534;
      setRegister (lhs.of_reg v_2534) (mux (eq v_7901 (expression.bv_nat 1 1)) v_7904 v_7905);
      pure ()
    pat_end

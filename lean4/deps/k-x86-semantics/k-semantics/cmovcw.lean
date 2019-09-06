def cmovcw1 : instruction :=
  definst "cmovcw" $ do
    pattern fun (v_2614 : reg (bv 16)) (v_2615 : reg (bv 16)) => do
      v_4280 <- getRegister cf;
      v_4281 <- getRegister v_2614;
      v_4282 <- getRegister v_2615;
      setRegister (lhs.of_reg v_2615) (mux v_4280 v_4281 v_4282);
      pure ()
    pat_end;
    pattern fun (v_2610 : Mem) (v_2611 : reg (bv 16)) => do
      v_7748 <- getRegister cf;
      v_7749 <- evaluateAddress v_2610;
      v_7750 <- load v_7749 2;
      v_7751 <- getRegister v_2611;
      setRegister (lhs.of_reg v_2611) (mux v_7748 v_7750 v_7751);
      pure ()
    pat_end

def shrxl1 : instruction :=
  definst "shrxl" $ do
    pattern fun (v_3068 : reg (bv 32)) (v_3069 : reg (bv 32)) (v_3070 : reg (bv 32)) => do
      v_5933 <- getRegister v_3069;
      v_5934 <- getRegister v_3068;
      setRegister (lhs.of_reg v_3070) (lshr v_5933 (bv_and v_5934 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (v_3058 : reg (bv 32)) (v_3057 : Mem) (v_3059 : reg (bv 32)) => do
      v_9077 <- evaluateAddress v_3057;
      v_9078 <- load v_9077 4;
      v_9079 <- getRegister v_3058;
      setRegister (lhs.of_reg v_3059) (lshr v_9078 (bv_and v_9079 (expression.bv_nat 32 31)));
      pure ()
    pat_end

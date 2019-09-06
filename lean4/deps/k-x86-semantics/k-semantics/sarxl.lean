def sarxl1 : instruction :=
  definst "sarxl" $ do
    pattern fun (v_3236 : reg (bv 32)) (v_3237 : reg (bv 32)) (v_3238 : reg (bv 32)) => do
      v_6378 <- getRegister v_3237;
      v_6379 <- getRegister v_3236;
      setRegister (lhs.of_reg v_3238) (ashr v_6378 (bv_and v_6379 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (v_3227 : reg (bv 32)) (v_3224 : Mem) (v_3228 : reg (bv 32)) => do
      v_10672 <- evaluateAddress v_3224;
      v_10673 <- load v_10672 4;
      v_10674 <- getRegister v_3227;
      setRegister (lhs.of_reg v_3228) (ashr v_10673 (bv_and v_10674 (expression.bv_nat 32 31)));
      pure ()
    pat_end

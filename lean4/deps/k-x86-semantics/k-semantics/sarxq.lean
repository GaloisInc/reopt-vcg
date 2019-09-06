def sarxq1 : instruction :=
  definst "sarxq" $ do
    pattern fun (v_3255 : reg (bv 64)) (v_3256 : reg (bv 64)) (v_3257 : reg (bv 64)) => do
      v_6393 <- getRegister v_3256;
      v_6394 <- getRegister v_3255;
      setRegister (lhs.of_reg v_3257) (ashr v_6393 (bv_and v_6394 (expression.bv_nat 64 63)));
      pure ()
    pat_end;
    pattern fun (v_3245 : reg (bv 64)) (v_3247 : Mem) (v_3246 : reg (bv 64)) => do
      v_10679 <- evaluateAddress v_3247;
      v_10680 <- load v_10679 8;
      v_10681 <- getRegister v_3245;
      setRegister (lhs.of_reg v_3246) (ashr v_10680 (bv_and v_10681 (expression.bv_nat 64 63)));
      pure ()
    pat_end

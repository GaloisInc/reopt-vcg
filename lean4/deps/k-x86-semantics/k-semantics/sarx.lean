def sarx1 : instruction :=
  definst "sarx" $ do
    pattern fun (v_3231 : reg (bv 32)) (v_3232 : reg (bv 32)) (v_3233 : reg (bv 32)) => do
      v_7841 <- getRegister v_3232;
      v_7842 <- getRegister v_3231;
      setRegister (lhs.of_reg v_3233) (ashr v_7841 (bv_and v_7842 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (v_3250 : reg (bv 64)) (v_3251 : reg (bv 64)) (v_3252 : reg (bv 64)) => do
      v_7857 <- getRegister v_3251;
      v_7858 <- getRegister v_3250;
      setRegister (lhs.of_reg v_3252) (ashr v_7857 (bv_and v_7858 (expression.bv_nat 64 63)));
      pure ()
    pat_end;
    pattern fun (v_3221 : reg (bv 32)) (v_3223 : Mem) (v_3222 : reg (bv 32)) => do
      v_12769 <- evaluateAddress v_3223;
      v_12770 <- load v_12769 4;
      v_12771 <- getRegister v_3221;
      setRegister (lhs.of_reg v_3222) (ashr v_12770 (bv_and v_12771 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (v_3240 : reg (bv 64)) (v_3244 : Mem) (v_3241 : reg (bv 64)) => do
      v_12775 <- evaluateAddress v_3244;
      v_12776 <- load v_12775 8;
      v_12777 <- getRegister v_3240;
      setRegister (lhs.of_reg v_3241) (ashr v_12776 (bv_and v_12777 (expression.bv_nat 64 63)));
      pure ()
    pat_end

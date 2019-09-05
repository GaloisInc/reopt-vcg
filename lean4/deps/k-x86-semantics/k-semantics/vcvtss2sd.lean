def vcvtss2sd1 : instruction :=
  definst "vcvtss2sd" $ do
    pattern fun (v_3314 : reg (bv 128)) (v_3315 : reg (bv 128)) (v_3316 : reg (bv 128)) => do
      v_6216 <- getRegister v_3315;
      v_6218 <- getRegister v_3314;
      setRegister (lhs.of_reg v_3316) (concat (extract v_6216 0 64) (Float2MInt (roundFloat (MInt2Float (extract v_6218 96 128) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3308 : Mem) (v_3309 : reg (bv 128)) (v_3310 : reg (bv 128)) => do
      v_10242 <- getRegister v_3309;
      v_10244 <- evaluateAddress v_3308;
      v_10245 <- load v_10244 4;
      setRegister (lhs.of_reg v_3310) (concat (extract v_10242 0 64) (Float2MInt (roundFloat (MInt2Float v_10245 24 8) 53 11) 64));
      pure ()
    pat_end

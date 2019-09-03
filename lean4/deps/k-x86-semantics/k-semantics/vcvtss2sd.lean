def vcvtss2sd1 : instruction :=
  definst "vcvtss2sd" $ do
    pattern fun (v_3250 : reg (bv 128)) (v_3251 : reg (bv 128)) (v_3252 : reg (bv 128)) => do
      v_6294 <- getRegister v_3251;
      v_6296 <- getRegister v_3250;
      setRegister (lhs.of_reg v_3252) (concat (extract v_6294 0 64) (Float2MInt (roundFloat (MInt2Float (extract v_6296 96 128) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3242 : Mem) (v_3245 : reg (bv 128)) (v_3246 : reg (bv 128)) => do
      v_10480 <- getRegister v_3245;
      v_10482 <- evaluateAddress v_3242;
      v_10483 <- load v_10482 4;
      setRegister (lhs.of_reg v_3246) (concat (extract v_10480 0 64) (Float2MInt (roundFloat (MInt2Float v_10483 24 8) 53 11) 64));
      pure ()
    pat_end

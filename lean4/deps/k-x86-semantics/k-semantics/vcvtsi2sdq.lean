def vcvtsi2sdq1 : instruction :=
  definst "vcvtsi2sdq" $ do
    pattern fun (v_3290 : reg (bv 64)) (v_3294 : reg (bv 128)) (v_3295 : reg (bv 128)) => do
      v_6198 <- getRegister v_3294;
      v_6200 <- getRegister v_3290;
      setRegister (lhs.of_reg v_3295) (concat (extract v_6198 0 64) (Float2MInt (Int2Float (svalueMInt v_6200) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3280 : Mem) (v_3283 : reg (bv 128)) (v_3284 : reg (bv 128)) => do
      v_10241 <- getRegister v_3283;
      v_10243 <- evaluateAddress v_3280;
      v_10244 <- load v_10243 8;
      setRegister (lhs.of_reg v_3284) (concat (extract v_10241 0 64) (Float2MInt (Int2Float (svalueMInt v_10244) 53 11) 64));
      pure ()
    pat_end

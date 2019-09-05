def vcvtsi2sdq1 : instruction :=
  definst "vcvtsi2sdq" $ do
    pattern fun (v_3268 : reg (bv 64)) (v_3266 : reg (bv 128)) (v_3267 : reg (bv 128)) => do
      v_6171 <- getRegister v_3266;
      v_6173 <- getRegister v_3268;
      setRegister (lhs.of_reg v_3267) (concat (extract v_6171 0 64) (Float2MInt (Int2Float (svalueMInt v_6173) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3255 : Mem) (v_3256 : reg (bv 128)) (v_3257 : reg (bv 128)) => do
      v_10214 <- getRegister v_3256;
      v_10216 <- evaluateAddress v_3255;
      v_10217 <- load v_10216 8;
      setRegister (lhs.of_reg v_3257) (concat (extract v_10214 0 64) (Float2MInt (Int2Float (svalueMInt v_10217) 53 11) 64));
      pure ()
    pat_end

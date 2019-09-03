def vcvtsi2sdq1 : instruction :=
  definst "vcvtsi2sdq" $ do
    pattern fun (v_3200 : reg (bv 64)) (v_3203 : reg (bv 128)) (v_3204 : reg (bv 128)) => do
      v_6249 <- getRegister v_3203;
      v_6251 <- getRegister v_3200;
      setRegister (lhs.of_reg v_3204) (concat (extract v_6249 0 64) (Float2MInt (Int2Float (svalueMInt v_6251) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3189 : Mem) (v_3192 : reg (bv 128)) (v_3193 : reg (bv 128)) => do
      v_10452 <- getRegister v_3192;
      v_10454 <- evaluateAddress v_3189;
      v_10455 <- load v_10454 8;
      setRegister (lhs.of_reg v_3193) (concat (extract v_10452 0 64) (Float2MInt (Int2Float (svalueMInt v_10455) 53 11) 64));
      pure ()
    pat_end

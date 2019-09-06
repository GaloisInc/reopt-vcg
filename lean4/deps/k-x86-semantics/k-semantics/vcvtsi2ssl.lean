def vcvtsi2ssl1 : instruction :=
  definst "vcvtsi2ssl" $ do
    pattern fun (v_3314 : reg (bv 32)) (v_3315 : reg (bv 128)) (v_3316 : reg (bv 128)) => do
      v_6216 <- getRegister v_3315;
      v_6218 <- getRegister v_3314;
      setRegister (lhs.of_reg v_3316) (concat (extract v_6216 0 96) (Float2MInt (Int2Float (svalueMInt v_6218) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_3301 : Mem) (v_3304 : reg (bv 128)) (v_3305 : reg (bv 128)) => do
      v_10251 <- getRegister v_3304;
      v_10253 <- evaluateAddress v_3301;
      v_10254 <- load v_10253 4;
      setRegister (lhs.of_reg v_3305) (concat (extract v_10251 0 96) (Float2MInt (Int2Float (svalueMInt v_10254) 24 8) 32));
      pure ()
    pat_end

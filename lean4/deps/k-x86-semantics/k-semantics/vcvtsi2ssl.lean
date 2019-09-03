def vcvtsi2ssl1 : instruction :=
  definst "vcvtsi2ssl" $ do
    pattern fun (v_3233 : reg (bv 32)) (v_3237 : reg (bv 128)) (v_3238 : reg (bv 128)) => do
      v_6948 <- getRegister v_3237;
      v_6950 <- getRegister v_3233;
      setRegister (lhs.of_reg v_3238) (concat (extract v_6948 0 96) (Float2MInt (Int2Float (svalueMInt v_6950) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_3223 : Mem) (v_3226 : reg (bv 128)) (v_3227 : reg (bv 128)) => do
      v_12190 <- getRegister v_3226;
      v_12192 <- evaluateAddress v_3223;
      v_12193 <- load v_12192 4;
      setRegister (lhs.of_reg v_3227) (concat (extract v_12190 0 96) (Float2MInt (Int2Float (svalueMInt v_12193) 24 8) 32));
      pure ()
    pat_end

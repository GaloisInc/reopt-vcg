def vcvtsi2ss1 : instruction :=
  definst "vcvtsi2ss" $ do
    pattern fun (v_3218 : Mem) (v_3221 : reg (bv 128)) (v_3222 : reg (bv 128)) => do
      v_13268 <- getRegister v_3221;
      v_13270 <- evaluateAddress v_3218;
      v_13271 <- load v_13270 4;
      setRegister (lhs.of_reg v_3222) (concat (extract v_13268 0 96) (Float2MInt (Int2Float (svalueMInt v_13271) 24 8) 32));
      pure ()
    pat_end

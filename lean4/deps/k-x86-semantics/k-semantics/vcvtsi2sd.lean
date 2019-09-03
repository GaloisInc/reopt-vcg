def vcvtsi2sd1 : instruction :=
  definst "vcvtsi2sd" $ do
    pattern fun (v_3181 : Mem) (v_3184 : reg (bv 128)) (v_3185 : reg (bv 128)) => do
      v_13259 <- getRegister v_3184;
      v_13261 <- evaluateAddress v_3181;
      v_13262 <- load v_13261 4;
      setRegister (lhs.of_reg v_3185) (concat (extract v_13259 0 64) (Float2MInt (Int2Float (svalueMInt v_13262) 53 11) 64));
      pure ()
    pat_end

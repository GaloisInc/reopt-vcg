def vcvtsi2sd1 : instruction :=
  definst "vcvtsi2sd" $ do
    pattern fun (v_3168 : Mem) (v_3171 : reg (bv 128)) (v_3172 : reg (bv 128)) => do
      v_11045 <- getRegister v_3171;
      v_11047 <- evaluateAddress v_3168;
      v_11048 <- load v_11047 4;
      setRegister (lhs.of_reg v_3172) (concat (extract v_11045 0 64) (Float2MInt (Int2Float (svalueMInt v_11048) 53 11) 64));
      pure ()
    pat_end

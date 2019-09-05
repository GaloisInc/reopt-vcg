def vcvtsi2sd1 : instruction :=
  definst "vcvtsi2sd" $ do
    pattern fun (v_3236 : Mem) (v_3234 : reg (bv 128)) (v_3235 : reg (bv 128)) => do
      v_10787 <- getRegister v_3234;
      v_10789 <- evaluateAddress v_3236;
      v_10790 <- load v_10789 4;
      setRegister (lhs.of_reg v_3235) (concat (extract v_10787 0 64) (Float2MInt (Int2Float (svalueMInt v_10790) 53 11) 64));
      pure ()
    pat_end

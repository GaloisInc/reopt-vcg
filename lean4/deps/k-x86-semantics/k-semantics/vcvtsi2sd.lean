def vcvtsi2sd1 : instruction :=
  definst "vcvtsi2sd" $ do
    pattern fun (v_3259 : Mem) (v_3262 : reg (bv 128)) (v_3263 : reg (bv 128)) => do
      v_10814 <- getRegister v_3262;
      v_10816 <- evaluateAddress v_3259;
      v_10817 <- load v_10816 4;
      setRegister (lhs.of_reg v_3263) (concat (extract v_10814 0 64) (Float2MInt (Int2Float (svalueMInt v_10817) 53 11) 64));
      pure ()
    pat_end

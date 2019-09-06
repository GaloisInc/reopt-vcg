def vcvtsi2ss1 : instruction :=
  definst "vcvtsi2ss" $ do
    pattern fun (v_3296 : Mem) (v_3299 : reg (bv 128)) (v_3300 : reg (bv 128)) => do
      v_10823 <- getRegister v_3299;
      v_10825 <- evaluateAddress v_3296;
      v_10826 <- load v_10825 4;
      setRegister (lhs.of_reg v_3300) (concat (extract v_10823 0 96) (Float2MInt (Int2Float (svalueMInt v_10826) 24 8) 32));
      pure ()
    pat_end

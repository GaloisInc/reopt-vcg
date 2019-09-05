def vcvtsi2ss1 : instruction :=
  definst "vcvtsi2ss" $ do
    pattern fun (v_3273 : Mem) (v_3271 : reg (bv 128)) (v_3272 : reg (bv 128)) => do
      v_10796 <- getRegister v_3271;
      v_10798 <- evaluateAddress v_3273;
      v_10799 <- load v_10798 4;
      setRegister (lhs.of_reg v_3272) (concat (extract v_10796 0 96) (Float2MInt (Int2Float (svalueMInt v_10799) 24 8) 32));
      pure ()
    pat_end

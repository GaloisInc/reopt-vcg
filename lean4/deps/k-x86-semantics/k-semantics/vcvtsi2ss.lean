def vcvtsi2ss1 : instruction :=
  definst "vcvtsi2ss" $ do
    pattern fun (v_3205 : Mem) (v_3208 : reg (bv 128)) (v_3209 : reg (bv 128)) => do
      v_11054 <- getRegister v_3208;
      v_11056 <- evaluateAddress v_3205;
      v_11057 <- load v_11056 4;
      setRegister (lhs.of_reg v_3209) (concat (extract v_11054 0 96) (Float2MInt (Int2Float (svalueMInt v_11057) 24 8) 32));
      pure ()
    pat_end

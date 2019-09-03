def vcvtdq2pd1 : instruction :=
  definst "vcvtdq2pd" $ do
    pattern fun (v_3002 : reg (bv 128)) (v_3003 : reg (bv 128)) => do
      v_5790 <- getRegister v_3002;
      setRegister (lhs.of_reg v_3003) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5790 64 96)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_5790 96 128)) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3009 : reg (bv 256)) (v_3010 : reg (bv 256)) => do
      v_5805 <- getRegister v_3009;
      setRegister (lhs.of_reg v_3010) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5805 128 160)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5805 160 192)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_5805 192 224)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_5805 224 256)) 53 11) 64))));
      pure ()
    pat_end;
    pattern fun (v_2995 : Mem) (v_2998 : reg (bv 128)) => do
      v_10094 <- evaluateAddress v_2995;
      v_10095 <- load v_10094 8;
      setRegister (lhs.of_reg v_2998) (concat (Float2MInt (Int2Float (svalueMInt (extract v_10095 0 32)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_10095 32 64)) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3004 : Mem) (v_3005 : reg (bv 256)) => do
      v_10106 <- evaluateAddress v_3004;
      v_10107 <- load v_10106 16;
      setRegister (lhs.of_reg v_3005) (concat (Float2MInt (Int2Float (svalueMInt (extract v_10107 0 32)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_10107 32 64)) 53 11) 64) (concat (Float2MInt (Int2Float (svalueMInt (extract v_10107 64 96)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_10107 96 128)) 53 11) 64))));
      pure ()
    pat_end

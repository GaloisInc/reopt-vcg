def vcvtsi2ssq1 : instruction :=
  definst "vcvtsi2ssq" $ do
    pattern fun (v_3327 : reg (bv 64)) (v_3331 : reg (bv 128)) (v_3332 : reg (bv 128)) => do
      v_6230 <- getRegister v_3331;
      v_6232 <- getRegister v_3327;
      setRegister (lhs.of_reg v_3332) (concat (extract v_6230 0 96) (Float2MInt (Int2Float (svalueMInt v_6232) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_3317 : Mem) (v_3320 : reg (bv 128)) (v_3321 : reg (bv 128)) => do
      v_10260 <- getRegister v_3320;
      v_10262 <- evaluateAddress v_3317;
      v_10263 <- load v_10262 8;
      setRegister (lhs.of_reg v_3321) (concat (extract v_10260 0 96) (Float2MInt (Int2Float (svalueMInt v_10263) 24 8) 32));
      pure ()
    pat_end

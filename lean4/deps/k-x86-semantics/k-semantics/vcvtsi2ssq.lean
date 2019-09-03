def vcvtsi2ssq1 : instruction :=
  definst "vcvtsi2ssq" $ do
    pattern fun (v_3237 : reg (bv 64)) (v_3240 : reg (bv 128)) (v_3241 : reg (bv 128)) => do
      v_6281 <- getRegister v_3240;
      v_6283 <- getRegister v_3237;
      setRegister (lhs.of_reg v_3241) (concat (extract v_6281 0 96) (Float2MInt (Int2Float (svalueMInt v_6283) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_3226 : Mem) (v_3229 : reg (bv 128)) (v_3230 : reg (bv 128)) => do
      v_10471 <- getRegister v_3229;
      v_10473 <- evaluateAddress v_3226;
      v_10474 <- load v_10473 8;
      setRegister (lhs.of_reg v_3230) (concat (extract v_10471 0 96) (Float2MInt (Int2Float (svalueMInt v_10474) 24 8) 32));
      pure ()
    pat_end

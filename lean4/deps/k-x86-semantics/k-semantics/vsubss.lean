def vsubss1 : instruction :=
  definst "vsubss" $ do
    pattern fun (v_3135 : reg (bv 128)) (v_3136 : reg (bv 128)) (v_3137 : reg (bv 128)) => do
      v_7272 <- getRegister v_3136;
      v_7276 <- getRegister v_3135;
      setRegister (lhs.of_reg v_3137) (concat (extract v_7272 0 96) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7272 96 128) 24 8) (MInt2Float (extract v_7276 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3129 : Mem) (v_3130 : reg (bv 128)) (v_3131 : reg (bv 128)) => do
      v_13177 <- getRegister v_3130;
      v_13181 <- evaluateAddress v_3129;
      v_13182 <- load v_13181 4;
      setRegister (lhs.of_reg v_3131) (concat (extract v_13177 0 96) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13177 96 128) 24 8) (MInt2Float v_13182 24 8)) 32));
      pure ()
    pat_end

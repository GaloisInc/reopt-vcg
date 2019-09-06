def vcvtsd2ss1 : instruction :=
  definst "vcvtsd2ss" $ do
    pattern fun (v_3256 : reg (bv 128)) (v_3257 : reg (bv 128)) (v_3258 : reg (bv 128)) => do
      v_6165 <- getRegister v_3257;
      v_6167 <- getRegister v_3256;
      setRegister (lhs.of_reg v_3258) (concat (extract v_6165 0 96) (Float2MInt (roundFloat (MInt2Float (extract v_6167 64 128) 53 11) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_3248 : Mem) (v_3251 : reg (bv 128)) (v_3252 : reg (bv 128)) => do
      v_10222 <- getRegister v_3251;
      v_10224 <- evaluateAddress v_3248;
      v_10225 <- load v_10224 8;
      setRegister (lhs.of_reg v_3252) (concat (extract v_10222 0 96) (Float2MInt (roundFloat (MInt2Float v_10225 53 11) 24 8) 32));
      pure ()
    pat_end

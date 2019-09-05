def vcvtsd2ss1 : instruction :=
  definst "vcvtsd2ss" $ do
    pattern fun (v_3229 : reg (bv 128)) (v_3230 : reg (bv 128)) (v_3231 : reg (bv 128)) => do
      v_6138 <- getRegister v_3230;
      v_6140 <- getRegister v_3229;
      setRegister (lhs.of_reg v_3231) (concat (extract v_6138 0 96) (Float2MInt (roundFloat (MInt2Float (extract v_6140 64 128) 53 11) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_3223 : Mem) (v_3224 : reg (bv 128)) (v_3225 : reg (bv 128)) => do
      v_10195 <- getRegister v_3224;
      v_10197 <- evaluateAddress v_3223;
      v_10198 <- load v_10197 8;
      setRegister (lhs.of_reg v_3225) (concat (extract v_10195 0 96) (Float2MInt (roundFloat (MInt2Float v_10198 53 11) 24 8) 32));
      pure ()
    pat_end

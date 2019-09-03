def vcvtsd2ss1 : instruction :=
  definst "vcvtsd2ss" $ do
    pattern fun (v_3165 : reg (bv 128)) (v_3166 : reg (bv 128)) (v_3167 : reg (bv 128)) => do
      v_6216 <- getRegister v_3166;
      v_6218 <- getRegister v_3165;
      setRegister (lhs.of_reg v_3167) (concat (extract v_6216 0 96) (Float2MInt (roundFloat (MInt2Float (extract v_6218 64 128) 53 11) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_3157 : Mem) (v_3160 : reg (bv 128)) (v_3161 : reg (bv 128)) => do
      v_10433 <- getRegister v_3160;
      v_10435 <- evaluateAddress v_3157;
      v_10436 <- load v_10435 8;
      setRegister (lhs.of_reg v_3161) (concat (extract v_10433 0 96) (Float2MInt (roundFloat (MInt2Float v_10436 53 11) 24 8) 32));
      pure ()
    pat_end

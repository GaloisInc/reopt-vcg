def vpor1 : instruction :=
  definst "vpor" $ do
    pattern fun (v_3021 : Mem) (v_3022 : reg (bv 128)) (v_3023 : reg (bv 128)) => do
      v_13261 <- getRegister v_3022;
      v_13262 <- evaluateAddress v_3021;
      v_13263 <- load v_13262 16;
      setRegister (lhs.of_reg v_3023) (bv_or v_13261 v_13263);
      pure ()
    pat_end;
    pattern fun (v_3032 : Mem) (v_3033 : reg (bv 256)) (v_3034 : reg (bv 256)) => do
      v_13266 <- getRegister v_3033;
      v_13267 <- evaluateAddress v_3032;
      v_13268 <- load v_13267 32;
      setRegister (lhs.of_reg v_3034) (bv_or v_13266 v_13268);
      pure ()
    pat_end

def movaps1 : instruction :=
  definst "movaps" $ do
    pattern fun (v_3231 : reg (bv 128)) (v_3232 : reg (bv 128)) => do
      v_5743 <- getRegister v_3231;
      setRegister (lhs.of_reg v_3232) v_5743;
      pure ()
    pat_end;
    pattern fun (v_3224 : reg (bv 128)) (v_3223 : Mem) => do
      v_7513 <- evaluateAddress v_3223;
      v_7514 <- getRegister v_3224;
      store v_7513 v_7514 16;
      pure ()
    pat_end;
    pattern fun (v_3227 : Mem) (v_3228 : reg (bv 128)) => do
      v_8959 <- evaluateAddress v_3227;
      v_8960 <- load v_8959 16;
      setRegister (lhs.of_reg v_3228) v_8960;
      pure ()
    pat_end

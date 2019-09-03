def movaps1 : instruction :=
  definst "movaps" $ do
    pattern fun (v_3153 : reg (bv 128)) (v_3154 : reg (bv 128)) => do
      v_6192 <- getRegister v_3153;
      setRegister (lhs.of_reg v_3154) v_6192;
      pure ()
    pat_end;
    pattern fun (v_3145 : reg (bv 128)) (v_3143 : Mem) => do
      v_7962 <- evaluateAddress v_3143;
      v_7963 <- getRegister v_3145;
      store v_7962 v_7963 16;
      pure ()
    pat_end;
    pattern fun (v_3147 : Mem) (v_3149 : reg (bv 128)) => do
      v_9899 <- evaluateAddress v_3147;
      v_9900 <- load v_9899 16;
      setRegister (lhs.of_reg v_3149) v_9900;
      pure ()
    pat_end

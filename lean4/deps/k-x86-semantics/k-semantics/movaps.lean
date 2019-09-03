def movaps1 : instruction :=
  definst "movaps" $ do
    pattern fun (v_3140 : reg (bv 128)) (v_3141 : reg (bv 128)) => do
      v_5895 <- getRegister v_3140;
      setRegister (lhs.of_reg v_3141) v_5895;
      pure ()
    pat_end;
    pattern fun (v_3133 : reg (bv 128)) (v_3132 : Mem) => do
      v_7665 <- evaluateAddress v_3132;
      v_7666 <- getRegister v_3133;
      store v_7665 v_7666 16;
      pure ()
    pat_end;
    pattern fun (v_3136 : Mem) (v_3137 : reg (bv 128)) => do
      v_9309 <- evaluateAddress v_3136;
      v_9310 <- load v_9309 16;
      setRegister (lhs.of_reg v_3137) v_9310;
      pure ()
    pat_end

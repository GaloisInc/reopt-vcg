def pxor1 : instruction :=
  definst "pxor" $ do
    pattern fun (v_3244 : reg (bv 128)) (v_3245 : reg (bv 128)) => do
      v_9223 <- getRegister v_3245;
      v_9224 <- getRegister v_3244;
      setRegister (lhs.of_reg v_3245) (bv_xor v_9223 v_9224);
      pure ()
    pat_end;
    pattern fun (v_3239 : Mem) (v_3240 : reg (bv 128)) => do
      v_16081 <- getRegister v_3240;
      v_16082 <- evaluateAddress v_3239;
      v_16083 <- load v_16082 16;
      setRegister (lhs.of_reg v_3240) (bv_xor v_16081 v_16083);
      pure ()
    pat_end

def pxor1 : instruction :=
  definst "pxor" $ do
    pattern fun (v_3335 : reg (bv 128)) (v_3336 : reg (bv 128)) => do
      v_8864 <- getRegister v_3336;
      v_8865 <- getRegister v_3335;
      setRegister (lhs.of_reg v_3336) (bv_xor v_8864 v_8865);
      pure ()
    pat_end;
    pattern fun (v_3331 : Mem) (v_3332 : reg (bv 128)) => do
      v_15235 <- getRegister v_3332;
      v_15236 <- evaluateAddress v_3331;
      v_15237 <- load v_15236 16;
      setRegister (lhs.of_reg v_3332) (bv_xor v_15235 v_15237);
      pure ()
    pat_end

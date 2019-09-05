def xorps1 : instruction :=
  definst "xorps" $ do
    pattern fun (v_3426 : reg (bv 128)) (v_3427 : reg (bv 128)) => do
      v_8035 <- getRegister v_3427;
      v_8036 <- getRegister v_3426;
      setRegister (lhs.of_reg v_3427) (bv_xor v_8035 v_8036);
      pure ()
    pat_end;
    pattern fun (v_3421 : Mem) (v_3422 : reg (bv 128)) => do
      v_13567 <- getRegister v_3422;
      v_13568 <- evaluateAddress v_3421;
      v_13569 <- load v_13568 16;
      setRegister (lhs.of_reg v_3422) (bv_xor v_13567 v_13569);
      pure ()
    pat_end

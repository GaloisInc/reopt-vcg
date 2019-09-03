def xorps1 : instruction :=
  definst "xorps" $ do
    pattern fun (v_2804 : reg (bv 128)) (v_2805 : reg (bv 128)) => do
      v_5046 <- getRegister v_2805;
      v_5047 <- getRegister v_2804;
      setRegister (lhs.of_reg v_2805) (bv_xor v_5046 v_5047);
      pure ()
    pat_end;
    pattern fun (v_2800 : Mem) (v_2801 : reg (bv 128)) => do
      v_7251 <- getRegister v_2801;
      v_7252 <- evaluateAddress v_2800;
      v_7253 <- load v_7252 16;
      setRegister (lhs.of_reg v_2801) (bv_xor v_7251 v_7253);
      pure ()
    pat_end

def xorps1 : instruction :=
  definst "xorps" $ do
    pattern fun (v_3453 : reg (bv 128)) (v_3454 : reg (bv 128)) => do
      v_8062 <- getRegister v_3454;
      v_8063 <- getRegister v_3453;
      setRegister (lhs.of_reg v_3454) (bv_xor v_8062 v_8063);
      pure ()
    pat_end;
    pattern fun (v_3448 : Mem) (v_3449 : reg (bv 128)) => do
      v_13594 <- getRegister v_3449;
      v_13595 <- evaluateAddress v_3448;
      v_13596 <- load v_13595 16;
      setRegister (lhs.of_reg v_3449) (bv_xor v_13594 v_13596);
      pure ()
    pat_end

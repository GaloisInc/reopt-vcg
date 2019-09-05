def notw1 : instruction :=
  definst "notw" $ do
    pattern fun (v_2953 : reg (bv 16)) => do
      v_4542 <- getRegister v_2953;
      setRegister (lhs.of_reg v_2953) (bv_xor v_4542 (expression.bv_nat 16 65535));
      pure ()
    pat_end;
    pattern fun (v_2949 : Mem) => do
      v_10797 <- evaluateAddress v_2949;
      v_10798 <- load v_10797 2;
      store v_10797 (bv_xor v_10798 (expression.bv_nat 16 65535)) 2;
      pure ()
    pat_end

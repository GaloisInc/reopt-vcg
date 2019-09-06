def notl1 : instruction :=
  definst "notl" $ do
    pattern fun (v_2964 : reg (bv 32)) => do
      v_4557 <- getRegister v_2964;
      setRegister (lhs.of_reg v_2964) (bv_xor v_4557 (expression.bv_nat 32 4294967295));
      pure ()
    pat_end;
    pattern fun (v_2961 : Mem) => do
      v_10816 <- evaluateAddress v_2961;
      v_10817 <- load v_10816 4;
      store v_10816 (bv_xor v_10817 (expression.bv_nat 32 4294967295)) 4;
      pure ()
    pat_end

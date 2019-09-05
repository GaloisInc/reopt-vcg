def cmovnaw1 : instruction :=
  definst "cmovnaw" $ do
    pattern fun (v_2825 : reg (bv 16)) (v_2826 : reg (bv 16)) => do
      v_4581 <- getRegister cf;
      v_4583 <- getRegister zf;
      v_4586 <- getRegister v_2825;
      v_4587 <- getRegister v_2826;
      setRegister (lhs.of_reg v_2826) (mux (bit_or (eq v_4581 (expression.bv_nat 1 1)) (eq v_4583 (expression.bv_nat 1 1))) v_4586 v_4587);
      pure ()
    pat_end;
    pattern fun (v_2820 : Mem) (v_2821 : reg (bv 16)) => do
      v_8136 <- getRegister cf;
      v_8138 <- getRegister zf;
      v_8141 <- evaluateAddress v_2820;
      v_8142 <- load v_8141 2;
      v_8143 <- getRegister v_2821;
      setRegister (lhs.of_reg v_2821) (mux (bit_or (eq v_8136 (expression.bv_nat 1 1)) (eq v_8138 (expression.bv_nat 1 1))) v_8142 v_8143);
      pure ()
    pat_end

def cmovnaq : instruction :=
  definst "cmovnaq" $ do
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister cf;
      v_3 <- getRegister zf;
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 8;
      v_6 <- getRegister (lhs.of_reg r64_1);
      setRegister (lhs.of_reg r64_1) (mux (bit_or v_2 v_3) v_5 v_6);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister cf;
      v_3 <- getRegister zf;
      v_4 <- getRegister (lhs.of_reg r64_0);
      v_5 <- getRegister (lhs.of_reg r64_1);
      setRegister (lhs.of_reg r64_1) (mux (bit_or v_2 v_3) v_4 v_5);
      pure ()
    pat_end

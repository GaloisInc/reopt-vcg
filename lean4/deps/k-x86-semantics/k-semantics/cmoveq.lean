def cmoveq : instruction :=
  definst "cmoveq" $ do
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister zf;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 8;
      v_5 <- getRegister (lhs.of_reg r64_1);
      setRegister (lhs.of_reg r64_1) (mux v_2 v_4 v_5);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister zf;
      v_3 <- getRegister (lhs.of_reg r64_0);
      v_4 <- getRegister (lhs.of_reg r64_1);
      setRegister (lhs.of_reg r64_1) (mux v_2 v_3 v_4);
      pure ()
    pat_end
def movb : instruction :=
  definst "movb" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      store v_2 (handleImmediateWithSignExtend imm_0 8 8) 1;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (rh_1 : reg (bv 8)) => do
      setRegister (lhs.of_reg rh_1) (handleImmediateWithSignExtend imm_0 8 8);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (rh_1 : reg (bv 8)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 1;
      setRegister (lhs.of_reg rh_1) v_3;
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister (lhs.of_reg rh_0);
      store v_2 v_3 1;
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) (rh_1 : reg (bv 8)) => do
      v_2 <- getRegister (lhs.of_reg rh_0);
      setRegister (lhs.of_reg rh_1) v_2;
      pure ()
    pat_end

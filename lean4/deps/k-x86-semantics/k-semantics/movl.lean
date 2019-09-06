def movl1 : instruction :=
  definst "movl" $ do
    pattern fun (v_2567 : imm int) (v_2568 : reg (bv 32)) => do
      setRegister (lhs.of_reg v_2568) (handleImmediateWithSignExtend v_2567 32 32);
      pure ()
    pat_end;
    pattern fun (v_2576 : reg (bv 32)) (v_2577 : reg (bv 32)) => do
      v_3997 <- getRegister v_2576;
      setRegister (lhs.of_reg v_2577) v_3997;
      pure ()
    pat_end;
    pattern fun (v_2560 : imm int) (v_2559 : Mem) => do
      v_8468 <- evaluateAddress v_2559;
      store v_8468 (handleImmediateWithSignExtend v_2560 32 32) 4;
      pure ()
    pat_end;
    pattern fun (v_2564 : reg (bv 32)) (v_2563 : Mem) => do
      v_8471 <- evaluateAddress v_2563;
      v_8472 <- getRegister v_2564;
      store v_8471 v_8472 4;
      pure ()
    pat_end;
    pattern fun (v_2572 : Mem) (v_2573 : reg (bv 32)) => do
      v_8731 <- evaluateAddress v_2572;
      v_8732 <- load v_8731 4;
      setRegister (lhs.of_reg v_2573) v_8732;
      pure ()
    pat_end

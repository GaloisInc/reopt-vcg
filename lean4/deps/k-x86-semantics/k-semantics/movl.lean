def movl1 : instruction :=
  definst "movl" $ do
    pattern fun (v_2479 : imm int) (v_2480 : reg (bv 32)) => do
      setRegister (lhs.of_reg v_2480) (handleImmediateWithSignExtend v_2479 32 32);
      pure ()
    pat_end;
    pattern fun (v_2488 : reg (bv 32)) (v_2489 : reg (bv 32)) => do
      v_3906 <- getRegister v_2488;
      setRegister (lhs.of_reg v_2489) v_3906;
      pure ()
    pat_end;
    pattern fun (v_2471 : imm int) (v_2470 : Mem) => do
      v_8597 <- evaluateAddress v_2470;
      store v_8597 (handleImmediateWithSignExtend v_2471 32 32) 4;
      pure ()
    pat_end;
    pattern fun (v_2475 : reg (bv 32)) (v_2474 : Mem) => do
      v_8600 <- evaluateAddress v_2474;
      v_8601 <- getRegister v_2475;
      store v_8600 v_8601 4;
      pure ()
    pat_end;
    pattern fun (v_2483 : Mem) (v_2484 : reg (bv 32)) => do
      v_8861 <- evaluateAddress v_2483;
      v_8862 <- load v_8861 4;
      setRegister (lhs.of_reg v_2484) v_8862;
      pure ()
    pat_end

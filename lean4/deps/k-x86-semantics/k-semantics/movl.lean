def movl1 : instruction :=
  definst "movl" $ do
    pattern fun (v_2541 : imm int) (v_2543 : reg (bv 32)) => do
      setRegister (lhs.of_reg v_2543) (handleImmediateWithSignExtend v_2541 32 32);
      pure ()
    pat_end;
    pattern fun (v_2551 : reg (bv 32)) (v_2552 : reg (bv 32)) => do
      v_3970 <- getRegister v_2551;
      setRegister (lhs.of_reg v_2552) v_3970;
      pure ()
    pat_end;
    pattern fun (v_2534 : imm int) (v_2533 : Mem) => do
      v_8441 <- evaluateAddress v_2533;
      store v_8441 (handleImmediateWithSignExtend v_2534 32 32) 4;
      pure ()
    pat_end;
    pattern fun (v_2538 : reg (bv 32)) (v_2537 : Mem) => do
      v_8444 <- evaluateAddress v_2537;
      v_8445 <- getRegister v_2538;
      store v_8444 v_8445 4;
      pure ()
    pat_end;
    pattern fun (v_2546 : Mem) (v_2547 : reg (bv 32)) => do
      v_8704 <- evaluateAddress v_2546;
      v_8705 <- load v_8704 4;
      setRegister (lhs.of_reg v_2547) v_8705;
      pure ()
    pat_end

def movl1 : instruction :=
  definst "movl" $ do
    pattern fun (v_2491 : imm int) (v_2492 : reg (bv 32)) => do
      setRegister (lhs.of_reg v_2492) (handleImmediateWithSignExtend v_2491 32 32);
      pure ()
    pat_end;
    pattern fun (v_2500 : reg (bv 32)) (v_2501 : reg (bv 32)) => do
      v_3919 <- getRegister v_2500;
      setRegister (lhs.of_reg v_2501) v_3919;
      pure ()
    pat_end;
    pattern fun (v_2484 : imm int) (v_2483 : Mem) => do
      v_8577 <- evaluateAddress v_2483;
      store v_8577 (handleImmediateWithSignExtend v_2484 32 32) 4;
      pure ()
    pat_end;
    pattern fun (v_2488 : reg (bv 32)) (v_2487 : Mem) => do
      v_8580 <- evaluateAddress v_2487;
      v_8581 <- getRegister v_2488;
      store v_8580 v_8581 4;
      pure ()
    pat_end;
    pattern fun (v_2496 : Mem) (v_2497 : reg (bv 32)) => do
      v_8840 <- evaluateAddress v_2496;
      v_8841 <- load v_8840 4;
      setRegister (lhs.of_reg v_2497) v_8841;
      pure ()
    pat_end

def movw1 : instruction :=
  definst "movw" $ do
    pattern fun (v_2699 : imm int) (v_2701 : reg (bv 16)) => do
      setRegister (lhs.of_reg v_2701) (handleImmediateWithSignExtend v_2699 16 16);
      pure ()
    pat_end;
    pattern fun (v_2709 : reg (bv 16)) (v_2710 : reg (bv 16)) => do
      v_4118 <- getRegister v_2709;
      setRegister (lhs.of_reg v_2710) v_4118;
      pure ()
    pat_end;
    pattern fun (v_2692 : imm int) (v_2691 : Mem) => do
      v_8495 <- evaluateAddress v_2691;
      store v_8495 (handleImmediateWithSignExtend v_2692 16 16) 2;
      pure ()
    pat_end;
    pattern fun (v_2696 : reg (bv 16)) (v_2695 : Mem) => do
      v_8498 <- evaluateAddress v_2695;
      v_8499 <- getRegister v_2696;
      store v_8498 v_8499 2;
      pure ()
    pat_end;
    pattern fun (v_2704 : Mem) (v_2705 : reg (bv 16)) => do
      v_8735 <- evaluateAddress v_2704;
      v_8736 <- load v_8735 2;
      setRegister (lhs.of_reg v_2705) v_8736;
      pure ()
    pat_end

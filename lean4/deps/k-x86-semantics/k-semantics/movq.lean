def movq1 : instruction :=
  definst "movq" $ do
    pattern fun (v_2659 : imm int) (v_2658 : reg (bv 64)) => do
      setRegister (lhs.of_reg v_2658) (handleImmediateWithSignExtend v_2659 64 64);
      pure ()
    pat_end;
    pattern fun (v_2667 : reg (bv 64)) (v_2668 : reg (bv 64)) => do
      v_4095 <- getRegister v_2667;
      setRegister (lhs.of_reg v_2668) v_4095;
      pure ()
    pat_end;
    pattern fun (v_2673 : reg (bv 128)) (v_2672 : reg (bv 64)) => do
      v_4097 <- getRegister v_2673;
      setRegister (lhs.of_reg v_2672) (extract v_4097 64 128);
      pure ()
    pat_end;
    pattern fun (v_2681 : reg (bv 64)) (v_2682 : reg (bv 128)) => do
      v_4104 <- getRegister v_2681;
      setRegister (lhs.of_reg v_2682) (concat (expression.bv_nat 64 0) v_4104);
      pure ()
    pat_end;
    pattern fun (v_2686 : reg (bv 128)) (v_2687 : reg (bv 128)) => do
      v_4107 <- getRegister v_2686;
      setRegister (lhs.of_reg v_2687) (concat (expression.bv_nat 64 0) (extract v_4107 64 128));
      pure ()
    pat_end;
    pattern fun (v_2647 : imm int) (v_2646 : Mem) => do
      v_8501 <- evaluateAddress v_2646;
      store v_8501 (sext (handleImmediateWithSignExtend v_2647 32 32) 64) 8;
      pure ()
    pat_end;
    pattern fun (v_2651 : reg (bv 64)) (v_2650 : Mem) => do
      v_8505 <- evaluateAddress v_2650;
      v_8506 <- getRegister v_2651;
      store v_8505 v_8506 8;
      pure ()
    pat_end;
    pattern fun (v_2655 : reg (bv 128)) (v_2654 : Mem) => do
      v_8508 <- evaluateAddress v_2654;
      v_8509 <- getRegister v_2655;
      store v_8508 (extract v_8509 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2663 : Mem) (v_2664 : reg (bv 64)) => do
      v_8749 <- evaluateAddress v_2663;
      v_8750 <- load v_8749 8;
      setRegister (lhs.of_reg v_2664) v_8750;
      pure ()
    pat_end;
    pattern fun (v_2677 : Mem) (v_2678 : reg (bv 128)) => do
      v_8752 <- evaluateAddress v_2677;
      v_8753 <- load v_8752 8;
      setRegister (lhs.of_reg v_2678) (concat (expression.bv_nat 64 0) v_8753);
      pure ()
    pat_end
